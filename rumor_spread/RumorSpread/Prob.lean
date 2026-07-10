import Mathlib

/-!
# A minimal finite uniform probability layer

All randomness in the rumor-spreading proof is uniform over finite types, so
instead of measure theory or `PMF` we use plain finite sums:

* `avg f` is the expectation of `f` under the uniform distribution on a
  fintype — a sum divided by a cardinality;
* `expList α T F` is the expectation of the trajectory functional `F` over a
  list of `T` i.i.d. uniform draws from `α`, defined by recursion on `T`
  (the transition-operator form of the expectation, which makes
  "conditioning on the first round" a definitional unfolding).

Markov's inequality and union bounds are not separate lemmas: they all reduce
to pointwise inequalities pushed through `avg_le_avg` / `expList_le_expList`.
-/

namespace RumorPush

open Finset

variable {α : Type*} [Fintype α]

/-- Expectation under the uniform distribution on a fintype. -/
noncomputable def avg (f : α → ℝ) : ℝ := (∑ a, f a) / (Fintype.card α : ℝ)

lemma avg_nonneg {f : α → ℝ} (hf : ∀ a, 0 ≤ f a) : 0 ≤ avg f :=
  div_nonneg (sum_nonneg fun a _ => hf a) (by positivity)

lemma avg_le_avg {f g : α → ℝ} (h : ∀ a, f a ≤ g a) : avg f ≤ avg g :=
  div_le_div_of_nonneg_right (sum_le_sum fun a _ => h a) (by positivity)

lemma avg_add (f g : α → ℝ) : avg (fun a => f a + g a) = avg f + avg g := by
  unfold avg
  rw [sum_add_distrib, add_div]

lemma avg_sub (f g : α → ℝ) : avg (fun a => f a - g a) = avg f - avg g := by
  unfold avg
  rw [sum_sub_distrib, sub_div]

lemma avg_const_mul (c : ℝ) (f : α → ℝ) :
    avg (fun a => c * f a) = c * avg f := by
  unfold avg
  rw [← mul_sum, mul_div_assoc]

lemma avg_sum {ι : Type*} (s : Finset ι) (f : ι → α → ℝ) :
    avg (fun a => ∑ i ∈ s, f i a) = ∑ i ∈ s, avg (f i) := by
  unfold avg
  rw [sum_comm, sum_div]

/-- The expectation of an indicator is a counting ratio. -/
lemma avg_indicator (P : α → Prop) [DecidablePred P] :
    avg (fun a => if P a then (1 : ℝ) else 0)
      = ((univ.filter P).card : ℝ) / (Fintype.card α : ℝ) := by
  unfold avg
  congr 1
  rw [sum_boole]

lemma card_cast_pos [Nonempty α] : (0 : ℝ) < (Fintype.card α : ℝ) := by
  exact_mod_cast Fintype.card_pos

lemma avg_const [Nonempty α] (c : ℝ) : avg (fun _ : α => c) = c := by
  unfold avg
  rw [sum_const, card_univ, nsmul_eq_mul, mul_comm, mul_div_assoc,
    div_self (ne_of_gt (card_cast_pos (α := α))), mul_one]

/-- Expectation of a functional of `T` i.i.d. uniform draws from `α`,
in transition-operator form: the head draw is averaged out first. -/
noncomputable def expList (α : Type*) [Fintype α] : ℕ → (List α → ℝ) → ℝ
  | 0, F => F []
  | T + 1, F => avg fun a : α => expList α T fun l => F (a :: l)

@[simp] lemma expList_zero (F : List α → ℝ) : expList α 0 F = F [] := rfl

lemma expList_succ (T : ℕ) (F : List α → ℝ) :
    expList α (T + 1) F = avg fun a : α => expList α T fun l => F (a :: l) :=
  rfl

lemma expList_nonneg {T : ℕ} {F : List α → ℝ} (h : ∀ l, 0 ≤ F l) :
    0 ≤ expList α T F := by
  induction T generalizing F with
  | zero => exact h []
  | succ T ih => exact avg_nonneg fun a => ih fun l => h (a :: l)

lemma expList_le_expList {T : ℕ} {F G : List α → ℝ} (h : ∀ l, F l ≤ G l) :
    expList α T F ≤ expList α T G := by
  induction T generalizing F G with
  | zero => exact h []
  | succ T ih => exact avg_le_avg fun a => ih fun l => h (a :: l)

lemma expList_add (T : ℕ) (F G : List α → ℝ) :
    expList α T (fun l => F l + G l) = expList α T F + expList α T G := by
  induction T generalizing F G with
  | zero => rfl
  | succ T ih =>
    rw [expList_succ, expList_succ (F := F), expList_succ (F := G), ← avg_add]
    exact congrArg avg (funext fun a => ih _ _)

lemma expList_const_mul (T : ℕ) (c : ℝ) (F : List α → ℝ) :
    expList α T (fun l => c * F l) = c * expList α T F := by
  induction T generalizing F with
  | zero => rfl
  | succ T ih =>
    rw [expList_succ, expList_succ (F := F), ← avg_const_mul]
    exact congrArg avg (funext fun a => ih _)

lemma expList_const [Nonempty α] (T : ℕ) (c : ℝ) :
    expList α T (fun _ => c) = c := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [expList_succ]
    simpa [ih] using avg_const (α := α) c

lemma expList_append (T₁ T₂ : ℕ) (F : List α → ℝ) :
    expList α (T₁ + T₂) F
      = expList α T₁ fun l₁ => expList α T₂ fun l₂ => F (l₁ ++ l₂) := by
  induction T₁ generalizing F with
  | zero => simp
  | succ T₁ ih =>
    rw [Nat.succ_add, expList_succ, expList_succ
      (F := fun l₁ => expList α T₂ fun l₂ => F (l₁ ++ l₂))]
    exact congrArg avg (funext fun a => by rw [ih]; simp)

end RumorPush
