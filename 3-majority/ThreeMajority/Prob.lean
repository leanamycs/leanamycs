import Mathlib

/-!
# A minimal finite uniform probability layer

Copied from the sister `rumor_spread` development (`RumorSpread/Prob.lean`),
since the two Lean projects are independent packages: `avg f` is the
expectation of `f` under the uniform distribution on a fintype, and
`expList α T F` is the expectation of a trajectory functional `F` over `T`
i.i.d.\ uniform draws, defined by recursion on `T`.

New in this file (not needed by the push protocol, since it only ever
averaged over a single uniform draw at a time): `avg_prod_pi`, the
discrete/measure-theory-free statement that the average of a *product* of
functions of *different* coordinates over a product-of-fintypes space
equals the product of the individual averages. This is the independence
fact that lets the 3-majority protocol's per-agent updates (one round,
`n` agents, each sampling independently) be combined into a single
concentration bound for the whole round.
-/

namespace ThreeMajority

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

/-! ### Independence: average of a product over a product space -/

/-- **Independence for a pair of coordinates**: the average of a product
`g p.1 * h p.2` over a product Fintype `β × δ` (uniform measure) equals the
product of the individual averages. No `Nonempty` hypothesis is needed:
if either factor is empty, both sides are `0` by the `0/0 = 0` convention. -/
lemma avg_mul_prod {β δ : Type*} [Fintype β] [Fintype δ] (g : β → ℝ) (h : δ → ℝ) :
    avg (fun p : β × δ => g p.1 * h p.2) = avg g * avg h := by
  unfold avg
  rw [Fintype.card_prod, Fintype.sum_prod_type]
  rw [show (∑ i : β, ∑ j : δ, g i * h j) = (∑ b, g b) * ∑ d, h d from by
    rw [Finset.sum_mul_sum univ univ g h]]
  push_cast
  ring

/-- **Marginal**: the average of a function of the first coordinate only,
over a product space, equals its average over the first factor alone. -/
lemma avg_fst_mul {β δ : Type*} [Fintype β] [Fintype δ] [Nonempty δ] (g : β → ℝ) :
    avg (fun p : β × δ => g p.1) = avg g := by
  rw [show (fun p : β × δ => g p.1) = fun p : β × δ => g p.1 * (fun _ : δ => (1 : ℝ)) p.2
      from funext fun p => (mul_one _).symm,
    avg_mul_prod g (fun _ : δ => (1 : ℝ)), avg_const, mul_one]

/-- **Marginal**: the average of a function of the second coordinate only,
over a product space, equals its average over the second factor alone. -/
lemma avg_snd_mul {β δ : Type*} [Fintype β] [Nonempty β] [Fintype δ] (h : δ → ℝ) :
    avg (fun p : β × δ => h p.2) = avg h := by
  rw [show (fun p : β × δ => h p.2) = fun p : β × δ => (fun _ : β => (1 : ℝ)) p.1 * h p.2
      from funext fun p => (one_mul _).symm,
    avg_mul_prod (fun _ : β => (1 : ℝ)) h, avg_const, one_mul]

/-- Reindexing `avg` along an `Equiv` between the underlying Fintypes. -/
lemma avg_equiv {β : Type*} [Fintype β] (e : α ≃ β) (F : β → ℝ) :
    avg (fun a => F (e a)) = avg F := by
  unfold avg
  rw [Equiv.sum_comp e F, Fintype.card_congr e]

/-- **Independence over a `Fin n`-indexed product**: the average of a product
`∏ i, f i (x i)` over the product Fintype `Fin n → γ` (uniform measure)
equals the product of the individual averages `avg (f i)`. This is the
discrete, measure-theory-free form of "coordinate projections on a product
space are independent." -/
lemma avg_prod_pi {γ : Type*} [Fintype γ] :
    ∀ (n : ℕ) (f : Fin n → γ → ℝ),
      avg (fun x : Fin n → γ => ∏ i, f i (x i)) = ∏ i, avg (f i)
  | 0, f => by
      have h1 : (fun x : Fin 0 → γ => ∏ i : Fin 0, f i (x i)) = fun _ => (1 : ℝ) := by
        funext x; simp
      have h2 : Nonempty (Fin 0 → γ) := ⟨Fin.elim0⟩
      rw [h1]
      haveI := h2
      rw [avg_const, Finset.prod_of_isEmpty]
  | n + 1, f => by
      have hfun : (fun x : Fin (n + 1) → γ => ∏ i, f i (x i))
          = (fun x : Fin (n + 1) → γ =>
              (fun p : γ × (Fin n → γ) => f 0 p.1 * ∏ i : Fin n, f i.succ (p.2 i))
                ((Fin.consEquiv (fun _ : Fin (n + 1) => γ)).symm x)) := by
        funext x
        simp only [Fin.prod_univ_succ]
        congr 1
      rw [hfun,
        avg_equiv (Fin.consEquiv (fun _ : Fin (n + 1) => γ)).symm
          (fun p : γ × (Fin n → γ) => f 0 p.1 * ∏ i : Fin n, f i.succ (p.2 i)),
        avg_mul_prod (f 0) (fun x : Fin n → γ => ∏ i : Fin n, f i.succ (x i)),
        avg_prod_pi n (fun i => f i.succ), Fin.prod_univ_succ]

/-- **Marginal for `Fin n`-indexed Pi types**: the average of a function of
a single fixed coordinate, over the whole product space, equals its average
over that one factor alone. -/
lemma avg_eval {γ : Type*} [Fintype γ] [Nonempty γ] (n : ℕ) (v : Fin n) (G : γ → ℝ) :
    avg (fun x : Fin n → γ => G (x v)) = avg G := by
  have hval : (fun x : Fin n → γ => G (x v))
      = fun x : Fin n → γ =>
          ∏ i : Fin n, (if i = v then G else (fun _ : γ => (1 : ℝ))) (x i) := by
    funext x
    rw [Finset.prod_eq_single v]
    · simp
    · intro i _ hiv
      simp [hiv]
    · intro h
      exact absurd (mem_univ v) h
  rw [hval, avg_prod_pi n (fun i => if i = v then G else (fun _ : γ => (1 : ℝ)))]
  rw [Finset.prod_eq_single v]
  · simp
  · intro i _ hiv
    simp [hiv, avg_const]
  · intro h
    exact absurd (mem_univ v) h

end ThreeMajority
