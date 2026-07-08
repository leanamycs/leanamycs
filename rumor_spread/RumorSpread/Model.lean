import Mathlib

/-!
# The uniform push protocol on the complete graph

* `Tgt n` — a round configuration: every node of `Fin n` picks a target
  different from itself (uniformly at random, in the probabilistic layer).
* `step I r` — one push round: the informed set `I` together with the targets
  of its members.
* `run I l` — the informed set after consuming the list `l` of rounds.
* `goodRound I r` — the round at least multiplies the informed set by `9/8`,
  or the informed set already exceeds `n/2`.
* `goodCount I l` — number of good rounds along a trajectory.

The deterministic heart of the growth phase is
`pow_goodCount_mul_card_le_card_run`: as long as the final informed set is
still at most `n/2`, the informed count is at least `(9/8) ^ (good rounds)`.
-/

namespace RumorPush

open Finset

/-- A round configuration: every node picks a target different from itself. -/
def Tgt (n : ℕ) := ∀ v : Fin n, {u : Fin n // u ≠ v}

instance (n : ℕ) : Fintype (Tgt n) :=
  inferInstanceAs (Fintype (∀ v : Fin n, {u : Fin n // u ≠ v}))

instance (n : ℕ) : DecidableEq (Tgt n) :=
  inferInstanceAs (DecidableEq (∀ v : Fin n, {u : Fin n // u ≠ v}))

lemma tgt_nonempty {n : ℕ} (hn : 2 ≤ n) : Nonempty (Tgt n) := by
  have : ∀ v : Fin n, Nonempty {u : Fin n // u ≠ v} := by
    intro v
    have h2 : 1 < Fintype.card (Fin n) := by simpa using hn
    exact (Fintype.exists_ne_of_one_lt_card h2 v).elim fun u hu => ⟨⟨u, hu⟩⟩
  exact inferInstanceAs (Nonempty (∀ v : Fin n, {u : Fin n // u ≠ v}))

variable {n : ℕ}

/-- One push round: every informed node pushes the rumor to its target. -/
def step (I : Finset (Fin n)) (r : Tgt n) : Finset (Fin n) :=
  I ∪ I.image fun v => ((r v) : Fin n)

lemma subset_step (I : Finset (Fin n)) (r : Tgt n) : I ⊆ step I r :=
  subset_union_left

lemma card_le_card_step (I : Finset (Fin n)) (r : Tgt n) :
    I.card ≤ (step I r).card :=
  card_le_card (subset_step I r)

lemma card_step_le (I : Finset (Fin n)) (r : Tgt n) :
    (step I r).card ≤ 2 * I.card :=
  calc (step I r).card ≤ I.card + (I.image fun v => ((r v) : Fin n)).card :=
        card_union_le _ _
    _ ≤ I.card + I.card := Nat.add_le_add_left card_image_le _
    _ = 2 * I.card := (two_mul _).symm

lemma mem_step {I : Finset (Fin n)} {r : Tgt n} {u : Fin n} :
    u ∈ step I r ↔ u ∈ I ∨ ∃ v ∈ I, ((r v) : Fin n) = u := by
  simp [step]

/-- The informed set after consuming a list of rounds. -/
def run (I : Finset (Fin n)) : List (Tgt n) → Finset (Fin n)
  | [] => I
  | r :: l => run (step I r) l

@[simp] lemma run_nil (I : Finset (Fin n)) : run I [] = I := rfl

@[simp] lemma run_cons (I : Finset (Fin n)) (r : Tgt n) (l : List (Tgt n)) :
    run I (r :: l) = run (step I r) l := rfl

lemma subset_run (I : Finset (Fin n)) (l : List (Tgt n)) : I ⊆ run I l := by
  induction l generalizing I with
  | nil => simp
  | cons r l ih => exact (subset_step I r).trans (ih (step I r))

lemma run_append (I : Finset (Fin n)) (l₁ l₂ : List (Tgt n)) :
    run I (l₁ ++ l₂) = run (run I l₁) l₂ := by
  induction l₁ generalizing I with
  | nil => simp
  | cons r l ih => simp [ih]

lemma card_run_le (I : Finset (Fin n)) (l : List (Tgt n)) :
    (run I l).card ≤ n := by
  simpa using card_le_card (subset_univ (run I l))

/-- A round is *good* if it grows the informed set by a factor `≥ 9/8`,
or if the informed set already exceeds `n/2`. -/
def goodRound (I : Finset (Fin n)) (r : Tgt n) : Prop :=
  9 * I.card ≤ 8 * (step I r).card ∨ n < 2 * I.card

instance (I : Finset (Fin n)) (r : Tgt n) : Decidable (goodRound I r) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- The number of good rounds along a trajectory. -/
def goodCount (I : Finset (Fin n)) : List (Tgt n) → ℕ
  | [] => 0
  | r :: l => (if goodRound I r then 1 else 0) + goodCount (step I r) l

@[simp] lemma goodCount_nil (I : Finset (Fin n)) : goodCount I [] = 0 := rfl

lemma goodCount_cons (I : Finset (Fin n)) (r : Tgt n) (l : List (Tgt n)) :
    goodCount I (r :: l)
      = (if goodRound I r then 1 else 0) + goodCount (step I r) l := rfl

/-- Deterministic growth: if the informed set never exceeded `n/2` (which by
monotonicity is implied by the *final* informed set being `≤ n/2`), each good
round multiplied its size by `9/8`. -/
lemma pow_goodCount_mul_card_le_card_run (I : Finset (Fin n))
    (l : List (Tgt n)) (h : 2 * (run I l).card ≤ n) :
    ((9 : ℝ) / 8) ^ goodCount I l * I.card ≤ ((run I l).card : ℝ) := by
  induction l generalizing I with
  | nil => simp
  | cons r l ih =>
    rw [run_cons] at h ⊢
    have hrun : (step I r).card ≤ (run (step I r) l).card :=
      card_le_card (subset_run (step I r) l)
    have hnotbig : ¬ n < 2 * I.card := by
      have h1 : I.card ≤ (step I r).card := card_le_card_step I r
      omega
    have IH := ih (step I r) h
    have hpow : (0 : ℝ) ≤ ((9 : ℝ) / 8) ^ goodCount (step I r) l := by
      positivity
    rw [goodCount_cons]
    by_cases hg : goodRound I r
    · have h98 : 9 * I.card ≤ 8 * (step I r).card := hg.resolve_right hnotbig
      have hcast : (9 : ℝ) / 8 * I.card ≤ ((step I r).card : ℝ) := by
        have : (9 : ℝ) * I.card ≤ 8 * (step I r).card := by exact_mod_cast h98
        linarith
      rw [if_pos hg]
      calc ((9 : ℝ) / 8) ^ (1 + goodCount (step I r) l) * I.card
          = ((9 : ℝ) / 8) ^ goodCount (step I r) l * ((9 / 8) * I.card) := by
            rw [pow_add, pow_one]; ring
        _ ≤ ((9 : ℝ) / 8) ^ goodCount (step I r) l * (step I r).card :=
            mul_le_mul_of_nonneg_left hcast hpow
        _ ≤ ((run (step I r) l).card : ℝ) := IH
    · have hcast : (I.card : ℝ) ≤ ((step I r).card : ℝ) := by
        exact_mod_cast card_le_card_step I r
      rw [if_neg hg, zero_add]
      calc ((9 : ℝ) / 8) ^ goodCount (step I r) l * I.card
          ≤ ((9 : ℝ) / 8) ^ goodCount (step I r) l * (step I r).card :=
            mul_le_mul_of_nonneg_left hcast hpow
        _ ≤ ((run (step I r) l).card : ℝ) := IH

end RumorPush
