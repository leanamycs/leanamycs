import RumorSpread.OneRound

/-!
# Growth phase

While the informed set has size `≤ n/2`, each round multiplies it by `9/8`
with probability `≥ 1/8` (`prob_goodRound`).  The exponential-moment bound
`expList_half_pow_goodCount` — `𝔼[(1/2)^(good rounds)] ≤ (15/16)^T` — is the
only concentration tool of the development: one induction over rounds
replaces both the stochastic domination by a binomial and the Chernoff bound.

`phase1` concludes: if `(9/8)^L ≥ n`, the probability that the informed set
is still `≤ n/2` after `T₁` rounds is at most `2^L · (15/16)^T₁`.
-/

namespace RumorPush

open Finset

variable {n : ℕ}

/-- Per-round exponential moment of the good-round indicator. -/
lemma avg_half_pow_good (hn : 2 ≤ n) (I : Finset (Fin n)) (hI : I.Nonempty) :
    avg (fun r : Tgt n => ((1 : ℝ) / 2) ^ (if goodRound I r then 1 else 0))
      ≤ 15 / 16 := by
  haveI := tgt_nonempty hn
  have hpt : (fun r : Tgt n => ((1 : ℝ) / 2) ^ (if goodRound I r then 1 else 0))
      = fun r : Tgt n => (fun _ : Tgt n => (1 : ℝ)) r
          - (fun r : Tgt n =>
              (1 : ℝ) / 2 * (if goodRound I r then (1 : ℝ) else 0)) r := by
    funext r
    by_cases hg : goodRound I r
    · simp [hg]
      norm_num
    · simp [hg]
  rw [hpt, avg_sub, avg_const, avg_const_mul]
  have h := prob_goodRound hn I hI
  linarith

/-- **Exponential-moment bound for adaptive trials**:
`𝔼[(1/2) ^ (number of good rounds in T rounds)] ≤ (15/16) ^ T`. -/
lemma expList_half_pow_goodCount (hn : 2 ≤ n) (T : ℕ) :
    ∀ I : Finset (Fin n), I.Nonempty →
      expList (Tgt n) T (fun l => ((1 : ℝ) / 2) ^ goodCount I l)
        ≤ ((15 : ℝ) / 16) ^ T := by
  haveI := tgt_nonempty hn
  induction T with
  | zero =>
    intro I _
    simp
  | succ T ih =>
    intro I hI
    rw [expList_succ]
    have key : ∀ r : Tgt n,
        (expList (Tgt n) T fun l => ((1 : ℝ) / 2) ^ goodCount I (r :: l))
          = ((1 : ℝ) / 2) ^ (if goodRound I r then 1 else 0)
              * expList (Tgt n) T
                  fun l => ((1 : ℝ) / 2) ^ goodCount (step I r) l := by
      intro r
      rw [← expList_const_mul]
      congr 1
      funext l
      rw [goodCount_cons, pow_add]
    calc avg (fun r : Tgt n =>
            expList (Tgt n) T fun l => ((1 : ℝ) / 2) ^ goodCount I (r :: l))
        = avg (fun r : Tgt n =>
            ((1 : ℝ) / 2) ^ (if goodRound I r then 1 else 0)
              * expList (Tgt n) T
                  fun l => ((1 : ℝ) / 2) ^ goodCount (step I r) l) :=
          congrArg avg (funext key)
      _ ≤ avg (fun r : Tgt n =>
            ((1 : ℝ) / 2) ^ (if goodRound I r then 1 else 0)
              * ((15 : ℝ) / 16) ^ T) := by
          apply avg_le_avg
          intro r
          exact mul_le_mul_of_nonneg_left
            (ih (step I r) (hI.mono (subset_step I r))) (by positivity)
      _ = ((15 : ℝ) / 16) ^ T
            * avg (fun r : Tgt n =>
                ((1 : ℝ) / 2) ^ (if goodRound I r then 1 else 0)) := by
          rw [← avg_const_mul]
          exact congrArg avg (funext fun r => mul_comm _ _)
      _ ≤ ((15 : ℝ) / 16) ^ T * ((15 : ℝ) / 16) :=
          mul_le_mul_of_nonneg_left (avg_half_pow_good hn I hI) (by positivity)
      _ = ((15 : ℝ) / 16) ^ (T + 1) := (pow_succ _ _).symm

/-- **Phase 1**: if `(9/8)^L ≥ n`, then after `T₁` rounds the informed set is
still `≤ n/2` with probability at most `2^L · (15/16)^T₁`. -/
lemma phase1 (hn : 2 ≤ n) (v₀ : Fin n) (L T₁ : ℕ)
    (hL : (n : ℝ) ≤ ((9 : ℝ) / 8) ^ L) :
    expList (Tgt n) T₁
        (fun l => if 2 * (run {v₀} l).card ≤ n then (1 : ℝ) else 0)
      ≤ 2 ^ L * ((15 : ℝ) / 16) ^ T₁ := by
  haveI := tgt_nonempty hn
  have hpt : ∀ l : List (Tgt n),
      (if 2 * (run {v₀} l).card ≤ n then (1 : ℝ) else 0)
        ≤ 2 ^ L * ((1 : ℝ) / 2) ^ goodCount {v₀} l := by
    intro l
    by_cases h : 2 * (run {v₀} l).card ≤ n
    · rw [if_pos h]
      have hgrow := pow_goodCount_mul_card_le_card_run {v₀} l h
      rw [card_singleton] at hgrow
      have h1 : 1 ≤ (run {v₀} l).card :=
        card_pos.2 ((singleton_nonempty v₀).mono (subset_run _ l))
      have hltn : (run {v₀} l).card < n := by omega
      have hgL : ((9 : ℝ) / 8) ^ goodCount {v₀} l < ((9 : ℝ) / 8) ^ L := by
        calc ((9 : ℝ) / 8) ^ goodCount {v₀} l
            ≤ ((run {v₀} l).card : ℝ) := by simpa using hgrow
          _ < (n : ℝ) := by exact_mod_cast hltn
          _ ≤ ((9 : ℝ) / 8) ^ L := hL
      have hglt : goodCount {v₀} l < L := by
        by_contra hge
        push_neg at hge
        exact absurd
          (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 9 / 8) hge)
          (not_le.2 hgL)
      have h2g : (2 : ℝ) ^ goodCount {v₀} l ≤ 2 ^ L :=
        pow_le_pow_right₀ (by norm_num) hglt.le
      have hpos : (0 : ℝ) < 2 ^ goodCount {v₀} l := by positivity
      rw [div_pow, one_pow, mul_one_div, le_div_iff₀ hpos, one_mul]
      exact h2g
    · rw [if_neg h]
      positivity
  calc expList (Tgt n) T₁
        (fun l => if 2 * (run {v₀} l).card ≤ n then (1 : ℝ) else 0)
      ≤ expList (Tgt n) T₁
          (fun l => 2 ^ L * ((1 : ℝ) / 2) ^ goodCount {v₀} l) :=
        expList_le_expList hpt
    _ = 2 ^ L * expList (Tgt n) T₁
          (fun l => ((1 : ℝ) / 2) ^ goodCount {v₀} l) :=
        expList_const_mul _ _ _
    _ ≤ 2 ^ L * ((15 : ℝ) / 16) ^ T₁ :=
        mul_le_mul_of_nonneg_left
          (expList_half_pow_goodCount hn T₁ {v₀} (singleton_nonempty v₀))
          (by positivity)

end RumorPush
