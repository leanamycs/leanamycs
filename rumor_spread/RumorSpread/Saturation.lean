import RumorSpread.OneRound

/-!
# Saturation phase

Once the informed set has size `≥ n/2` (which persists by monotonicity), the
expected number of uninformed nodes contracts by a factor `2/3` per round
(`avg_uninformed_le`); iterating gives `saturation`.  Combined with Markov's
inequality — which here is just a pointwise bound pushed through
`expList_le_expList` — this finishes the proof in `Main.lean`.
-/

namespace RumorPush

open Finset

variable {n : ℕ}

/-- **Phase 2**: starting above half, the expected number of uninformed nodes
after `T` further rounds is at most `(2/3)^T · (n - |I|)`. -/
lemma saturation (hn : 2 ≤ n) (T : ℕ) :
    ∀ I : Finset (Fin n), n ≤ 2 * I.card →
      expList (Tgt n) T (fun l => (n : ℝ) - (run I l).card)
        ≤ ((2 : ℝ) / 3) ^ T * ((n : ℝ) - I.card) := by
  haveI := tgt_nonempty hn
  induction T with
  | zero =>
    intro I _
    simp
  | succ T ih =>
    intro I hI
    rw [expList_succ]
    calc avg (fun r : Tgt n =>
            expList (Tgt n) T fun l => (n : ℝ) - (run I (r :: l)).card)
        ≤ avg (fun r : Tgt n =>
            ((2 : ℝ) / 3) ^ T * ((n : ℝ) - (step I r).card)) := by
          apply avg_le_avg
          intro r
          exact ih (step I r)
            (le_trans hI (by have := card_le_card_step I r; omega))
      _ = ((2 : ℝ) / 3) ^ T
            * avg (fun r : Tgt n => (n : ℝ) - (step I r).card) :=
          avg_const_mul _ _
      _ ≤ ((2 : ℝ) / 3) ^ T * (2 / 3 * ((n : ℝ) - I.card)) :=
          mul_le_mul_of_nonneg_left (avg_uninformed_le hn I hI) (by positivity)
      _ = ((2 : ℝ) / 3) ^ (T + 1) * ((n : ℝ) - I.card) := by
          rw [pow_succ]
          ring

end RumorPush
