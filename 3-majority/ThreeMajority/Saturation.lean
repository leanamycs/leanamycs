import ThreeMajority.OneRound
import ThreeMajority.Chernoff
import ThreeMajority.Growth

/-!
# Saturation phase

Once the dissent count `U_t = n - X_t` drops to `≤ n/4` (guaranteed whp by
`growth_phase1`), the majority map contracts it by a factor `≤ 5/8` per
round in expectation (`Corollary saturation`). Getting `U_t` all the way to
*exactly* `0` needs three distinct stages, because a single Chernoff bound
using a *fixed relative margin* has an absolute floor around `Θ(log n)`
(Mathlib's Hoeffding-style bound is mean-scaled, not range-scaled, but a
*fixed ratio* Chernoff argument still needs the mean itself to be
`Ω(log n)` for a polynomially-small per-round failure probability):

* **Stage 2a** (`saturation_stage2a`): geometric descent, contraction factor
  `0.7` (vs. the true `5/8`), from `n/4` down to a floor of
  `500 log n`, over `⌈6 log n⌉` rounds, each with failure `≤ n⁻²`.
* **Stage 2b** (`saturation_stage2b`): *one* round, jumping directly from
  the `Θ(log n)` floor to the *fixed* constant `10` (not scaled to the
  current mean) — since the mean is already tiny, this one round has
  astronomically small failure probability.
* **Stage 2c** (`saturation_stage2c`): the last round, from `U ≤ 10` to
  *exactly* `U = 0`, via ordinary Markov (`E[U] = O(1/n)`, no concentration
  needed at all for the very last step).
-/

namespace ThreeMajority

open Finset

variable {n : ℕ}

/-- **General per-round upper-tail bound**: given a reference dissent bound
`U_t ≤ M` (`M ≤ n/4`) and any target `k ≥ (5/8)M` (an upper bound on the
true one-round mean), the probability of the next dissent count exceeding
`k` decays according to the closed-form Chernoff exponent. -/
lemma saturation_round_closed (hn : 1 ≤ n) (I : Finset (Fin n)) {M k : ℝ}
    (hM0 : 0 < M) (hM1 : M ≤ (n : ℝ) / 4) (hkM : (5 / 8 : ℝ) * M ≤ k)
    (hUI : (n : ℝ) - (I.card : ℝ) ≤ M) :
    avg (fun r : Tgt3 n => if k ≤ (n : ℝ) - ((step I r).card : ℝ) then (1 : ℝ) else 0)
      ≤ Real.exp (k - (5 / 8) * M - k * Real.log (k / ((5 / 8) * M))) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  set x : ℝ := avg (ind I) with hx
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hxeq : x = (I.card : ℝ) / n := avg_ind_eq I
  have hcardle : (I.card : ℝ) ≤ n := by exact_mod_cast I.card_le_univ.trans_eq (by simp)
  have hx0 : (0 : ℝ) ≤ x := by rw [hxeq]; positivity
  have hx1 : (3 : ℝ) / 4 ≤ x := by rw [hxeq]; rw [le_div_iff₀ hn0]; nlinarith
  have hxle1 : x ≤ 1 := by rw [hxeq, div_le_one hn0]; exact hcardle
  set μub : ℝ := (5 / 8) * M with hμub
  have hμub0 : 0 < μub := by rw [hμub]; linarith
  have hnx : (n : ℝ) * (1 - x) ≤ M := by rw [hxeq]; field_simp; nlinarith
  have hμ : ∑ v : Fin n, avg (Y_dis I v) ≤ μub := by
    rw [sum_avg_Y_dis hn I, ← hx]
    have hquad : (1 - x) * (1 + 2 * x) ≤ 5 / 8 := by
      nlinarith [mul_nonneg (show (0:ℝ) ≤ x - 3/4 by linarith) (show (0:ℝ) ≤ x + 1/4 by linarith)]
    have hidentity : (n : ℝ) - (n:ℝ) * (3 * x ^ 2 - 2 * x ^ 3)
        = (n:ℝ) * (1 - x) * ((1 - x) * (1 + 2 * x)) := by ring
    rw [hidentity]
    have h1x : (0 : ℝ) ≤ (n:ℝ) * (1 - x) := by
      apply mul_nonneg hn0.le; linarith
    calc (n:ℝ) * (1 - x) * ((1 - x) * (1 + 2 * x))
        ≤ (n:ℝ) * (1 - x) * (5 / 8) := mul_le_mul_of_nonneg_left hquad h1x
      _ = (5 / 8) * ((n:ℝ) * (1 - x)) := by ring
      _ ≤ (5 / 8) * M := by nlinarith [hnx]
      _ = μub := hμub.symm
  have hbound := avg_tail_ge_log_le (Y_dis I) (Y_dis_zero_one I) hμ hμub0 hkM
  rw [show (fun x : Fin n → Fin n × Fin n × Fin n =>
        if k ≤ ∑ i, Y_dis I i (x i) then (1 : ℝ) else 0)
      = fun r : Tgt3 n => if k ≤ (n : ℝ) - ((step I r).card : ℝ) then (1 : ℝ) else 0
      from funext fun r => by rw [card_dissent_eq_sum]] at hbound
  exact hbound

/-- **Generic per-round upper-tail bound**, parametrized directly by an
upper bound `μub` on the true mean (rather than deriving it from `M` via
the linear `5/8` estimate, as `saturation_round_closed` does). Used by
stage 2b, where `M` is small and the *quadratic* estimate `g(M) ≤ 3M²/n`
is the tight one — the linear `5/8·M` bound is technically still valid but
far too crude to be useful there. -/
lemma saturation_round_generic (hn : 1 ≤ n) (I : Finset (Fin n)) {μub k : ℝ}
    (hμub0 : 0 < μub) (hkμ : μub ≤ k)
    (hμ : ∑ v : Fin n, avg (Y_dis I v) ≤ μub) :
    avg (fun r : Tgt3 n => if k ≤ (n : ℝ) - ((step I r).card : ℝ) then (1 : ℝ) else 0)
      ≤ Real.exp (k - μub - k * Real.log (k / μub)) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hbound := avg_tail_ge_log_le (Y_dis I) (Y_dis_zero_one I) hμ hμub0 hkμ
  rw [show (fun x : Fin n → Fin n × Fin n × Fin n =>
        if k ≤ ∑ i, Y_dis I i (x i) then (1 : ℝ) else 0)
      = fun r : Tgt3 n => if k ≤ (n : ℝ) - ((step I r).card : ℝ) then (1 : ℝ) else 0
      from funext fun r => by rw [card_dissent_eq_sum]] at hbound
  exact hbound

/-- **Quadratic mean bound**: for any dissent bound `U_t ≤ M` (`M ≤ n`),
the true one-round mean is at most `3M²/n` — the crude, but here tight,
bound `1-p(x) ≤ 3(1-x)²` (dropping the `5/8`-type refinement). -/
lemma saturation_mean_quad (hn1 : 1 ≤ n) (I : Finset (Fin n)) {M : ℝ}
    (hM0 : 0 ≤ M) (hUI : (n : ℝ) - (I.card : ℝ) ≤ M) :
    ∑ v : Fin n, avg (Y_dis I v) ≤ 3 * M ^ 2 / n := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn1⟩⟩
  set x : ℝ := avg (ind I) with hx
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hxeq : x = (I.card : ℝ) / n := avg_ind_eq I
  have hcardle : (I.card : ℝ) ≤ n := by exact_mod_cast I.card_le_univ.trans_eq (by simp)
  have hxle1 : x ≤ 1 := by rw [hxeq, div_le_one hn0]; exact hcardle
  have hnx : (n : ℝ) * (1 - x) ≤ M := by rw [hxeq]; field_simp; nlinarith
  have h1x : (0 : ℝ) ≤ 1 - x := by linarith
  rw [sum_avg_Y_dis hn1 I, ← hx]
  have hidentity : (n : ℝ) - (n : ℝ) * (3 * x ^ 2 - 2 * x ^ 3)
      = (n:ℝ) * (1 - x) * ((1 - x) * (1 + 2 * x)) := by ring
  rw [hidentity]
  have h3 : (1 - x) * (1 + 2 * x) ≤ 3 * (1 - x) := by nlinarith
  calc (n:ℝ) * (1 - x) * ((1 - x) * (1 + 2 * x))
      ≤ (n:ℝ) * (1 - x) * (3 * (1 - x)) := mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = 3 * ((n:ℝ) * (1 - x)) ^ 2 / n := by field_simp
    _ ≤ 3 * M ^ 2 / n := by
        gcongr

/-- **Numeric per-round upper-tail bound**: the closed-form Chernoff
exponent of `saturation_round_closed`, simplified via the quadratic-tight
Padé bound `Real.le_log_one_add_of_nonneg` to `-λ²/(k+μub)`,
`λ = k - (5/8)M`. This is the *only* place the upward direction needs a
quadratic-tight log bound (the downward direction used `log_ge_quadratic`
from `Bounds.lean`; here Mathlib's ready-made Padé bound suffices). -/
lemma saturation_round_numeric (hn : 1 ≤ n) (I : Finset (Fin n)) {M k : ℝ}
    (hM0 : 0 < M) (hM1 : M ≤ (n : ℝ) / 4) (hkM : (5 / 8 : ℝ) * M ≤ k) (hk0 : 0 < k)
    (hUI : (n : ℝ) - (I.card : ℝ) ≤ M) :
    avg (fun r : Tgt3 n => if k ≤ (n : ℝ) - ((step I r).card : ℝ) then (1 : ℝ) else 0)
      ≤ Real.exp (-(k - (5 / 8) * M) ^ 2 / (k + (5 / 8) * M)) := by
  have hclosed := saturation_round_closed hn I hM0 hM1 hkM hUI
  refine hclosed.trans (Real.exp_le_exp.mpr ?_)
  set μub : ℝ := (5 / 8) * M with hμubdef
  have hμub0 : 0 < μub := by rw [hμubdef]; linarith
  set lam : ℝ := k - μub with hlamdef
  have hρm1 : k / μub - 1 = lam / μub := by
    rw [hlamdef, div_sub_one (ne_of_gt hμub0)]
  have hpade : 2 * (k / μub - 1) / (k / μub + 1) ≤ Real.log (k / μub) := by
    have hx0 : (0 : ℝ) ≤ k / μub - 1 := by rw [hρm1]; positivity
    have h := Real.le_log_one_add_of_nonneg hx0
    rw [show (1 : ℝ) + (k / μub - 1) = k / μub from by ring,
      show k / μub - 1 + 2 = k / μub + 1 from by ring] at h
    exact h
  have hlogk : k * (2 * (k / μub - 1) / (k / μub + 1)) ≤ k * Real.log (k / μub) :=
    mul_le_mul_of_nonneg_left hpade hk0.le
  have hstep : k - μub - k * (2 * (k / μub - 1) / (k / μub + 1)) = -lam ^ 2 / (k + μub) := by
    rw [hlamdef, hρm1]
    have hkμub_pos : (0:ℝ) < k + μub := by linarith
    field_simp
    ring
  have hfinal : k - μub - k * Real.log (k / μub)
      ≤ k - μub - k * (2 * (k / μub - 1) / (k / μub + 1)) := by linarith [hlogk]
  rw [hstep] at hfinal
  exact hfinal

/-- **Stage 2a per-round bound**: guaranteed contraction factor `0.7`
(vs. the true `5/8`), with failure probability `≤ exp(-M/250)`. -/
lemma saturation_round_contract (hn : 1 ≤ n) (I : Finset (Fin n)) {M : ℝ}
    (hM0 : 0 < M) (hM1 : M ≤ (n : ℝ) / 4) (hUI : (n : ℝ) - (I.card : ℝ) ≤ M) :
    avg (fun r : Tgt3 n =>
        if (7 / 10 : ℝ) * M ≤ (n : ℝ) - ((step I r).card : ℝ) then (1 : ℝ) else 0)
      ≤ Real.exp (-(1 / 250 : ℝ) * M) := by
  have hk0 : (0 : ℝ) < (7 / 10) * M := by linarith
  have hkM : (5 / 8 : ℝ) * M ≤ (7 / 10) * M := by nlinarith
  have h := saturation_round_numeric hn I hM0 hM1 hkM hk0 hUI
  refine h.trans (Real.exp_le_exp.mpr ?_)
  rw [show (7 / 10 : ℝ) * M - 5 / 8 * M = (3 / 40) * M from by ring,
    show (7 / 10 : ℝ) * M + 5 / 8 * M = (53 / 40) * M from by ring, neg_div]
  have hgoal : (1 / 250 : ℝ) * M ≤ (3 / 40 * M) ^ 2 / (53 / 40 * M) := by
    rw [le_div_iff₀ (by linarith : (0:ℝ) < 53 / 40 * M)]
    nlinarith [sq_nonneg M, hM0]
  linarith [hgoal]

/-- The deterministic dissent-count target after `i` stage-2a rounds,
starting from bound `M`, clamped below at the floor `500 log n`. Written
in closed form (not recursively) so that `satAfter n M (i+1)` and
`satAfter n (0.7*M) i`-style shifts agree definitionally on the
unclamped branch, and only need `max`-monotonicity on the clamped one. -/
noncomputable def satAfter (n : ℕ) (M : ℝ) (i : ℕ) : ℝ :=
  max (500 * Real.log n) ((7 / 10 : ℝ) ^ i * M)

lemma satAfter_ge_floor (n : ℕ) (M : ℝ) (i : ℕ) :
    500 * Real.log n ≤ satAfter n M i := le_max_left _ _

lemma satAfter_zero (n : ℕ) (M : ℝ) (hM : 500 * Real.log n ≤ M) : satAfter n M 0 = M := by
  unfold satAfter; simp [max_eq_right hM]

lemma satAfter_le_of_le {n : ℕ} {M : ℝ} (hM0 : 0 ≤ M) (hM1 : M ≤ (n : ℝ) / 4)
    (hfloor4 : 500 * Real.log n ≤ (n : ℝ) / 4) (i : ℕ) : satAfter n M i ≤ (n : ℝ) / 4 := by
  unfold satAfter
  refine max_le hfloor4 ?_
  calc (7 / 10 : ℝ) ^ i * M ≤ 1 * M := by
        apply mul_le_mul_of_nonneg_right _ hM0
        exact pow_le_one₀ (by norm_num) (by norm_num)
    _ = M := one_mul M
    _ ≤ (n : ℝ) / 4 := hM1

lemma satAfter_contract_le (hn1 : 1 ≤ n) (M : ℝ) (i : ℕ) :
    (7 / 10 : ℝ) * satAfter n M i ≤ satAfter n M (i + 1) := by
  have hlog0 : (0:ℝ) ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn1)
  unfold satAfter
  rw [pow_succ]
  rcases le_total (500 * Real.log n) ((7 / 10 : ℝ) ^ i * M) with h | h
  · rw [max_eq_right h]
    apply le_max_of_le_right
    nlinarith
  · rw [max_eq_left h]
    apply le_max_of_le_left
    nlinarith

/-- **Stage 2a, union bound over `j` rounds**: starting from a dissent
bound `M` (`500 log n ≤ M ≤ n/4`), offset `i` rounds in, the probability
that the dissent count exceeds `satAfter n M (i+j)` after `j` further
rounds is at most `j · n⁻²` (`n⁻² = exp(-2 log n)`). Mirrors
`growth_fail_le`'s `expList`-conditioning idiom exactly, with the tail
direction flipped (dissent *shrinking*, not opinion-`1` count *growing*). -/
lemma saturation_fail_le (hn2 : 2 ≤ n) {M : ℝ} (hM0 : 500 * Real.log n ≤ M)
    (hM1 : M ≤ (n : ℝ) / 4) (hfloor4 : 500 * Real.log n ≤ (n : ℝ) / 4) (j : ℕ) :
    ∀ (i : ℕ) (I : Finset (Fin n)), (n : ℝ) - I.card ≤ satAfter n M i →
      expList (Tgt3 n) j
          (fun l => if satAfter n M (i + j) < (n : ℝ) - (run I l).card then (1 : ℝ) else 0)
        ≤ j * Real.exp (-2 * Real.log n) := by
  have hn1 : 1 ≤ n := by omega
  have hlogpos : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn2)
  haveI := tgt3_nonempty hn1
  induction j with
  | zero =>
    intro i I hUI
    simp only [Nat.add_zero, expList_zero, run_nil]
    rw [if_neg (by linarith)]
    norm_num
  | succ j ih =>
    intro i I hUI
    rw [expList_succ]
    have hMi_pos : 0 < satAfter n M i := lt_of_lt_of_le (by linarith) (satAfter_ge_floor n M i)
    have hMi_le : satAfter n M i ≤ (n : ℝ) / 4 := satAfter_le_of_le (by linarith) hM1 hfloor4 i
    have hsat := saturation_round_contract hn1 I hMi_pos hMi_le hUI
    have hkey : ∀ r : Tgt3 n,
        expList (Tgt3 n) j
            (fun l => if satAfter n M (i + (j + 1)) < (n : ℝ) - (run I (r :: l)).card
                then (1 : ℝ) else 0)
          ≤ (if (7 / 10 : ℝ) * satAfter n M i ≤ (n : ℝ) - ((step I r).card : ℝ)
              then (1 : ℝ) else 0) + j * Real.exp (-2 * Real.log n) := by
      intro r
      simp only [run_cons]
      by_cases hcase : (7 / 10 : ℝ) * satAfter n M i ≤ (n : ℝ) - ((step I r).card : ℝ)
      · rw [if_pos hcase]
        have hbound1 : expList (Tgt3 n) j
            (fun l => if satAfter n M (i + (j + 1)) < (n : ℝ) - (run (step I r) l).card
                then (1 : ℝ) else 0) ≤ 1 := by
          calc expList (Tgt3 n) j
                (fun l => if satAfter n M (i + (j + 1)) < (n : ℝ) - (run (step I r) l).card
                    then (1 : ℝ) else 0)
              ≤ expList (Tgt3 n) j (fun _ => (1 : ℝ)) :=
                expList_le_expList fun l => by split <;> norm_num
            _ = 1 := expList_const j 1
        have hpos : (0:ℝ) ≤ j * Real.exp (-2 * Real.log n) := by positivity
        exact le_trans hbound1 (by linarith)
      · rw [if_neg hcase]
        push_neg at hcase
        have hle : (n : ℝ) - ((step I r).card : ℝ) ≤ satAfter n M (i + 1) :=
          le_trans hcase.le (satAfter_contract_le hn1 M i)
        have hthis := ih (i + 1) (step I r) hle
        have hidx : i + 1 + j = i + (j + 1) := by omega
        rw [hidx] at hthis
        rw [zero_add]
        exact hthis
    calc avg (fun r : Tgt3 n => expList (Tgt3 n) j
          (fun l => if satAfter n M (i + (j + 1)) < (n : ℝ) - (run I (r :: l)).card
              then (1 : ℝ) else 0))
        ≤ avg (fun r : Tgt3 n =>
            (if (7 / 10 : ℝ) * satAfter n M i ≤ (n : ℝ) - ((step I r).card : ℝ)
                then (1 : ℝ) else 0) + j * Real.exp (-2 * Real.log n)) :=
          avg_le_avg hkey
      _ = avg (fun r : Tgt3 n => if (7 / 10 : ℝ) * satAfter n M i
              ≤ (n : ℝ) - ((step I r).card : ℝ) then (1 : ℝ) else 0)
            + j * Real.exp (-2 * Real.log n) := by
          rw [avg_add, avg_const]
      _ ≤ Real.exp (-(1 / 250 : ℝ) * satAfter n M i) + j * Real.exp (-2 * Real.log n) := by
          linarith [hsat]
      _ ≤ Real.exp (-2 * Real.log n) + j * Real.exp (-2 * Real.log n) := by
          have hle2 : Real.exp (-(1 / 250 : ℝ) * satAfter n M i) ≤ Real.exp (-2 * Real.log n) := by
            apply Real.exp_le_exp.mpr
            have := satAfter_ge_floor n M i
            nlinarith
          linarith [hle2]
      _ = (↑(j + 1) : ℝ) * Real.exp (-2 * Real.log n) := by push_cast; ring

/-- The number of stage-2a rounds. -/
noncomputable def T2a (n : ℕ) : ℕ := ⌈6 * Real.log n⌉₊

lemma satAfter_quarter_le_floor (hn2 : 2 ≤ n) :
    satAfter n ((n : ℝ) / 4) (T2a n) ≤ 500 * Real.log n := by
  have hlogpos : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn2)
  unfold satAfter
  apply max_le (le_refl _)
  have hT2a : (6 : ℝ) * Real.log n ≤ T2a n := Nat.le_ceil _
  have hlog710 : Real.log (7 / 10 : ℝ) ≤ -(3 / 10) := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 7/10 by norm_num); linarith
  have hlog710neg : Real.log (7 / 10 : ℝ) ≤ 0 := by linarith
  have hpow_le : (7 / 10 : ℝ) ^ (T2a n) ≤ Real.exp (-(9 / 5) * Real.log n) := by
    have heq : (7 / 10 : ℝ) ^ (T2a n) = Real.exp ((T2a n : ℝ) * Real.log (7 / 10)) := by
      rw [← Real.log_pow, Real.exp_log (by positivity)]
    rw [heq]
    apply Real.exp_le_exp.mpr
    have h1 : (T2a n : ℝ) * Real.log (7/10) ≤ (6 * Real.log n) * Real.log (7/10) :=
      mul_le_mul_of_nonpos_right hT2a hlog710neg
    have h2 : (6 * Real.log n : ℝ) * Real.log (7/10) ≤ (6 * Real.log n) * (-(3/10)) :=
      mul_le_mul_of_nonneg_left hlog710 (by linarith)
    nlinarith [h1, h2]
  have hlog2 : (0.6931 : ℝ) ≤ Real.log n := by
    have h2n : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hn2)
    linarith [Real.log_two_gt_d9]
  have hfinal : (7 / 10 : ℝ) ^ (T2a n) * ((n : ℝ) / 4) ≤ 500 * Real.log n := by
    have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    calc (7 / 10 : ℝ) ^ (T2a n) * ((n : ℝ) / 4)
        ≤ Real.exp (-(9 / 5) * Real.log n) * ((n : ℝ) / 4) :=
          mul_le_mul_of_nonneg_right hpow_le (by positivity)
      _ = Real.exp (-(4/5) * Real.log n) * Real.exp (-Real.log n) * ((n:ℝ)/4) := by
          rw [show (-(9/5) : ℝ) * Real.log n = -(4/5) * Real.log n + (-Real.log n) from by ring,
            Real.exp_add]
      _ = Real.exp (-(4/5) * Real.log n) / 4 := by
          rw [Real.exp_neg, Real.exp_log hn0]
          field_simp
      _ ≤ 1 / 4 := by
          have hexp1 : Real.exp (-(4/5) * Real.log n) ≤ 1 := by
            rw [show (1:ℝ) = Real.exp 0 from (Real.exp_zero).symm]
            apply Real.exp_le_exp.mpr
            nlinarith
          linarith
      _ ≤ 500 * Real.log n := by nlinarith
  exact hfinal

/-- **Stage 2a, wrapped**: starting from any dissent bound `≤ n/4`, after
`T2a n = ⌈6 log n⌉` rounds the dissent count exceeds the floor
`500 log n` with probability at most `T2a n · n⁻²`. -/
lemma saturation_stage2a (hn2 : 2 ≤ n) (hfloor4 : 500 * Real.log n ≤ (n : ℝ) / 4)
    (I₀ : Finset (Fin n)) (hI₀ : (n : ℝ) - I₀.card ≤ (n : ℝ) / 4) :
    expList (Tgt3 n) (T2a n)
        (fun l => if (500 * Real.log n : ℝ) < (n : ℝ) - (run I₀ l).card then (1 : ℝ) else 0)
      ≤ (T2a n : ℝ) * Real.exp (-2 * Real.log n) := by
  have h := saturation_fail_le hn2 hfloor4 (le_refl _) hfloor4 (T2a n) 0 I₀
    (by rw [satAfter_zero n ((n : ℝ) / 4) hfloor4]; exact hI₀)
  rw [Nat.zero_add] at h
  have hle := satAfter_quarter_le_floor (n := n) hn2
  have hmono : ∀ l : List (Tgt3 n),
      (if (500 * Real.log n : ℝ) < (n : ℝ) - (run I₀ l).card then (1 : ℝ) else 0)
        ≤ (if satAfter n ((n : ℝ) / 4) (T2a n) < (n : ℝ) - (run I₀ l).card then (1 : ℝ) else 0) := by
    intro l
    by_cases hc : (500 * Real.log n : ℝ) < (n : ℝ) - (run I₀ l).card
    · have hc2 : satAfter n ((n : ℝ) / 4) (T2a n) < (n : ℝ) - (run I₀ l).card :=
        lt_of_le_of_lt hle hc
      rw [if_pos hc, if_pos hc2]
    · rw [if_neg hc]
      split <;> norm_num
  exact (expList_le_expList hmono).trans h

/-- **Stage 2b**: one round, jumping from the `Θ(log n)` floor directly to
the *fixed* constant `10`. Requires `log n` to be moderately large
(`≥ 30` suffices) — not because the bound is delicate, but because `μ`
(the true mean, `Θ((log n)²/n)`) must beat the *polynomial-in-`log n`*
target `10`; a degree-`11` Taylor lower bound on `exp` (`exp_ge_pow`),
combined with the tangent-line log-log bound `log_log_le_of_pos` (far
tighter, near `log n ≈ 30`, than a bound tangent at the fixed point `e`),
already secures this once `log n ≥ 30` (a low-degree bound such as the
cubic case, or a log-log bound tangent at `e`, would instead force
`log n` to be astronomically large). -/
lemma saturation_stage2b (hbig : (30 : ℝ) ≤ Real.log n)
    (I : Finset (Fin n)) (hUI : (n : ℝ) - I.card ≤ 500 * Real.log n) :
    avg (fun r : Tgt3 n => if (10 : ℝ) ≤ (n : ℝ) - ((step I r).card : ℝ) then (1 : ℝ) else 0)
      ≤ Real.exp (-Real.log n) := by
  have hn2 : 2 ≤ n := two_le_of_hbig hbig
  have hn1 : 1 ≤ n := by omega
  have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  set L : ℝ := Real.log n with hLdef
  have hL0 : 0 < L := by rw [hLdef]; linarith
  have hn_eq : (n : ℝ) = Real.exp L := (Real.exp_log hn0).symm
  set M : ℝ := 500 * L with hMdef
  have hM0 : (0 : ℝ) ≤ M := by rw [hMdef]; positivity
  have hμ := saturation_mean_quad hn1 I hM0 hUI
  set μub : ℝ := 3 * M ^ 2 / n with hμubdef
  have hn_ge_pow : L ^ 11 / (Nat.factorial 11 : ℝ) ≤ (n : ℝ) := by
    have h := exp_ge_pow hL0.le 11; rwa [← hn_eq] at h
  have hL9 : (30 : ℝ) ^ 9 ≤ L ^ 9 := pow_le_pow_left₀ (by norm_num) hbig 9
  have hμub_le9 : μub ≤ 9 := by
    rw [hμubdef, hMdef, div_le_iff₀ hn0]
    have hfact : (Nat.factorial 11 : ℝ) = 39916800 := by norm_num [Nat.factorial]
    rw [hfact] at hn_ge_pow
    nlinarith [hn_ge_pow, hL9, sq_nonneg L]
  have hμub0 : (0 : ℝ) < μub := by rw [hμubdef]; positivity
  have hkμ : μub ≤ (10 : ℝ) := by linarith
  have hround := saturation_round_generic hn1 I hμub0 hkμ hμ
  refine hround.trans (Real.exp_le_exp.mpr ?_)
  have hμub_eq : μub = 750000 * L ^ 2 / Real.exp L := by
    rw [hμubdef, hMdef, hn_eq]; ring
  have hratio_eq : (10:ℝ) / μub = Real.exp L / (75000 * L ^ 2) := by
    rw [hμub_eq]; field_simp; ring
  have hlog_ratio : Real.log (10 / μub) = L - Real.log 75000 - 2 * Real.log L := by
    rw [hratio_eq, Real.log_div (Real.exp_pos L).ne' (by positivity),
      Real.log_exp, Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    push_cast
    ring
  have hloglog : Real.log L ≤ 2 + L / 20 := log_log_le_of_pos hL0
  have hlog75000 : Real.log 75000 ≤ 12 := by
    have h1 : (75000:ℝ) ≤ (2:ℝ) ^ (17:ℕ) := by norm_num
    have h2 : Real.log (75000:ℝ) ≤ Real.log ((2:ℝ) ^ (17:ℕ)) := Real.log_le_log (by norm_num) h1
    rw [Real.log_pow] at h2
    have h3 := Real.log_two_lt_d9
    push_cast at h2
    nlinarith [h2, h3]
  rw [hlog_ratio]
  nlinarith [hloglog, hμub_le9, hμub0, hbig, hL0, hlog75000]

/-- **Stage 2c**: the last round, from `U ≤ 10` to *exactly* `U = 0`, via
ordinary Markov — `U_{t+1}` is a nonnegative integer, so `P[U_{t+1}≥1] ≤
E[U_{t+1}] ≤ 300/n`, no concentration needed at all. -/
lemma saturation_stage2c (hn1 : 1 ≤ n) (I : Finset (Fin n))
    (hUI : (n : ℝ) - I.card ≤ 10) :
    avg (fun r : Tgt3 n => if (1 : ℝ) ≤ (n : ℝ) - ((step I r).card : ℝ) then (1 : ℝ) else 0)
      ≤ 300 / n := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn1⟩⟩
  have hmean := saturation_mean_quad hn1 I (by norm_num : (0:ℝ) ≤ 10) hUI
  have hmean_eq : (3:ℝ) * 10 ^ 2 / n = 300 / n := by ring
  rw [hmean_eq] at hmean
  have hpt : ∀ r : Tgt3 n,
      (if (1 : ℝ) ≤ (n : ℝ) - ((step I r).card : ℝ) then (1 : ℝ) else 0)
        ≤ (n : ℝ) - ((step I r).card : ℝ) := by
    intro r
    have hcard_le : ((step I r).card : ℝ) ≤ n := by exact_mod_cast card_step_le I r
    split_ifs with h <;> linarith
  calc avg (fun r : Tgt3 n => if (1 : ℝ) ≤ (n : ℝ) - ((step I r).card : ℝ) then (1 : ℝ) else 0)
      ≤ avg (fun r : Tgt3 n => (n : ℝ) - ((step I r).card : ℝ)) := avg_le_avg hpt
    _ = ∑ v : Fin n, avg (Y_dis I v) := by
        rw [show (fun r : Tgt3 n => (n : ℝ) - ((step I r).card : ℝ))
            = fun r : Tgt3 n => ∑ v : Fin n, Y_dis I v (r v) from funext (card_dissent_eq_sum I)]
        rw [avg_sum]
        refine Finset.sum_congr rfl fun v _ => ?_
        exact avg_eval n v (Y_dis I v)
    _ ≤ 300 / n := hmean

end ThreeMajority
