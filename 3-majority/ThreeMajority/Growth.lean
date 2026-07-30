import ThreeMajority.OneRound
import ThreeMajority.Chernoff
import ThreeMajority.Bounds

/-!
# Growth phase

While the opinion-`1` fraction `x` is in `[3/5, 3/4]` (i.e. bias
`β = x - 1/2 ∈ [1/10, 1/4]`), the majority map amplifies the bias by a
factor `≥ 5/4` per round in expectation (`Corollary growth`, folded into
the numeric argument below); `growth_round` shows this is realized with
probability `≥ 1 - exp(-c₁n)` even with only a guaranteed `11/10` factor of
slack. `growth_fail_le` glues `10` such rounds by induction (exactly the
`expList`-conditioning idiom of the push protocol's `Main.lean`), taking
the bias from `1/10` to strictly above `1/4` (opinion-`1` fraction `> 3/4`)
except with probability `≤ 10 exp(-c₁n)`.

Unlike the push protocol's growth phase (informed sets only grow, so a
counting argument over "good rounds" suffices), the 3-majority count is
*not* monotone in the round index, so every round genuinely needs the
Chernoff bound of `Chernoff.lean` — there is no way to get by with a purely
combinatorial argument here.
-/

namespace ThreeMajority

open Finset

variable {n : ℕ}

/-- The deterministic bias target after `j` growth rounds. -/
noncomputable def growthBias (j : ℕ) : ℝ := (1 / 10) * (11 / 10) ^ j

lemma growthBias_zero : growthBias 0 = 1 / 10 := by unfold growthBias; norm_num

lemma growthBias_nonneg (j : ℕ) : 0 ≤ growthBias j := by
  unfold growthBias; positivity

lemma growthBias_mono (j : ℕ) : growthBias j ≤ growthBias (j + 1) := by
  unfold growthBias
  have : (1 : ℝ) ≤ 11 / 10 := by norm_num
  calc (1/10 : ℝ) * (11/10)^j ≤ (1/10) * (11/10)^j * (11/10) := by
        nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 11/10) j]
    _ = (1/10) * (11/10)^(j+1) := by ring

lemma growthBias_le_of_le {i j : ℕ} (h : i ≤ j) : growthBias i ≤ growthBias j := by
  induction h with
  | refl => exact le_refl _
  | step _ ih => exact ih.trans (growthBias_mono _)

lemma growthBias_le_quarter {j : ℕ} (hj : j ≤ 9) : growthBias j ≤ 1 / 4 := by
  unfold growthBias
  have hpow : (11 / 10 : ℝ) ^ j ≤ (11 / 10 : ℝ) ^ 9 :=
    pow_le_pow_right₀ (by norm_num) hj
  have : (11 / 10 : ℝ) ^ 9 ≤ 5 / 2 := by norm_num
  nlinarith

lemma growthBias_ten : growthBias 10 > 1 / 4 := by
  unfold growthBias
  norm_num

/-- **Single growth round**: starting from opinion-`1` fraction `≥ 1/2+β`
(`β` the current bias, `1/10 ≤ β ≤ 1/4`), the probability of *failing* to
reach the next bias target (guaranteed growth factor `11/10`, comfortably
below the true drift factor `5/4`) is at most `exp(-n/10^7)`. -/
lemma growth_round (hn : 1 ≤ n) (I : Finset (Fin n)) {β : ℝ}
    (hβ0 : (1 : ℝ) / 10 ≤ β) (hβ1 : β ≤ 1 / 4)
    (hI : (n : ℝ) * (1 / 2 + β) ≤ (I.card : ℝ)) :
    avg (fun r : Tgt3 n =>
        if ((step I r).card : ℝ) ≤ (n : ℝ) * (1 / 2 + (11 / 10) * β) then (1 : ℝ) else 0)
      ≤ Real.exp (-(1 / 10 ^ 7) * n) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  set x : ℝ := avg (ind I) with hx
  have hxeq : x = (I.card : ℝ) / n := avg_ind_eq I
  have hcardle : (I.card : ℝ) ≤ n := by exact_mod_cast I.card_le_univ.trans_eq (by simp)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hx0 : 1 / 2 + β ≤ x := by rw [hxeq]; rw [le_div_iff₀ hn0]; linarith
  have hx1 : x ≤ 1 := by rw [hxeq, div_le_one hn0]; exact hcardle
  set k : ℝ := (n : ℝ) * (1 / 2 + (11 / 10) * β) with hk
  set μlb : ℝ := (n : ℝ) * (1 / 2 + (5 / 4) * β) with hμlb
  have hμ : μlb ≤ ∑ v : Fin n, avg (Y_maj I v) := by
    rw [sum_avg_Y_maj hn I, ← hx]
    -- Step A: the identity holds exactly at x = 1/2 + β.
    have hbase : (1 / 2 : ℝ) + (5 / 4) * β ≤ 3 * (1 / 2 + β) ^ 2 - 2 * (1 / 2 + β) ^ 3 := by
      nlinarith [sq_nonneg β, mul_nonneg (by linarith : (0:ℝ) ≤ β) (by nlinarith : (0:ℝ) ≤ 1/4 - 2*β^2)]
    -- Step B: `p` is monotone on `[0,1]`, applied to `y := 1/2+β ≤ x ≤ 1`.
    have hmono : 3 * (1 / 2 + β) ^ 2 - 2 * (1 / 2 + β) ^ 3 ≤ 3 * x ^ 2 - 2 * x ^ 3 := by
      have hy0 : (0:ℝ) ≤ 1 / 2 + β := by linarith
      have hy1 : (1:ℝ) / 2 + β ≤ x := hx0
      have hxy : (0:ℝ) ≤ x - (1/2 + β) := by linarith
      have hxnn : (0:ℝ) ≤ x := by linarith
      have h1x : (0:ℝ) ≤ 1 - x := by linarith
      have h1y : (0:ℝ) ≤ 1 - (1/2+β) := by linarith
      nlinarith [mul_nonneg (mul_nonneg hxy hxnn) h1y,
        mul_nonneg (mul_nonneg hxy hy0) h1x,
        mul_nonneg (mul_nonneg hxy hxnn) h1x,
        mul_nonneg (mul_nonneg hxy hy0) h1y]
    have hcomb : (1 / 2 : ℝ) + 5 / 4 * β ≤ 3 * x ^ 2 - 2 * x ^ 3 := le_trans hbase hmono
    have hscaled : (n : ℝ) * (1 / 2 + 5 / 4 * β) ≤ (n : ℝ) * (3 * x ^ 2 - 2 * x ^ 3) :=
      mul_le_mul_of_nonneg_left hcomb hn0.le
    rw [hμlb]
    exact hscaled
  have hk0 : 0 < k := by rw [hk]; nlinarith
  have hkμ : k ≤ μlb := by rw [hk, hμlb]; nlinarith
  have hbound := avg_tail_le_log_ge (Y_maj I) (Y_maj_zero_one I) hμ hk0 hkμ
  rw [show (fun x : Fin n → Fin n × Fin n × Fin n =>
        if ∑ i, Y_maj I i (x i) ≤ k then (1 : ℝ) else 0)
      = fun r : Tgt3 n => if ((step I r).card : ℝ) ≤ k then (1 : ℝ) else 0
      from funext fun r => by rw [card_step_eq_sum]] at hbound
  refine hbound.trans (Real.exp_le_exp.mpr ?_)
  have hμlb0 : 0 < μlb := by rw [hμlb]; nlinarith
  have hρ0 : (1 : ℝ) / 2 ≤ k / μlb := by
    rw [le_div_iff₀ hμlb0]; rw [hk, hμlb]; nlinarith
  have hρ1 : k / μlb ≤ 1 := by
    rw [div_le_one hμlb0]; exact hkμ
  have hlog := log_ge_quadratic hρ0 hρ1
  have hlogk : k * ((k / μlb - 1) - (k / μlb - 1) ^ 2) ≤ k * Real.log (k / μlb) :=
    mul_le_mul_of_nonneg_left hlog hk0.le
  -- Substitute `lam := μlb - k > 0`; the exponent reduces to `-lam^3/μlb^2`.
  set lam : ℝ := μlb - k with hlamdef
  have hlam_pos : 0 < lam := by rw [hlamdef, hk, hμlb]; nlinarith
  have hρm1 : k / μlb - 1 = -lam / μlb := by
    rw [hlamdef, div_sub_one (ne_of_gt hμlb0)]; ring
  have hcubic : lam ^ 3 ≥ (1 / 10 ^ 7) * n * μlb ^ 2 := by
    have hlam_eq : lam = (n : ℝ) * ((3 / 20) * β) := by rw [hlamdef, hk, hμlb]; ring
    have hβcubed : (1 / 10 ^ 7 : ℝ) * (1 / 2 + 5 / 4 * β) ^ 2 ≤ (3 / 20 * β) ^ 3 := by
      nlinarith [hβ0, hβ1, sq_nonneg β, mul_nonneg (by linarith : (0:ℝ) ≤ β - 1/10)
        (by linarith : (0:ℝ) ≤ 1/4 - β)]
    rw [hlam_eq, hμlb]
    have hexpand1 : ((n:ℝ) * (3/20 * β)) ^ 3 = (n:ℝ)^3 * (3/20*β)^3 := by ring
    have hexpand2 : (1/10^7 : ℝ) * n * ((n:ℝ) * (1/2+5/4*β))^2
        = (n:ℝ)^3 * ((1/10^7) * (1/2+5/4*β)^2) := by ring
    rw [hexpand1, hexpand2]
    exact mul_le_mul_of_nonneg_left hβcubed (by positivity)
  have hclear : k - μlb - k * ((k / μlb - 1) - (k / μlb - 1) ^ 2) ≤ -(1 / 10 ^ 7) * n := by
    rw [hρm1]
    have hstep : k - μlb - k * (-lam / μlb - (-lam / μlb) ^ 2) = -(lam ^ 3 / μlb ^ 2) := by
      rw [hlamdef]
      field_simp
      ring
    rw [hstep]
    have hfrac : (1 / 10 ^ 7 : ℝ) * n ≤ lam ^ 3 / μlb ^ 2 := by
      rw [le_div_iff₀ (by positivity : (0:ℝ) < μlb ^ 2)]
      linarith [hcubic]
    linarith [hfrac]
  linarith [hlogk, hclear]

/-- **Union bound over `j` growth rounds**, starting from bias `growthBias i`
(offset `i`, with `i + j ≤ 10` so the bias never leaves `[1/10, 1/4]`):
the probability of failing to reach the bias target `growthBias (i+j)` is
at most `j · exp(-n/10⁷)`. Mirrors the `expList`-conditioning idiom of the
push protocol's `Main.lean`/`Growth.lean`. -/
lemma growth_fail_le (hn : 1 ≤ n) (j : ℕ) :
    ∀ (i : ℕ), i + j ≤ 10 → ∀ (I : Finset (Fin n)),
      (n : ℝ) * (1 / 2 + growthBias i) ≤ (I.card : ℝ) →
      expList (Tgt3 n) j
          (fun l => if (n : ℝ) * (1 / 2 + growthBias (i + j)) ≤ ((run I l).card : ℝ)
              then (0 : ℝ) else 1)
        ≤ j * Real.exp (-(1 / 10 ^ 7) * n) := by
  haveI := tgt3_nonempty hn
  induction j with
  | zero =>
    intro i _ I hI
    simp only [Nat.add_zero, expList_zero, run_nil]
    rw [if_pos hI]
    norm_num
  | succ j ih =>
    intro i hij I hI
    rw [expList_succ]
    have hi1 : i ≤ 9 := by omega
    have hβ0 : (1 : ℝ) / 10 ≤ growthBias i := by
      rw [← growthBias_zero]; exact growthBias_le_of_le (Nat.zero_le i)
    have hβ1 : growthBias i ≤ 1 / 4 := growthBias_le_quarter hi1
    have hgrowth := growth_round hn I hβ0 hβ1 hI
    have hkey : ∀ r : Tgt3 n,
        expList (Tgt3 n) j
            (fun l => if (n : ℝ) * (1 / 2 + growthBias (i + (j + 1))) ≤ ((run I (r :: l)).card : ℝ)
                then (0 : ℝ) else 1)
          ≤ (if ((step I r).card : ℝ) ≤ (n : ℝ) * (1 / 2 + growthBias (i + 1))
              then (1 : ℝ) else 0) + j * Real.exp (-(1 / 10 ^ 7) * n) := by
      intro r
      simp only [run_cons]
      by_cases hcase : (n : ℝ) * (1 / 2 + growthBias (i + 1)) ≤ ((step I r).card : ℝ)
      · have hthis := ih (i + 1) (by omega) (step I r) hcase
        have hidx : i + 1 + j = i + (j + 1) := by omega
        rw [hidx] at hthis
        have hnn : (0:ℝ) ≤ if ((step I r).card : ℝ) ≤ (n : ℝ) * (1 / 2 + growthBias (i + 1))
            then (1:ℝ) else 0 := by split <;> norm_num
        linarith
      · rw [if_pos (not_le.mp hcase).le]
        have hbound1 : expList (Tgt3 n) j
            (fun l => if (n : ℝ) * (1 / 2 + growthBias (i + (j + 1))) ≤ ((run (step I r) l).card : ℝ)
                then (0 : ℝ) else 1) ≤ 1 := by
          calc expList (Tgt3 n) j
                (fun l => if (n : ℝ) * (1 / 2 + growthBias (i + (j + 1)))
                    ≤ ((run (step I r) l).card : ℝ) then (0 : ℝ) else 1)
              ≤ expList (Tgt3 n) j (fun _ => (1 : ℝ)) :=
                expList_le_expList fun l => by split <;> norm_num
            _ = 1 := expList_const j 1
        have hpos : (0:ℝ) ≤ j * Real.exp (-(1/10^7) * n) := by positivity
        linarith
    calc avg (fun r : Tgt3 n => expList (Tgt3 n) j
          (fun l => if (n : ℝ) * (1 / 2 + growthBias (i + (j + 1)))
              ≤ ((run I (r :: l)).card : ℝ) then (0 : ℝ) else 1))
        ≤ avg (fun r : Tgt3 n =>
            (if ((step I r).card : ℝ) ≤ (n : ℝ) * (1 / 2 + growthBias (i + 1))
                then (1 : ℝ) else 0) + j * Real.exp (-(1 / 10 ^ 7) * n)) :=
          avg_le_avg hkey
      _ = avg (fun r : Tgt3 n => if ((step I r).card : ℝ)
              ≤ (n : ℝ) * (1 / 2 + growthBias (i + 1)) then (1 : ℝ) else 0)
            + j * Real.exp (-(1 / 10 ^ 7) * n) := by
          rw [avg_add, avg_const]
      _ = avg (fun r : Tgt3 n => if ((step I r).card : ℝ)
              ≤ (n : ℝ) * (1 / 2 + 11 / 10 * growthBias i) then (1 : ℝ) else 0)
            + j * Real.exp (-(1 / 10 ^ 7) * n) := by
          rw [show growthBias (i + 1) = 11 / 10 * growthBias i from by
            unfold growthBias; ring]
      _ ≤ Real.exp (-(1 / 10 ^ 7) * n) + j * Real.exp (-(1 / 10 ^ 7) * n) := by linarith [hgrowth]
      _ = (↑(j + 1) : ℝ) * Real.exp (-(1 / 10 ^ 7) * n) := by push_cast; ring

/-- **Phase 1**: starting from opinion-`1` fraction `≥ 3/5`, after `10`
rounds the opinion-`1` fraction exceeds `3/4`, except with probability
`≤ 10 · exp(-n/10⁷)`. -/
lemma growth_phase1 (hn : 1 ≤ n) (I₀ : Finset (Fin n))
    (hI₀ : (n : ℝ) * (3 / 5) ≤ (I₀.card : ℝ)) :
    expList (Tgt3 n) 10
        (fun l => if (n : ℝ) * (3 / 4) ≤ ((run I₀ l).card : ℝ) then (0 : ℝ) else 1)
      ≤ 10 * Real.exp (-(1 / 10 ^ 7) * n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h := growth_fail_le hn 10 0 (by omega) I₀ (by
    rw [growthBias_zero]; convert hI₀ using 2; norm_num)
  rw [show (0 : ℕ) + 10 = 10 from rfl] at h
  have hbias : growthBias 10 > 1 / 4 := growthBias_ten
  have hmono : ∀ l : List (Tgt3 n),
      (if (n : ℝ) * (3 / 4) ≤ ((run I₀ l).card : ℝ) then (0 : ℝ) else 1)
        ≤ (if (n : ℝ) * (1 / 2 + growthBias 10) ≤ ((run I₀ l).card : ℝ) then (0 : ℝ) else 1) := by
    intro l
    by_cases hc : (n : ℝ) * (3 / 4) ≤ ((run I₀ l).card : ℝ)
    · by_cases hc2 : (n : ℝ) * (1 / 2 + growthBias 10) ≤ ((run I₀ l).card : ℝ)
      · rw [if_pos hc, if_pos hc2]
      · rw [if_pos hc, if_neg hc2]; norm_num
    · rw [if_neg hc]
      by_cases hc2 : (n : ℝ) * (1 / 2 + growthBias 10) ≤ ((run I₀ l).card : ℝ)
      · exfalso
        push_neg at hc
        have : (n : ℝ) * (3 / 4) < (n : ℝ) * (1 / 2 + growthBias 10) := by nlinarith
        linarith
      · rw [if_neg hc2]
  exact (expList_le_expList hmono).trans h

end ThreeMajority
