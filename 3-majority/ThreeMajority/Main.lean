import ThreeMajority.Growth
import ThreeMajority.Saturation

/-!
# Main theorem: 3-majority reaches consensus in `O(log n)` rounds w.h.p.

Glues `growth_phase1` (`10` rounds) to the three saturation stages
(`saturation_stage2a`, `2b`, `2c`; `T2a n + 2` rounds total) via the same
`expList`-conditioning idiom the push protocol's `Main.lean` uses to glue
its own two phases (`prNotAllInformed_le`).
-/

namespace ThreeMajority

open Finset

variable {n : ℕ}

/-- `I ≠ univ` iff there is at least one dissenting agent. -/
lemma ne_univ_iff_pos_dissent (I : Finset (Fin n)) :
    I ≠ univ ↔ (1 : ℝ) ≤ (n : ℝ) - (I.card : ℝ) := by
  rw [Ne, ← Finset.card_eq_iff_eq_univ, Fintype.card_fin]
  have hcard_le : I.card ≤ n := by simpa using card_le_card (subset_univ I)
  constructor
  · intro h
    have hlt : I.card < n := lt_of_le_of_ne hcard_le h
    have hle1 : I.card + 1 ≤ n := hlt
    have : ((I.card : ℝ) + 1) ≤ n := by exact_mod_cast hle1
    linarith
  · intro h hcontra
    rw [hcontra] at h
    linarith

/-- **`log n ≥ 30` already forces `500 log n ≤ n/4`**: makes an explicit
`hfloor4` hypothesis redundant everywhere it appears alongside `hbig`. -/
lemma hfloor4_of_hbig (hbig : (30 : ℝ) ≤ Real.log n) :
    500 * Real.log n ≤ (n : ℝ) / 4 := by
  have hn2 : 2 ≤ n := two_le_of_hbig hbig
  have hn1 : 1 ≤ n := by omega
  have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  set L : ℝ := Real.log n with hLdef
  have hL0 : 0 < L := by rw [hLdef]; linarith
  have hn_eq : (n : ℝ) = Real.exp L := (Real.exp_log hn0).symm
  have hn_ge_pow : L ^ 11 / (Nat.factorial 11 : ℝ) ≤ (n : ℝ) := by
    have h := exp_ge_pow hL0.le 11; rwa [← hn_eq] at h
  have hfact : (Nat.factorial 11 : ℝ) = 39916800 := by norm_num [Nat.factorial]
  rw [hfact] at hn_ge_pow
  have hL10 : (30 : ℝ) ^ 10 ≤ L ^ 10 := pow_le_pow_left₀ (by norm_num) hbig 10
  have hL11ge : (30 : ℝ) ^ 10 * L ≤ L ^ 11 := by nlinarith [hL10, hL0.le]
  nlinarith [hn_ge_pow, hL11ge]

/-- **Stages 2b and 2c combined**: two rounds, from `U ≤ 500 log n` to
*exactly* `U = 0`. -/
lemma saturation_2b2c (hbig : (30 : ℝ) ≤ Real.log n) (I : Finset (Fin n))
    (hUI : (n : ℝ) - I.card ≤ 500 * Real.log n) :
    expList (Tgt3 n) 2 (fun l => if (1 : ℝ) ≤ (n : ℝ) - (run I l).card then (1 : ℝ) else 0)
      ≤ Real.exp (-Real.log n) + 300 / n := by
  have hn1 : 1 ≤ n := by have := two_le_of_hbig hbig; omega
  haveI := tgt3_nonempty hn1
  rw [show (2 : ℕ) = 1 + 1 from rfl, expList_succ]
  have hkey : ∀ r1 : Tgt3 n,
      expList (Tgt3 n) 1
          (fun l => if (1 : ℝ) ≤ (n : ℝ) - (run I (r1 :: l)).card then (1 : ℝ) else 0)
        ≤ (if (10 : ℝ) ≤ (n : ℝ) - ((step I r1).card : ℝ) then (1 : ℝ) else 0) + 300 / n := by
    intro r1
    have hstep1 : (fun l : List (Tgt3 n) =>
          if (1 : ℝ) ≤ (n : ℝ) - (run I (r1 :: l)).card then (1 : ℝ) else 0)
        = (fun l : List (Tgt3 n) =>
            if (1 : ℝ) ≤ (n : ℝ) - (run (step I r1) l).card then (1 : ℝ) else 0) := by
      funext l; rw [run_cons]
    rw [hstep1, expList_succ]
    by_cases hcase : (10 : ℝ) ≤ (n : ℝ) - ((step I r1).card : ℝ)
    · rw [if_pos hcase]
      have hpt : ∀ r2 : Tgt3 n, expList (Tgt3 n) 0
          (fun l => if (1 : ℝ) ≤ (n : ℝ) - (run (step I r1) (r2 :: l)).card then (1 : ℝ) else 0)
            ≤ (1 : ℝ) := by
        intro r2; simp only [expList_zero]; split <;> norm_num
      have hbound1 : avg (fun r2 : Tgt3 n => expList (Tgt3 n) 0
          (fun l => if (1 : ℝ) ≤ (n : ℝ) - (run (step I r1) (r2 :: l)).card then (1 : ℝ) else 0))
            ≤ 1 := by
        calc avg (fun r2 : Tgt3 n => expList (Tgt3 n) 0
              (fun l => if (1 : ℝ) ≤ (n : ℝ) - (run (step I r1) (r2 :: l)).card then (1 : ℝ) else 0))
            ≤ avg (fun _ : Tgt3 n => (1 : ℝ)) := avg_le_avg hpt
          _ = 1 := avg_const 1
      have hpos : (0 : ℝ) ≤ 300 / n := by positivity
      linarith
    · rw [if_neg hcase]
      push_neg at hcase
      have hUI2 : (n : ℝ) - ((step I r1).card : ℝ) ≤ 10 := hcase.le
      have h2c := saturation_stage2c hn1 (step I r1) hUI2
      have heq : (fun r2 : Tgt3 n => expList (Tgt3 n) 0
            (fun l => if (1 : ℝ) ≤ (n : ℝ) - (run (step I r1) (r2 :: l)).card then (1 : ℝ) else 0))
          = fun r2 : Tgt3 n =>
              if (1 : ℝ) ≤ (n : ℝ) - ((step (step I r1) r2).card : ℝ) then (1 : ℝ) else 0 := by
        funext r2; rw [expList_zero, run_cons, run_nil]
      rw [heq]
      linarith [h2c]
  calc avg (fun r1 : Tgt3 n => expList (Tgt3 n) 1
        (fun l => if (1 : ℝ) ≤ (n : ℝ) - (run I (r1 :: l)).card then (1 : ℝ) else 0))
      ≤ avg (fun r1 : Tgt3 n =>
          (if (10 : ℝ) ≤ (n : ℝ) - ((step I r1).card : ℝ) then (1 : ℝ) else 0) + 300 / n) :=
        avg_le_avg hkey
    _ = avg (fun r1 : Tgt3 n =>
          if (10 : ℝ) ≤ (n : ℝ) - ((step I r1).card : ℝ) then (1 : ℝ) else 0) + 300 / n := by
        rw [avg_add, avg_const]
    _ ≤ Real.exp (-Real.log n) + 300 / n := by
        linarith [saturation_stage2b hbig I hUI]

/-- **All three saturation stages combined**: `T2a n + 2` rounds, from
`U ≤ n/4` to *exactly* `U = 0`. -/
lemma saturation_2a2b2c (hbig : (30 : ℝ) ≤ Real.log n) (I₀ : Finset (Fin n))
    (hI₀ : (n : ℝ) - I₀.card ≤ (n : ℝ) / 4) :
    expList (Tgt3 n) (T2a n + 2)
        (fun l => if (1 : ℝ) ≤ (n : ℝ) - (run I₀ l).card then (1 : ℝ) else 0)
      ≤ (T2a n : ℝ) * Real.exp (-2 * Real.log n) + (Real.exp (-Real.log n) + 300 / n) := by
  have hn2 : 2 ≤ n := two_le_of_hbig hbig
  have hfloor4 : 500 * Real.log n ≤ (n : ℝ) / 4 := hfloor4_of_hbig hbig
  haveI := tgt3_nonempty (show 1 ≤ n by omega)
  rw [expList_append]
  have hinner : ∀ l₁ : List (Tgt3 n),
      expList (Tgt3 n) 2
          (fun l₂ => if (1 : ℝ) ≤ (n : ℝ) - (run I₀ (l₁ ++ l₂)).card then (1 : ℝ) else 0)
        ≤ (if (500 * Real.log n : ℝ) < (n : ℝ) - (run I₀ l₁).card then (1 : ℝ) else 0)
            + (Real.exp (-Real.log n) + 300 / n) := by
    intro l₁
    by_cases hA : (500 * Real.log n : ℝ) < (n : ℝ) - (run I₀ l₁).card
    · rw [if_pos hA]
      have h1 : expList (Tgt3 n) 2
          (fun l₂ => if (1 : ℝ) ≤ (n : ℝ) - (run I₀ (l₁ ++ l₂)).card then (1 : ℝ) else 0) ≤ 1 := by
        calc expList (Tgt3 n) 2
              (fun l₂ => if (1 : ℝ) ≤ (n : ℝ) - (run I₀ (l₁ ++ l₂)).card then (1 : ℝ) else 0)
            ≤ expList (Tgt3 n) 2 (fun _ => (1 : ℝ)) :=
              expList_le_expList fun l₂ => by split <;> norm_num
          _ = 1 := expList_const 2 1
      have hpos : (0 : ℝ) ≤ Real.exp (-Real.log n) + 300 / n := by positivity
      linarith
    · rw [if_neg hA]
      push_neg at hA
      have h2b2c := saturation_2b2c hbig (run I₀ l₁) hA
      rw [show (fun l₂ : List (Tgt3 n) =>
            if (1 : ℝ) ≤ (n : ℝ) - (run I₀ (l₁ ++ l₂)).card then (1 : ℝ) else 0)
          = fun l₂ : List (Tgt3 n) =>
              if (1 : ℝ) ≤ (n : ℝ) - (run (run I₀ l₁) l₂).card then (1 : ℝ) else 0
          from funext fun l₂ => by rw [run_append]]
      linarith [h2b2c]
  calc expList (Tgt3 n) (T2a n) (fun l₁ => expList (Tgt3 n) 2
          (fun l₂ => if (1 : ℝ) ≤ (n : ℝ) - (run I₀ (l₁ ++ l₂)).card then (1 : ℝ) else 0))
      ≤ expList (Tgt3 n) (T2a n)
          (fun l₁ => (if (500 * Real.log n : ℝ) < (n : ℝ) - (run I₀ l₁).card then (1 : ℝ) else 0)
              + (Real.exp (-Real.log n) + 300 / n)) := expList_le_expList hinner
    _ = expList (Tgt3 n) (T2a n)
          (fun l₁ => if (500 * Real.log n : ℝ) < (n : ℝ) - (run I₀ l₁).card then (1 : ℝ) else 0)
          + expList (Tgt3 n) (T2a n) (fun _ => Real.exp (-Real.log n) + 300 / n) :=
        expList_add _ _ _
    _ = expList (Tgt3 n) (T2a n)
          (fun l₁ => if (500 * Real.log n : ℝ) < (n : ℝ) - (run I₀ l₁).card then (1 : ℝ) else 0)
          + (Real.exp (-Real.log n) + 300 / n) := by rw [expList_const]
    _ ≤ (T2a n : ℝ) * Real.exp (-2 * Real.log n) + (Real.exp (-Real.log n) + 300 / n) := by
        linarith [saturation_stage2a hn2 hfloor4 I₀ hI₀]

/-- **Main theorem**: 3-majority reaches consensus in `10 + T2a n + 2 = O(log n)`
rounds, with failure probability bounded by an explicit, `n`-dependent
constant that `→ 0` as `n → ∞`. Combines `growth_phase1` (`10` rounds) with
`saturation_2a2b2c` (`T2a n + 2` rounds) exactly as the push protocol's
`prNotAllInformed_le` combines its own two phases. -/
theorem majority3_consensus_fail_le (hbig : (30 : ℝ) ≤ Real.log n) (I₀ : Finset (Fin n))
    (hI₀ : (n : ℝ) * (3 / 5) ≤ I₀.card) :
    expList (Tgt3 n) (10 + (T2a n + 2))
        (fun l => if (1 : ℝ) ≤ (n : ℝ) - (run I₀ l).card then (1 : ℝ) else 0)
      ≤ 10 * Real.exp (-(1 / 10 ^ 7) * n)
          + ((T2a n : ℝ) * Real.exp (-2 * Real.log n) + (Real.exp (-Real.log n) + 300 / n)) := by
  have hn1 : 1 ≤ n := by have := two_le_of_hbig hbig; omega
  haveI := tgt3_nonempty hn1
  rw [expList_append]
  have hinner : ∀ l₁ : List (Tgt3 n),
      expList (Tgt3 n) (T2a n + 2)
          (fun l₂ => if (1 : ℝ) ≤ (n : ℝ) - (run I₀ (l₁ ++ l₂)).card then (1 : ℝ) else 0)
        ≤ (if (n : ℝ) * (3 / 4) ≤ ((run I₀ l₁).card : ℝ) then (0 : ℝ) else 1)
            + ((T2a n : ℝ) * Real.exp (-2 * Real.log n)
                + (Real.exp (-Real.log n) + 300 / n)) := by
    intro l₁
    by_cases hA : (n : ℝ) * (3 / 4) ≤ ((run I₀ l₁).card : ℝ)
    · rw [if_pos hA]
      have hUI : (n : ℝ) - (run I₀ l₁).card ≤ (n : ℝ) / 4 := by linarith
      have hsat := saturation_2a2b2c hbig (run I₀ l₁) hUI
      rw [show (fun l₂ : List (Tgt3 n) =>
            if (1 : ℝ) ≤ (n : ℝ) - (run I₀ (l₁ ++ l₂)).card then (1 : ℝ) else 0)
          = fun l₂ : List (Tgt3 n) =>
              if (1 : ℝ) ≤ (n : ℝ) - (run (run I₀ l₁) l₂).card then (1 : ℝ) else 0
          from funext fun l₂ => by rw [run_append]]
      linarith [hsat]
    · rw [if_neg hA]
      have h1 : expList (Tgt3 n) (T2a n + 2)
          (fun l₂ => if (1 : ℝ) ≤ (n : ℝ) - (run I₀ (l₁ ++ l₂)).card then (1 : ℝ) else 0) ≤ 1 := by
        calc expList (Tgt3 n) (T2a n + 2)
              (fun l₂ => if (1 : ℝ) ≤ (n : ℝ) - (run I₀ (l₁ ++ l₂)).card then (1 : ℝ) else 0)
            ≤ expList (Tgt3 n) (T2a n + 2) (fun _ => (1 : ℝ)) :=
              expList_le_expList fun l₂ => by split <;> norm_num
          _ = 1 := expList_const (T2a n + 2) 1
      have hpos : (0 : ℝ) ≤ (T2a n : ℝ) * Real.exp (-2 * Real.log n)
          + (Real.exp (-Real.log n) + 300 / n) := by positivity
      linarith
  calc expList (Tgt3 n) 10 (fun l₁ => expList (Tgt3 n) (T2a n + 2)
        (fun l₂ => if (1 : ℝ) ≤ (n : ℝ) - (run I₀ (l₁ ++ l₂)).card then (1 : ℝ) else 0))
      ≤ expList (Tgt3 n) 10
          (fun l₁ => (if (n : ℝ) * (3 / 4) ≤ ((run I₀ l₁).card : ℝ) then (0 : ℝ) else 1)
              + ((T2a n : ℝ) * Real.exp (-2 * Real.log n) + (Real.exp (-Real.log n) + 300 / n))) :=
        expList_le_expList hinner
    _ = expList (Tgt3 n) 10
          (fun l₁ => if (n : ℝ) * (3 / 4) ≤ ((run I₀ l₁).card : ℝ) then (0 : ℝ) else 1)
          + ((T2a n : ℝ) * Real.exp (-2 * Real.log n) + (Real.exp (-Real.log n) + 300 / n)) := by
        rw [expList_add, expList_const]
    _ ≤ 10 * Real.exp (-(1 / 10 ^ 7) * n)
          + ((T2a n : ℝ) * Real.exp (-2 * Real.log n) + (Real.exp (-Real.log n) + 300 / n)) := by
        linarith [growth_phase1 hn1 I₀ hI₀]

/-- **Clean numeric bound**: the total failure probability is at most
`500/n`. -/
theorem majority3_consensus_fail_le_clean (hbig : (30 : ℝ) ≤ Real.log n)
    (I₀ : Finset (Fin n)) (hI₀ : (n : ℝ) * (3 / 5) ≤ I₀.card) :
    expList (Tgt3 n) (10 + (T2a n + 2))
        (fun l => if (1 : ℝ) ≤ (n : ℝ) - (run I₀ l).card then (1 : ℝ) else 0)
      ≤ 500 / n := by
  have hn1 : 1 ≤ n := by have := two_le_of_hbig hbig; omega
  have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hfloor4 := hfloor4_of_hbig hbig
  have hmain := majority3_consensus_fail_le hbig I₀ hI₀
  refine hmain.trans ?_
  have hL0 : 0 < Real.log n := by linarith
  have hn_ge_pow : (Real.log n) ^ 11 / (Nat.factorial 11 : ℝ) ≤ (n : ℝ) := by
    have h := exp_ge_pow hL0.le 11
    rwa [Real.exp_log hn0] at h
  have hfact11 : (Nat.factorial 11 : ℝ) = 39916800 := by norm_num [Nat.factorial]
  rw [hfact11] at hn_ge_pow
  have hL11 : (30 : ℝ) ^ 11 ≤ (Real.log n) ^ 11 := pow_le_pow_left₀ (by norm_num) hbig 11
  have hbig_n : (4 * 10 ^ 8 : ℝ) ≤ n := by nlinarith [hn_ge_pow, hL11]
  -- term 1: 10 * exp(-n/10^7) ≤ 1/n
  have hterm1 : 10 * Real.exp (-(1 / 10 ^ 7 : ℝ) * n) ≤ 1 / n := by
    have hx_ge : (40:ℝ) ≤ (1/10^7:ℝ) * n := by nlinarith [hbig_n]
    have hx_pos : (0:ℝ) < (1/10^7:ℝ) * n := by nlinarith [hx_ge]
    have hexp_ge : ((1/10^7:ℝ) * n)^11 / (Nat.factorial 11 : ℝ) ≤ Real.exp ((1/10^7:ℝ) * n) :=
      exp_ge_pow hx_pos.le 11
    rw [hfact11] at hexp_ge
    have hy10 : (40:ℝ)^10 ≤ ((1/10^7:ℝ) * n)^10 := pow_le_pow_left₀ (by norm_num) hx_ge 10
    have hkey : 10 * n ≤ Real.exp ((1/10^7:ℝ) * n) := by
      nlinarith [hexp_ge, hx_ge, hy10, hx_pos]
    have hep : (0:ℝ) < Real.exp ((1/10^7:ℝ) * n) := Real.exp_pos _
    have hyeq : -(1 / 10 ^ 7 : ℝ) * n = -((1/10^7:ℝ) * n) := by ring
    rw [hyeq, Real.exp_neg, le_div_iff₀ hn0]
    have hstep := mul_le_mul_of_nonneg_right hkey (inv_nonneg.mpr hep.le)
    rw [mul_inv_cancel₀ (ne_of_gt hep)] at hstep
    nlinarith [hstep]
  -- term 2: T2a n * exp(-2 log n) = T2a n / n^2 ≤ 1/n
  have hterm2 : (T2a n : ℝ) * Real.exp (-2 * Real.log n) ≤ 1 / n := by
    have hexp_eq : Real.exp (-2 * Real.log n) = 1 / n^2 := by
      rw [show (-2 * Real.log n : ℝ) = -(2 * Real.log n) from by ring, Real.exp_neg,
        show (2:ℝ) * Real.log n = Real.log n + Real.log n from by ring,
        Real.exp_add, Real.exp_log hn0]
      ring
    rw [hexp_eq, mul_one_div]
    have hT2a_le : (T2a n : ℝ) ≤ n := by
      have h1 : (T2a n : ℝ) ≤ 6 * Real.log n + 1 := by
        have := Nat.ceil_lt_add_one (by positivity : (0:ℝ) ≤ 6 * Real.log n)
        unfold T2a; linarith
      nlinarith [h1, hfloor4, hbig]
    rw [div_le_div_iff₀ (by positivity : (0:ℝ) < (n:ℝ)^2) hn0, one_mul]
    nlinarith [hT2a_le, hn0]
  -- term 3: exp(-log n) = 1/n exactly
  have hterm3 : Real.exp (-Real.log n) = 1 / n := by
    rw [Real.exp_neg, Real.exp_log hn0, inv_eq_one_div]
  -- term 4: 300/n is already in the right form
  rw [hterm3]
  have heq : (1 : ℝ) / n + (1 / n + (1 / n + 300 / n)) = 303 / n := by ring
  have hle : (303 : ℝ) / n ≤ 500 / n := by gcongr; norm_num
  linarith [hterm1, hterm2, heq, hle]

/-- **Consensus with high probability**: starting from an initial
opinion-`1` majority of at least `60%`, and for `n` large enough
(`log n ≥ 30` suffices), 3-majority reaches *full* consensus within
`10 + T2a n + 2 = O(log n)` rounds with probability at least `1 - 500/n`. -/
theorem majority3_consensus_whp (hbig : (30 : ℝ) ≤ Real.log n)
    (I₀ : Finset (Fin n)) (hI₀ : (n : ℝ) * (3 / 5) ≤ I₀.card) :
    1 - 500 / (n : ℝ)
      ≤ expList (Tgt3 n) (10 + (T2a n + 2)) (fun l => if run I₀ l = univ then (1 : ℝ) else 0) := by
  have hn1 : 1 ≤ n := by have := two_le_of_hbig hbig; omega
  haveI := tgt3_nonempty hn1
  have hfail := majority3_consensus_fail_le_clean hbig I₀ hI₀
  have hsum : expList (Tgt3 n) (10 + (T2a n + 2)) (fun l => if run I₀ l = univ then (1 : ℝ) else 0)
        + expList (Tgt3 n) (10 + (T2a n + 2))
            (fun l => if (1 : ℝ) ≤ (n : ℝ) - (run I₀ l).card then (1 : ℝ) else 0)
      = 1 := by
    rw [← expList_add]
    have heq : (fun l : List (Tgt3 n) => (if run I₀ l = univ then (1 : ℝ) else 0)
          + (if (1 : ℝ) ≤ (n : ℝ) - (run I₀ l).card then (1 : ℝ) else 0)) = fun _ => (1 : ℝ) := by
      funext l
      by_cases h : run I₀ l = univ
      · simp [h]
      · have hd : (1 : ℝ) ≤ (n : ℝ) - (run I₀ l).card := (ne_univ_iff_pos_dissent (run I₀ l)).mp h
        simp [h, hd]
    rw [heq, expList_const]
  linarith [hfail, hsum]

end ThreeMajority
