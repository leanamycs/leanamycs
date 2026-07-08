import RumorSpread.Growth
import RumorSpread.Saturation

/-!
# Main theorem: push informs the complete graph in `O(log n)` rounds w.h.p.

`prNotAllInformed n v₀ T` is the probability that after `T` rounds of the
uniform push protocol on `K_n`, started from the single informed node `v₀`,
some node is still uninformed.  The main theorem states that for
`T = ⌈117 log n⌉ + 23 + ⌈6 log n⌉ = O(log n)` this probability is `≤ 2/n`.

The constants are deliberately crude (the sharp threshold is
`log₂ n + ln n`): they are chosen so that the verification needs only
`log 2 < 0.694` and the bound `1 - 1/x ≤ log x`.
-/

namespace RumorPush

open Finset

variable {n : ℕ}

/-- Probability that not all nodes are informed after `T` rounds, starting
from the single informed node `v₀`. -/
noncomputable def prNotAllInformed (n : ℕ) (v₀ : Fin n) (T : ℕ) : ℝ :=
  expList (Tgt n) T (fun l => if run {v₀} l = univ then (0 : ℝ) else 1)

/-- Gluing the two phases: failure requires either phase 1 to fail (informed
set still `≤ n/2` after `T₁` rounds) or phase 2 to leave an uninformed node
(controlled by Markov via the expected uninformed count). -/
lemma prNotAllInformed_le (hn : 2 ≤ n) (v₀ : Fin n) (L T₁ T₂ : ℕ)
    (hL : (n : ℝ) ≤ ((9 : ℝ) / 8) ^ L) :
    prNotAllInformed n v₀ (T₁ + T₂)
      ≤ 2 ^ L * ((15 : ℝ) / 16) ^ T₁ + ((2 : ℝ) / 3) ^ T₂ * n := by
  haveI := tgt_nonempty hn
  rw [prNotAllInformed, expList_append]
  have hinner : ∀ l₁ : List (Tgt n),
      expList (Tgt n) T₂
          (fun l₂ => if run {v₀} (l₁ ++ l₂) = univ then (0 : ℝ) else 1)
        ≤ (if 2 * (run {v₀} l₁).card ≤ n then (1 : ℝ) else 0)
            + ((2 : ℝ) / 3) ^ T₂ * n := by
    intro l₁
    by_cases hA : 2 * (run {v₀} l₁).card ≤ n
    · rw [if_pos hA]
      have h1 : expList (Tgt n) T₂
          (fun l₂ => if run {v₀} (l₁ ++ l₂) = univ then (0 : ℝ) else 1) ≤ 1 := by
        calc expList (Tgt n) T₂
              (fun l₂ => if run {v₀} (l₁ ++ l₂) = univ then (0 : ℝ) else 1)
            ≤ expList (Tgt n) T₂ (fun _ => (1 : ℝ)) :=
              expList_le_expList fun l₂ => by split <;> norm_num
          _ = 1 := expList_const _ _
      have h2 : (0 : ℝ) ≤ ((2 : ℝ) / 3) ^ T₂ * n := by positivity
      linarith
    · rw [if_neg hA]
      push_neg at hA
      have hpt : ∀ l₂ : List (Tgt n),
          (if run {v₀} (l₁ ++ l₂) = univ then (0 : ℝ) else 1)
            ≤ (n : ℝ) - (run (run {v₀} l₁) l₂).card := by
        intro l₂
        rw [run_append]
        by_cases h : run (run {v₀} l₁) l₂ = univ
        · rw [if_pos h, h, card_univ, Fintype.card_fin, sub_self]
        · rw [if_neg h]
          have hlt : (run (run {v₀} l₁) l₂).card < n := by
            have hss : run (run {v₀} l₁) l₂ ⊂ univ := ssubset_univ_iff.2 h
            simpa using card_lt_card hss
          have hc : ((run (run {v₀} l₁) l₂).card : ℝ) + 1 ≤ n := by
            exact_mod_cast hlt
          linarith
      calc expList (Tgt n) T₂
            (fun l₂ => if run {v₀} (l₁ ++ l₂) = univ then (0 : ℝ) else 1)
          ≤ expList (Tgt n) T₂
              (fun l₂ => (n : ℝ) - (run (run {v₀} l₁) l₂).card) :=
            expList_le_expList hpt
        _ ≤ ((2 : ℝ) / 3) ^ T₂ * ((n : ℝ) - (run {v₀} l₁).card) :=
            saturation hn T₂ _ (le_of_lt hA)
        _ ≤ ((2 : ℝ) / 3) ^ T₂ * n := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            have h0 : (0 : ℝ) ≤ ((run {v₀} l₁).card : ℝ) := by positivity
            linarith
        _ = 0 + ((2 : ℝ) / 3) ^ T₂ * n := (zero_add _).symm
  calc expList (Tgt n) T₁ (fun l₁ => expList (Tgt n) T₂
          fun l₂ => if run {v₀} (l₁ ++ l₂) = univ then (0 : ℝ) else 1)
      ≤ expList (Tgt n) T₁ (fun l₁ =>
          (if 2 * (run {v₀} l₁).card ≤ n then (1 : ℝ) else 0)
            + ((2 : ℝ) / 3) ^ T₂ * n) :=
        expList_le_expList hinner
    _ = expList (Tgt n) T₁
          (fun l₁ => if 2 * (run {v₀} l₁).card ≤ n then (1 : ℝ) else 0)
          + expList (Tgt n) T₁ (fun _ => ((2 : ℝ) / 3) ^ T₂ * n) :=
        expList_add _ _ _
    _ = expList (Tgt n) T₁
          (fun l₁ => if 2 * (run {v₀} l₁).card ≤ n then (1 : ℝ) else 0)
          + ((2 : ℝ) / 3) ^ T₂ * n := by
        rw [expList_const]
    _ ≤ 2 ^ L * ((15 : ℝ) / 16) ^ T₁ + ((2 : ℝ) / 3) ^ T₂ * n := by
        have h := phase1 hn v₀ L T₁ hL
        linarith

section Numerics

private lemma log_ge_198 : (1 : ℝ) / 9 ≤ Real.log ((9 : ℝ) / 8) := by
  have h := one_sub_inv_le_log (x := (9 : ℝ) / 8) (by norm_num)
  have he : (1 : ℝ) - 1 / ((9 : ℝ) / 8) = 1 / 9 := by norm_num
  linarith

private lemma log_ge_1615 : (1 : ℝ) / 16 ≤ Real.log ((16 : ℝ) / 15) := by
  have h := one_sub_inv_le_log (x := (16 : ℝ) / 15) (by norm_num)
  have he : (1 : ℝ) - 1 / ((16 : ℝ) / 15) = 1 / 16 := by norm_num
  linarith

private lemma log_ge_32 : (1 : ℝ) / 3 ≤ Real.log ((3 : ℝ) / 2) := by
  have h := one_sub_inv_le_log (x := (3 : ℝ) / 2) (by norm_num)
  have he : (1 : ℝ) - 1 / ((3 : ℝ) / 2) = 1 / 3 := by norm_num
  linarith

/-- The choice `L = ⌈9 log n⌉ + 1` makes `(9/8)^L ≥ n`. -/
lemma numeric_A (hn : 2 ≤ n) :
    (n : ℝ) ≤ ((9 : ℝ) / 8) ^ (⌈(9 : ℝ) * Real.log n⌉₊ + 1) := by
  set L := ⌈(9 : ℝ) * Real.log n⌉₊ + 1 with hLdef
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h9 : (9 : ℝ) * Real.log n ≤ (L : ℝ) := by
    rw [hLdef]
    push_cast
    have h := Nat.le_ceil ((9 : ℝ) * Real.log n)
    linarith
  have hkey : Real.log n ≤ (L : ℝ) * Real.log ((9 : ℝ) / 8) := by
    have hL0 : (0 : ℝ) ≤ (L : ℝ) := by positivity
    calc Real.log n = 9 * Real.log n * (1 / 9) := by ring
      _ ≤ (L : ℝ) * (1 / 9) :=
          mul_le_mul_of_nonneg_right h9 (by norm_num)
      _ ≤ (L : ℝ) * Real.log ((9 : ℝ) / 8) :=
          mul_le_mul_of_nonneg_left log_ge_198 hL0
  calc (n : ℝ) = Real.exp (Real.log n) := (Real.exp_log (by linarith)).symm
    _ ≤ Real.exp ((L : ℝ) * Real.log ((9 : ℝ) / 8)) := Real.exp_le_exp.2 hkey
    _ = ((9 : ℝ) / 8) ^ L := by
        rw [← Real.log_pow, Real.exp_log (by positivity)]

/-- With `L = ⌈9 log n⌉ + 1` and `T₁ = ⌈117 log n⌉ + 23`, phase 1 fails with
probability at most `1/n`. -/
lemma numeric_B (hn : 2 ≤ n) :
    2 ^ (⌈(9 : ℝ) * Real.log n⌉₊ + 1)
        * ((15 : ℝ) / 16) ^ (⌈(117 : ℝ) * Real.log n⌉₊ + 23)
      ≤ 1 / n := by
  set L := ⌈(9 : ℝ) * Real.log n⌉₊ + 1 with hLdef
  set T₁ := ⌈(117 : ℝ) * Real.log n⌉₊ + 23 with hT₁def
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hg0 : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
  have hL : (L : ℝ) ≤ 9 * Real.log n + 2 := by
    rw [hLdef]
    push_cast
    have h := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ 9 * Real.log n)
    linarith
  have hT₁ : 117 * Real.log n + 23 ≤ (T₁ : ℝ) := by
    rw [hT₁def]
    push_cast
    have h := Nat.le_ceil ((117 : ℝ) * Real.log n)
    linarith
  have hkey : Real.log n + L * Real.log 2 ≤ T₁ * Real.log ((16 : ℝ) / 15) := by
    have h1 : (L : ℝ) * Real.log 2 ≤ (9 * Real.log n + 2) * 0.6931471808 :=
      mul_le_mul hL (le_of_lt Real.log_two_lt_d9)
        (Real.log_nonneg (by norm_num)) (by linarith)
    have h2 : (117 * Real.log n + 23) * (1 / 16)
        ≤ (T₁ : ℝ) * Real.log ((16 : ℝ) / 15) :=
      mul_le_mul hT₁ log_ge_1615 (by norm_num) (by positivity)
    nlinarith
  rw [le_div_iff₀ hn0]
  have hpos : (0 : ℝ) < 2 ^ L * ((15 : ℝ) / 16) ^ T₁ * n := by positivity
  rw [← Real.log_nonpos_iff hpos.le]
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow]
  have h1516 : Real.log ((15 : ℝ) / 16) = -Real.log ((16 : ℝ) / 15) := by
    rw [show ((15 : ℝ) / 16) = ((16 : ℝ) / 15)⁻¹ by norm_num, Real.log_inv]
  rw [h1516]
  linarith

/-- With `T₂ = ⌈6 log n⌉`, phase 2 fails with probability at most `1/n`. -/
lemma numeric_C (hn : 2 ≤ n) :
    ((2 : ℝ) / 3) ^ (⌈(6 : ℝ) * Real.log n⌉₊) * n ≤ 1 / n := by
  set T₂ := ⌈(6 : ℝ) * Real.log n⌉₊ with hT₂def
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hg0 : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
  have hT₂ : 6 * Real.log n ≤ (T₂ : ℝ) := by
    rw [hT₂def]
    exact Nat.le_ceil _
  have hkey : 2 * Real.log n ≤ T₂ * Real.log ((3 : ℝ) / 2) := by
    have h2 : (6 * Real.log n) * (1 / 3) ≤ (T₂ : ℝ) * Real.log ((3 : ℝ) / 2) :=
      mul_le_mul hT₂ log_ge_32 (by norm_num) (by positivity)
    nlinarith
  rw [le_div_iff₀ hn0]
  have hpos : (0 : ℝ) < ((2 : ℝ) / 3) ^ T₂ * n * n := by positivity
  rw [← Real.log_nonpos_iff hpos.le]
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_pow]
  have h23 : Real.log ((2 : ℝ) / 3) = -Real.log ((3 : ℝ) / 2) := by
    rw [show ((2 : ℝ) / 3) = ((3 : ℝ) / 2)⁻¹ by norm_num, Real.log_inv]
  rw [h23]
  linarith

end Numerics

/-- **Rumor spreading on the complete graph, push model, `O(log n)` rounds.**

Start the uniform push protocol on `K_n` (`n ≥ 2`) with the single informed
node `v₀`.  After `T = (⌈117 log n⌉ + 23) + ⌈6 log n⌉ = O(log n)` rounds, all
`n` nodes are informed with probability at least `1 - 2/n`. -/
theorem push_informs_all_whp (hn : 2 ≤ n) (v₀ : Fin n) :
    prNotAllInformed n v₀
        ((⌈(117 : ℝ) * Real.log n⌉₊ + 23) + ⌈(6 : ℝ) * Real.log n⌉₊)
      ≤ 2 / n := by
  have hA := numeric_A hn
  have hB := numeric_B hn
  have hC := numeric_C hn
  have h := prNotAllInformed_le hn v₀ (⌈(9 : ℝ) * Real.log n⌉₊ + 1)
    (⌈(117 : ℝ) * Real.log n⌉₊ + 23) (⌈(6 : ℝ) * Real.log n⌉₊) hA
  have hn0 : (0 : ℝ) < n := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have htwo : 1 / (n : ℝ) + 1 / n = 2 / n := by ring
  linarith

/-- Complement form: after `(⌈117 log n⌉ + 23) + ⌈6 log n⌉` rounds, **all**
nodes are informed with probability at least `1 - 2/n`. -/
theorem push_informs_all_whp' (hn : 2 ≤ n) (v₀ : Fin n) :
    1 - 2 / (n : ℝ)
      ≤ expList (Tgt n)
          ((⌈(117 : ℝ) * Real.log n⌉₊ + 23) + ⌈(6 : ℝ) * Real.log n⌉₊)
          (fun l => if run {v₀} l = univ then (1 : ℝ) else 0) := by
  haveI := tgt_nonempty hn
  set T := (⌈(117 : ℝ) * Real.log n⌉₊ + 23) + ⌈(6 : ℝ) * Real.log n⌉₊ with hT
  have hsum : expList (Tgt n) T
        (fun l => if run {v₀} l = univ then (1 : ℝ) else 0)
      + prNotAllInformed n v₀ T = 1 := by
    rw [prNotAllInformed, ← expList_add]
    have h : (fun l => (if run {v₀} l = univ then (1 : ℝ) else 0)
        + (if run {v₀} l = univ then (0 : ℝ) else 1)) = fun _ => (1 : ℝ) := by
      funext l
      split <;> norm_num
    rw [h, expList_const]
  have hmain := push_informs_all_whp hn v₀
  rw [← hT] at hmain
  linarith

end RumorPush
