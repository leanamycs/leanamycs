import Mathlib

/-!
# Elementary inequalities for the rumor-spreading proof

Deterministic real-arithmetic facts (Section 3 of `latex/rumor_push.tex`):

* `one_sub_mul_le_pow`  : Bernoulli, `1 - m·x ≤ (1-x)^m`;
* `mul_sub_sq_le_one_sub_pow` : second-order lower bound
  `m·x - m²·x²/2 ≤ 1 - (1-x)^m`;
* `half_mul_le_one_sub_pow` : `m·x/2 ≤ 1 - (1-x)^m` when `m·x ≤ 1`;
* `pow_one_sub_le_one_div` : `(1-x)^m ≤ 1/(1 + m·x)`;
* `one_sub_inv_le_log` : `1 - 1/x ≤ log x`.

The point of this toolkit is that the whole `O(log n)` rumor-spreading proof
never needs the exponential function.
-/

namespace RumorPush

/-- Bernoulli's inequality in the form `1 - m·x ≤ (1 - x) ^ m`. -/
lemma one_sub_mul_le_pow {x : ℝ} (hx : x ≤ 2) (m : ℕ) :
    1 - m * x ≤ (1 - x) ^ m := by
  have h := one_add_mul_le_pow (a := -x) (by linarith) m
  have h1 : 1 + (m : ℝ) * -x = 1 - m * x := by ring
  have h2 : (1 : ℝ) + -x = 1 - x := by ring
  rwa [h1, h2] at h

/-- Second-order (Bonferroni-type) lower bound:
`m·x - m²·x²/2 ≤ 1 - (1-x)^m` for `0 ≤ x ≤ 1`. -/
lemma mul_sub_sq_le_one_sub_pow {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (m : ℕ) :
    m * x - m ^ 2 * x ^ 2 / 2 ≤ 1 - (1 - x) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hb : 1 - m * x ≤ (1 - x) ^ m := one_sub_mul_le_pow (by linarith) m
    have hbx : (1 - m * x) * x ≤ (1 - x) ^ m * x :=
      mul_le_mul_of_nonneg_right hb hx0
    have hsucc : (1 - x) ^ (m + 1) = (1 - x) ^ m * (1 - x) := pow_succ _ _
    have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
    rw [hsucc, hcast]
    nlinarith [sq_nonneg x, sq_nonneg ((m : ℝ) * x)]

/-- If `m·x ≤ 1` (and `0 ≤ x ≤ 1`) then `m·x/2 ≤ 1 - (1-x)^m`. -/
lemma half_mul_le_one_sub_pow {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) {m : ℕ}
    (hmx : (m : ℝ) * x ≤ 1) :
    m * x / 2 ≤ 1 - (1 - x) ^ m := by
  have h := mul_sub_sq_le_one_sub_pow hx0 hx1 m
  have hm0 : (0 : ℝ) ≤ (m : ℝ) * x := by positivity
  nlinarith [sq_nonneg ((m : ℝ) * x)]

/-- `(1-x)^m ≤ 1/(1 + m·x)` for `0 ≤ x ≤ 1` (an `e`-free upper bound). -/
lemma pow_one_sub_le_one_div {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (m : ℕ) :
    (1 - x) ^ m ≤ 1 / (1 + m * x) := by
  have hpos : (0 : ℝ) < 1 + m * x := by positivity
  rw [le_div_iff₀ hpos]
  have h1 : (0 : ℝ) ≤ (1 - x) ^ m := pow_nonneg (by linarith) m
  have h2 : 1 + (m : ℝ) * x ≤ (1 + x) ^ m := by
    have := one_add_mul_le_pow (a := x) (by linarith) m
    linarith
  calc (1 - x) ^ m * (1 + m * x) ≤ (1 - x) ^ m * (1 + x) ^ m :=
        mul_le_mul_of_nonneg_left h2 h1
    _ = ((1 - x) * (1 + x)) ^ m := (mul_pow _ _ _).symm
    _ = (1 - x ^ 2) ^ m := by ring_nf
    _ ≤ 1 := pow_le_one₀ (by nlinarith) (by nlinarith)

/-- Lower bound on the logarithm: `1 - 1/x ≤ log x` for `0 < x`. -/
lemma one_sub_inv_le_log {x : ℝ} (hx : 0 < x) : 1 - 1 / x ≤ Real.log x := by
  have h := Real.log_le_sub_one_of_pos (x := x⁻¹) (by positivity)
  rw [Real.log_inv] at h
  rw [one_div]
  linarith

end RumorPush
