import Mathlib

/-!
# Elementary exponential and logarithm bounds

Numeric lemmas underpinning the Chernoff-exponent estimates elsewhere in the
development, none requiring calculus/derivatives:

* `log_ge_quadratic`: the crude linear bound `1 - 1/x ≤ log x` (Mathlib's
  `Real.one_sub_inv_le_log_of_pos`) is *exactly* tangent to `log` at `x = 1`,
  so plugging it into the Chernoff exponent `k - μ - k·log(k/μ)` gives
  *exactly* `0` whenever `k/μ` is close to `1` — useless, since what's
  needed is a bound strictly below `0`. This derives a genuinely
  quadratic-tight lower bound on `log` near `1`, from Mathlib's degree-`3`
  Taylor lower bound for `exp` (`Real.sum_le_exp_of_nonneg`).
* `exp_ge_pow` (with `exp_ge_cube` as its `k = 3` special case): `xᵏ/k! ≤
  exp x` for any degree `k`, the single-term generalization of the same
  Taylor truncation. Picking `k` large enough relative to a given lower
  bound on `log n` is what keeps that bound modest (Stage 2b,
  `saturation_stage2b`) instead of astronomically large.
* `log_le_tangent_div`, `exp_three_ge_twenty`, `log_log_le_of_pos`: a
  tangent-line bound on `log` at an arbitrary reference point `c` (tight at
  `L = c`, unlike a bound tangent at a single fixed point), instantiated at
  `c = exp 3 ≥ 20` to bound `log log n` far more tightly than tangenting at
  `c = e` would — the second ingredient (besides `exp_ge_pow`) that keeps
  `saturation_stage2b`'s threshold on `log n` modest.
-/

namespace ThreeMajority

/-- **Quadratic-tight lower bound on `log`** for `x ∈ [1/2, 1]`:
`log x ≥ (x - 1) - (x - 1)²`. (The crude linear bound `log x ≥ x - 1` is
false for `x < 1`; this corrected version holds throughout `[1/2, 1]`.) -/
lemma log_ge_quadratic {x : ℝ} (hx0 : (1 : ℝ) / 2 ≤ x) (hx1 : x ≤ 1) :
    (x - 1) - (x - 1) ^ 2 ≤ Real.log x := by
  set t : ℝ := 1 - x with ht
  have ht0 : 0 ≤ t := by rw [ht]; linarith
  have ht1 : t ≤ 1 / 2 := by rw [ht]; linarith
  have hs0 : (0 : ℝ) ≤ t + t ^ 2 := by positivity
  have hexp3 := Real.sum_le_exp_of_nonneg hs0 3
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one] at hexp3
  norm_num at hexp3
  have h1 : (1 - t) * (1 + (t + t ^ 2) + (t + t ^ 2) ^ 2 / 2) ≥ 1 := by nlinarith
  have h2 : (1 - t) * Real.exp (t + t ^ 2) ≥ 1 :=
    le_trans h1 (mul_le_mul_of_nonneg_left hexp3 (by linarith))
  have hxpos : (0 : ℝ) < x := by rw [ht] at ht1; linarith
  have hxt : x = 1 - t := by rw [ht]; ring
  have h2' : x * Real.exp (t + t ^ 2) ≥ 1 := by rw [hxt]; exact h2
  have hep : (0 : ℝ) < Real.exp (t + t ^ 2) := Real.exp_pos _
  have h4 : Real.exp (-(t + t ^ 2)) ≤ x := by
    rw [Real.exp_neg, inv_le_iff_one_le_mul₀ hep]
    linarith [h2']
  have h5 : -(t + t ^ 2) ≤ Real.log x := by
    have := Real.log_le_log (Real.exp_pos _) h4
    rwa [Real.log_exp] at this
  have heq : -(t + t ^ 2) = (x - 1) - (x - 1) ^ 2 := by rw [ht]; ring
  linarith [heq ▸ h5]

/-- **Exponential beats any fixed power**: `xᵏ/k! ≤ exp x` for `x ≥ 0`, the
single degree-`k` term of the Taylor series (`Real.sum_le_exp_of_nonneg`),
extracted by dropping every other (nonnegative, since `x ≥ 0`) term of the
sum. Lets `n` be shown astronomically larger than any fixed polynomial in
`log n` using only a *modest* lower bound on `log n`, by picking `k` large
enough relative to that bound (unlike a single fixed low-degree truncation
such as the cubic case `k = 3`, which forces `log n` itself to be
enormous). -/
lemma exp_ge_pow {x : ℝ} (hx : 0 ≤ x) (k : ℕ) : x ^ k / k.factorial ≤ Real.exp x := by
  have h := Real.sum_le_exp_of_nonneg hx (k + 1)
  have hsplit : ∑ i ∈ Finset.range (k + 1), x ^ i / (i.factorial : ℝ)
      = (∑ i ∈ Finset.range k, x ^ i / (i.factorial : ℝ)) + x ^ k / (k.factorial : ℝ) :=
    Finset.sum_range_succ _ k
  have hnonneg : (0 : ℝ) ≤ ∑ i ∈ Finset.range k, x ^ i / (i.factorial : ℝ) :=
    Finset.sum_nonneg fun i _ => by positivity
  linarith [h, hsplit, hnonneg]

/-- **Exponential beats cubic**: `x³/6 ≤ exp x` for `x ≥ 0`. Special case of
`exp_ge_pow` at `k = 3`. -/
lemma exp_ge_cube {x : ℝ} (hx : 0 ≤ x) : x ^ 3 / 6 ≤ Real.exp x := by
  have h := exp_ge_pow hx 3
  norm_num at h
  linarith

/-- **Tangent-line log bound**: for `L > 0` and any reference point `c > 0`,
`log L ≤ log c - 1 + L / c`, from the crude linear bound `log t ≤ t - 1`
applied to `t := L / c`. Tight at `L = c` (equality there), unlike a single
globally-fixed reference point, so choosing `c` close to the `L` actually in
play gives a far sharper bound than e.g. `c = e`. -/
lemma log_le_tangent_div {L c : ℝ} (hL : 0 < L) (hc : 0 < c) :
    Real.log L ≤ Real.log c - 1 + L / c := by
  have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < L / c by positivity)
  rw [Real.log_div (ne_of_gt hL) (ne_of_gt hc)] at h
  linarith

/-- **`exp 3 ≥ 20`**, from cubing the standard `10`-digit lower bound on `e`
(`Real.exp_one_gt_d9`) via `Real.exp_nat_mul`. -/
lemma exp_three_ge_twenty : (20 : ℝ) ≤ Real.exp 3 := by
  have h1 : (2.7182818283 : ℝ) ^ 3 < Real.exp 1 ^ 3 :=
    pow_lt_pow_left₀ Real.exp_one_gt_d9 (by norm_num) (by norm_num)
  have h2 : Real.exp 1 ^ 3 = Real.exp 3 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [h2] at h1
  nlinarith [h1]

/-- **`log log x ≤ 2 + (log x) / 20`** for `log x > 0`: the tangent-line
bound `log_le_tangent_div` at the reference point `c = exp 3` (so
`log c = 3` exactly), combined with `exp_three_ge_twenty` to replace
`1 / exp 3` by the cruder but rational `1 / 20`. Far tighter than a bound
tangent at the fixed point `c = e` once `log x` is more than a few units
above `e`, which is exactly the regime `saturation_stage2b` needs. -/
lemma log_log_le_of_pos {x : ℝ} (hx : 0 < Real.log x) :
    Real.log (Real.log x) ≤ 2 + Real.log x / 20 := by
  have htan := log_le_tangent_div hx (show (0:ℝ) < Real.exp 3 from Real.exp_pos 3)
  rw [Real.log_exp] at htan
  have hinv : Real.log x / Real.exp 3 ≤ Real.log x / 20 :=
    div_le_div_of_nonneg_left hx.le (by norm_num) exp_three_ge_twenty
  linarith [htan, hinv]

/-- **`log n ≥ 30` already forces `n ≥ 2`**: makes an explicit `2 ≤ n`
hypothesis redundant everywhere it appears alongside `hbig`, since
`Real.log 0 = Real.log 1 = 0 < 30`. -/
lemma two_le_of_hbig {n : ℕ} (hbig : (30 : ℝ) ≤ Real.log n) : 2 ≤ n := by
  rcases n with _ | _ | n
  · norm_num [Real.log_zero] at hbig
  · norm_num [Real.log_one] at hbig
  · omega

end ThreeMajority
