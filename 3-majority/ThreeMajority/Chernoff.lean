import Mathlib
import ThreeMajority.Prob

/-!
# An elementary Chernoff bound

The only concentration tool used in this development, and the only place
where `Real.exp`/`Real.log` are structurally central (rather than confined
to a numeric side lemma, as in the push protocol). Everything here is
proved from the single elementary inequality `1 + x ≤ Real.exp x`
(`Real.add_one_le_exp`) plus `avg_prod_pi` (independence) — no measure
theory, no PMF, no appeal to Mathlib's `ProbabilityTheory` library.

* `avg_exp_le` — the moment-generating-function bound for a sum of
  independent `{0,1}`-valued trials: `𝔼[exp(tX)] ≤ exp(μ(eᵗ-1))` for every
  real `t` (no sign restriction).
* `avg_tail_ge` / `avg_tail_le` — the Chernoff tail bounds obtained from it
  via Markov's inequality applied to `exp(tX)`, for `t ≥ 0` / `t ≤ 0`
  respectively.
* `avg_tail_ge_log` / `avg_tail_le_log` — the closed forms obtained by
  plugging in the optimal `t = log(k/μ)`. These closed forms are
  *mean-scaled*: their strength depends on `μ`, not on a crude worst-case
  range/variance proxy, which is exactly what is needed to control the
  process even once very few "at-risk" agents remain (see the saturation
  phase).
-/

namespace ThreeMajority

open Finset Real

variable {n : ℕ} {γ : Type*} [Fintype γ]

/-- **MGF bound for a sum of independent `{0,1}`-valued trials.** `Y i x` is
agent `i`'s contribution when its private randomness is `x : γ`; the sum
`∑ i, Y i (ω i)` is taken over the product space `Fin n → γ` (one
independent draw of `γ` per agent `i`). No sign restriction on `t`. -/
lemma avg_exp_le (Y : Fin n → γ → ℝ) (hY : ∀ i x, Y i x = 0 ∨ Y i x = 1) (t : ℝ) :
    avg (fun x : Fin n → γ => Real.exp (t * ∑ i, Y i (x i)))
      ≤ Real.exp ((∑ i, avg (Y i)) * (Real.exp t - 1)) := by
  have hpt : ∀ x : Fin n → γ, Real.exp (t * ∑ i, Y i (x i)) = ∏ i, Real.exp (t * Y i (x i)) := by
    intro x
    rw [Finset.mul_sum, Real.exp_sum]
  rw [show (fun x : Fin n → γ => Real.exp (t * ∑ i, Y i (x i)))
      = fun x : Fin n → γ => ∏ i, Real.exp (t * Y i (x i)) from funext hpt,
    avg_prod_pi n (fun i y => Real.exp (t * Y i y))]
  have hone : ∀ i : Fin n, avg (fun y : γ => Real.exp (t * Y i y))
      ≤ Real.exp (avg (Y i) * (Real.exp t - 1)) := by
    intro i
    have hpt2 : ∀ y : γ, Real.exp (t * Y i y) = 1 + Y i y * (Real.exp t - 1) := by
      intro y
      rcases hY i y with h0 | h1
      · rw [h0]; simp
      · rw [h1]; simp
    rw [show (fun y : γ => Real.exp (t * Y i y))
        = fun y : γ => 1 + Y i y * (Real.exp t - 1) from funext hpt2]
    rw [show (fun y : γ => (1 : ℝ) + Y i y * (Real.exp t - 1))
        = fun y : γ => (fun _ : γ => (1 : ℝ)) y
            + (fun y : γ => (Real.exp t - 1) * Y i y) y from
          funext fun y => by rw [mul_comm]]
    rcases isEmpty_or_nonempty γ with hγ | hγ
    · simp [avg]
    · rw [avg_add, avg_const, avg_const_mul, mul_comm (Real.exp t - 1) (avg (Y i))]
      linarith [Real.add_one_le_exp (avg (Y i) * (Real.exp t - 1))]
  calc ∏ i, avg (fun y : γ => Real.exp (t * Y i y))
      ≤ ∏ i, Real.exp (avg (Y i) * (Real.exp t - 1)) := by
        apply Finset.prod_le_prod
        · intro i _
          rcases isEmpty_or_nonempty γ with hγ | hγ
          · simp [avg]
          · exact avg_nonneg (fun y => (Real.exp_pos _).le)
        · intro i _
          exact hone i
    _ = Real.exp (∑ i, avg (Y i) * (Real.exp t - 1)) := by rw [Real.exp_sum]
    _ = Real.exp ((∑ i, avg (Y i)) * (Real.exp t - 1)) := by rw [Finset.sum_mul]

/-- **Upper-tail Chernoff bound** via Markov's inequality applied to
`exp(t·(X-k))`, for `t ≥ 0`. -/
lemma avg_tail_ge (Y : Fin n → γ → ℝ) (hY : ∀ i x, Y i x = 0 ∨ Y i x = 1)
    {t : ℝ} (ht : 0 ≤ t) (k : ℝ) :
    avg (fun x : Fin n → γ => if k ≤ ∑ i, Y i (x i) then (1 : ℝ) else 0)
      ≤ Real.exp ((∑ i, avg (Y i)) * (Real.exp t - 1) - t * k) := by
  have hpt : ∀ x : Fin n → γ,
      (if k ≤ ∑ i, Y i (x i) then (1 : ℝ) else 0)
        ≤ Real.exp (t * ∑ i, Y i (x i)) * Real.exp (-(t * k)) := by
    intro x
    rw [← Real.exp_add]
    split_ifs with h
    · have h0 : (0 : ℝ) ≤ t * (∑ i, Y i (x i)) + -(t * k) := by nlinarith
      calc (1 : ℝ) ≤ Real.exp 0 := by simp
        _ ≤ _ := Real.exp_le_exp.mpr h0
    · exact (Real.exp_pos _).le
  calc avg (fun x : Fin n → γ => if k ≤ ∑ i, Y i (x i) then (1 : ℝ) else 0)
      ≤ avg (fun x : Fin n → γ =>
          Real.exp (t * ∑ i, Y i (x i)) * Real.exp (-(t * k))) := avg_le_avg hpt
    _ = avg (fun x : Fin n → γ => Real.exp (t * ∑ i, Y i (x i))) * Real.exp (-(t * k)) := by
        rw [show (fun x : Fin n → γ =>
              Real.exp (t * ∑ i, Y i (x i)) * Real.exp (-(t * k)))
            = fun x : Fin n → γ => Real.exp (-(t * k)) * Real.exp (t * ∑ i, Y i (x i))
            from funext fun x => mul_comm _ _]
        rw [avg_const_mul, mul_comm]
    _ ≤ Real.exp ((∑ i, avg (Y i)) * (Real.exp t - 1)) * Real.exp (-(t * k)) :=
        mul_le_mul_of_nonneg_right (avg_exp_le Y hY t) (Real.exp_pos _).le
    _ = Real.exp ((∑ i, avg (Y i)) * (Real.exp t - 1) - t * k) := by
        rw [← Real.exp_add]; ring_nf

/-- **Lower-tail Chernoff bound** via Markov's inequality applied to
`exp(t·(X-k))`, for `t ≤ 0`. -/
lemma avg_tail_le (Y : Fin n → γ → ℝ) (hY : ∀ i x, Y i x = 0 ∨ Y i x = 1)
    {t : ℝ} (ht : t ≤ 0) (k : ℝ) :
    avg (fun x : Fin n → γ => if ∑ i, Y i (x i) ≤ k then (1 : ℝ) else 0)
      ≤ Real.exp ((∑ i, avg (Y i)) * (Real.exp t - 1) - t * k) := by
  have hpt : ∀ x : Fin n → γ,
      (if ∑ i, Y i (x i) ≤ k then (1 : ℝ) else 0)
        ≤ Real.exp (t * ∑ i, Y i (x i)) * Real.exp (-(t * k)) := by
    intro x
    rw [← Real.exp_add]
    split_ifs with h
    · have h0 : (0 : ℝ) ≤ t * (∑ i, Y i (x i)) + -(t * k) := by nlinarith
      calc (1 : ℝ) ≤ Real.exp 0 := by simp
        _ ≤ _ := Real.exp_le_exp.mpr h0
    · exact (Real.exp_pos _).le
  calc avg (fun x : Fin n → γ => if ∑ i, Y i (x i) ≤ k then (1 : ℝ) else 0)
      ≤ avg (fun x : Fin n → γ =>
          Real.exp (t * ∑ i, Y i (x i)) * Real.exp (-(t * k))) := avg_le_avg hpt
    _ = avg (fun x : Fin n → γ => Real.exp (t * ∑ i, Y i (x i))) * Real.exp (-(t * k)) := by
        rw [show (fun x : Fin n → γ =>
              Real.exp (t * ∑ i, Y i (x i)) * Real.exp (-(t * k)))
            = fun x : Fin n → γ => Real.exp (-(t * k)) * Real.exp (t * ∑ i, Y i (x i))
            from funext fun x => mul_comm _ _]
        rw [avg_const_mul, mul_comm]
    _ ≤ Real.exp ((∑ i, avg (Y i)) * (Real.exp t - 1)) * Real.exp (-(t * k)) :=
        mul_le_mul_of_nonneg_right (avg_exp_le Y hY t) (Real.exp_pos _).le
    _ = Real.exp ((∑ i, avg (Y i)) * (Real.exp t - 1) - t * k) := by
        rw [← Real.exp_add]; ring_nf

/-- **Closed-form upper tail**, obtained from `avg_tail_ge` by plugging in
the optimal `t = log(k/μ)`. Mean-scaled: strong whenever `k/μ` is
bounded away from `1`, regardless of the absolute scale of `μ`. -/
lemma avg_tail_ge_log (Y : Fin n → γ → ℝ) (hY : ∀ i x, Y i x = 0 ∨ Y i x = 1)
    {k μ : ℝ} (hμ : μ = ∑ i, avg (Y i)) (hμ0 : 0 < μ) (hk : μ ≤ k) :
    avg (fun x : Fin n → γ => if k ≤ ∑ i, Y i (x i) then (1 : ℝ) else 0)
      ≤ Real.exp (k - μ - k * Real.log (k / μ)) := by
  have hk0 : 0 < k := lt_of_lt_of_le hμ0 hk
  have ht : 0 ≤ Real.log (k / μ) :=
    Real.log_nonneg (by rw [le_div_iff₀ hμ0]; linarith)
  have hbound := avg_tail_ge Y hY ht k
  rw [← hμ] at hbound
  have hexp : Real.exp (Real.log (k / μ)) = k / μ := Real.exp_log (by positivity)
  have heq : μ * (Real.exp (Real.log (k / μ)) - 1) - Real.log (k / μ) * k
      = k - μ - k * Real.log (k / μ) := by
    rw [hexp]; field_simp
  rwa [heq] at hbound

/-- **Closed-form lower tail**, obtained from `avg_tail_le` by plugging in
the optimal `t = log(k/μ)` (now `≤ 0`, since `k ≤ μ`). -/
lemma avg_tail_le_log (Y : Fin n → γ → ℝ) (hY : ∀ i x, Y i x = 0 ∨ Y i x = 1)
    {k μ : ℝ} (hμ : μ = ∑ i, avg (Y i)) (hk0 : 0 < k) (hkμ : k ≤ μ) :
    avg (fun x : Fin n → γ => if ∑ i, Y i (x i) ≤ k then (1 : ℝ) else 0)
      ≤ Real.exp (k - μ - k * Real.log (k / μ)) := by
  have hμ0 : 0 < μ := lt_of_lt_of_le hk0 hkμ
  have ht : Real.log (k / μ) ≤ 0 :=
    Real.log_nonpos (by positivity) (by rw [div_le_one hμ0]; exact hkμ)
  have hbound := avg_tail_le Y hY ht k
  rw [← hμ] at hbound
  have hexp : Real.exp (Real.log (k / μ)) = k / μ := Real.exp_log (by positivity)
  have heq : μ * (Real.exp (Real.log (k / μ)) - 1) - Real.log (k / μ) * k
      = k - μ - k * Real.log (k / μ) := by
    rw [hexp]; field_simp
  rwa [heq] at hbound

/-- **Generalized closed-form upper tail**: same conclusion as
`avg_tail_ge_log`, but only assuming an *upper bound* `μub` on the true
mean `∑ i, avg (Y i)` (not exact equality) — the exponent is monotone in
`μ` for the optimal `t`, so using the (larger) upper bound only weakens
the bound, which is exactly the direction needed downstream. -/
lemma avg_tail_ge_log_le (Y : Fin n → γ → ℝ) (hY : ∀ i x, Y i x = 0 ∨ Y i x = 1)
    {k μub : ℝ} (hμ : (∑ i, avg (Y i)) ≤ μub) (hμub0 : 0 < μub) (hk : μub ≤ k) :
    avg (fun x : Fin n → γ => if k ≤ ∑ i, Y i (x i) then (1 : ℝ) else 0)
      ≤ Real.exp (k - μub - k * Real.log (k / μub)) := by
  have ht : 0 ≤ Real.log (k / μub) := Real.log_nonneg (by rw [le_div_iff₀ hμub0]; linarith)
  have hbound := avg_tail_ge Y hY ht k
  have hslope : 0 ≤ Real.exp (Real.log (k / μub)) - 1 := by
    have h0 : Real.exp 0 ≤ Real.exp (Real.log (k / μub)) := Real.exp_le_exp.mpr ht
    simpa using h0
  have hmono : (∑ i, avg (Y i)) * (Real.exp (Real.log (k / μub)) - 1) - Real.log (k / μub) * k
      ≤ μub * (Real.exp (Real.log (k / μub)) - 1) - Real.log (k / μub) * k := by
    have := mul_le_mul_of_nonneg_right hμ hslope
    linarith
  have hk0 : 0 < k := lt_of_lt_of_le hμub0 hk
  have hexp : Real.exp (Real.log (k / μub)) = k / μub := Real.exp_log (by positivity)
  have heq : μub * (Real.exp (Real.log (k / μub)) - 1) - Real.log (k / μub) * k
      = k - μub - k * Real.log (k / μub) := by
    rw [hexp]; field_simp
  calc avg (fun x : Fin n → γ => if k ≤ ∑ i, Y i (x i) then (1 : ℝ) else 0)
      ≤ Real.exp ((∑ i, avg (Y i)) * (Real.exp (Real.log (k / μub)) - 1)
          - Real.log (k / μub) * k) := hbound
    _ ≤ Real.exp (μub * (Real.exp (Real.log (k / μub)) - 1) - Real.log (k / μub) * k) :=
        Real.exp_le_exp.mpr hmono
    _ = Real.exp (k - μub - k * Real.log (k / μub)) := by rw [heq]

/-- **Generalized closed-form lower tail**: same conclusion as
`avg_tail_le_log`, but only assuming a *lower bound* `μlb` on the true
mean (not exact equality). -/
lemma avg_tail_le_log_ge (Y : Fin n → γ → ℝ) (hY : ∀ i x, Y i x = 0 ∨ Y i x = 1)
    {k μlb : ℝ} (hμ : μlb ≤ ∑ i, avg (Y i)) (hk0 : 0 < k) (hkμ : k ≤ μlb) :
    avg (fun x : Fin n → γ => if ∑ i, Y i (x i) ≤ k then (1 : ℝ) else 0)
      ≤ Real.exp (k - μlb - k * Real.log (k / μlb)) := by
  have hμlb0 : 0 < μlb := lt_of_lt_of_le hk0 hkμ
  have ht : Real.log (k / μlb) ≤ 0 :=
    Real.log_nonpos (by positivity) (by rw [div_le_one hμlb0]; exact hkμ)
  have hbound := avg_tail_le Y hY ht k
  have hslope : Real.exp (Real.log (k / μlb)) - 1 ≤ 0 := by
    have h0 : Real.exp (Real.log (k / μlb)) ≤ Real.exp 0 := Real.exp_le_exp.mpr ht
    simpa using h0
  have hmono : (∑ i, avg (Y i)) * (Real.exp (Real.log (k / μlb)) - 1) - Real.log (k / μlb) * k
      ≤ μlb * (Real.exp (Real.log (k / μlb)) - 1) - Real.log (k / μlb) * k := by
    have := mul_le_mul_of_nonpos_right hμ hslope
    linarith
  have hexp : Real.exp (Real.log (k / μlb)) = k / μlb := Real.exp_log (by positivity)
  have heq : μlb * (Real.exp (Real.log (k / μlb)) - 1) - Real.log (k / μlb) * k
      = k - μlb - k * Real.log (k / μlb) := by
    rw [hexp]; field_simp
  calc avg (fun x : Fin n → γ => if ∑ i, Y i (x i) ≤ k then (1 : ℝ) else 0)
      ≤ Real.exp ((∑ i, avg (Y i)) * (Real.exp (Real.log (k / μlb)) - 1)
          - Real.log (k / μlb) * k) := hbound
    _ ≤ Real.exp (μlb * (Real.exp (Real.log (k / μlb)) - 1) - Real.log (k / μlb) * k) :=
        Real.exp_le_exp.mpr hmono
    _ = Real.exp (k - μlb - k * Real.log (k / μlb)) := by rw [heq]

end ThreeMajority
