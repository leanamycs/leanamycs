import ThreeMajority.Prob
import ThreeMajority.Model

/-!
# One-round exact drift

The cubic **majority map** `p(x) = 3x² - 2x³`: the exact probability that a
single agent adopts opinion `1` in one round, as a function of the current
fraction `x` of opinion-`1` agents. `avg_card_step` computes the exact
expected size of `step I r` as `n * p(|I|/n)`, via the algebraic identity
`maj(a,b,c) = ab+bc+ac-2abc` for `a,b,c ∈ {0,1}` (the majority-of-three
function, as a polynomial) plus the independence toolkit of `Prob.lean`.

`Y_maj` and `card_step_eq_sum` expose the underlying `{0,1}`-valued,
per-agent decomposition of `(step I r).card` as `∑ v, Y_maj I v (r v)`,
which is exactly the shape `Chernoff.lean`'s tail bounds need; `Growth.lean`
and `Saturation.lean` apply them directly to `Y_maj`.
-/

namespace ThreeMajority

open Finset

variable {n : ℕ}

/-- The real-valued membership indicator. -/
def ind (I : Finset (Fin n)) (x : Fin n) : ℝ := if x ∈ I then 1 else 0

lemma ind_eq_zero_or_one (I : Finset (Fin n)) (x : Fin n) : ind I x = 0 ∨ ind I x = 1 := by
  unfold ind; split_ifs <;> simp

lemma avg_ind (I : Finset (Fin n)) : avg (ind I) = (I.card : ℝ) / (Fintype.card (Fin n) : ℝ) := by
  unfold ind
  rw [avg_indicator]
  congr 2
  rw [show (univ.filter (· ∈ I)) = I from by ext x; simp]

/-- `avg (ind I) = |I|/n`, phrased so downstream files can talk about the
opinion-`1` fraction directly. -/
lemma avg_ind_eq (I : Finset (Fin n)) : avg (ind I) = (I.card : ℝ) / n := by
  rw [avg_ind]; simp

/-- **Majority-of-three as a polynomial**: for `a, b, c ∈ {0,1}`,
`𝟙[a+b+c ≥ 2] = ab+bc+ac-2abc`. -/
lemma majorityIndicator_eq (I : Finset (Fin n)) (s : Fin n × Fin n × Fin n) :
    (if 2 ≤ sampleCountOf I s then (1 : ℝ) else 0)
      = ind I s.1 * ind I s.2.1 + ind I s.2.1 * ind I s.2.2 + ind I s.1 * ind I s.2.2
          - 2 * (ind I s.1 * ind I s.2.1 * ind I s.2.2) := by
  unfold sampleCountOf ind
  by_cases h1 : s.1 ∈ I <;> by_cases h2 : s.2.1 ∈ I <;> by_cases h3 : s.2.2 ∈ I <;>
    simp [h1, h2, h3] <;> norm_num

lemma avg_ind_mul_fst_snd1 (I : Finset (Fin n)) [Nonempty (Fin n)] :
    avg (fun s : Fin n × Fin n × Fin n => ind I s.1 * ind I s.2.1) = avg (ind I) * avg (ind I) := by
  rw [show (fun s : Fin n × Fin n × Fin n => ind I s.1 * ind I s.2.1)
      = fun s : Fin n × (Fin n × Fin n) =>
          ind I s.1 * (fun q : Fin n × Fin n => ind I q.1) s.2 from rfl,
    avg_mul_prod (ind I) (fun q : Fin n × Fin n => ind I q.1), avg_fst_mul (ind I)]

lemma avg_ind_mul_snd1_snd2 (I : Finset (Fin n)) [Nonempty (Fin n)] :
    avg (fun s : Fin n × Fin n × Fin n => ind I s.2.1 * ind I s.2.2) = avg (ind I) * avg (ind I) := by
  rw [show (fun s : Fin n × Fin n × Fin n => ind I s.2.1 * ind I s.2.2)
      = fun s : Fin n × (Fin n × Fin n) =>
          (fun q : Fin n × Fin n => ind I q.1 * ind I q.2) s.2 from rfl,
    avg_snd_mul (fun q : Fin n × Fin n => ind I q.1 * ind I q.2),
    avg_mul_prod (ind I) (ind I)]

lemma avg_ind_mul_fst_snd2 (I : Finset (Fin n)) [Nonempty (Fin n)] :
    avg (fun s : Fin n × Fin n × Fin n => ind I s.1 * ind I s.2.2) = avg (ind I) * avg (ind I) := by
  rw [show (fun s : Fin n × Fin n × Fin n => ind I s.1 * ind I s.2.2)
      = fun s : Fin n × (Fin n × Fin n) =>
          ind I s.1 * (fun q : Fin n × Fin n => ind I q.2) s.2 from rfl,
    avg_mul_prod (ind I) (fun q : Fin n × Fin n => ind I q.2), avg_snd_mul (ind I)]

lemma avg_ind_mul_triple (I : Finset (Fin n)) [Nonempty (Fin n)] :
    avg (fun s : Fin n × Fin n × Fin n => ind I s.1 * ind I s.2.1 * ind I s.2.2)
      = avg (ind I) * avg (ind I) * avg (ind I) := by
  rw [show (fun s : Fin n × Fin n × Fin n => ind I s.1 * ind I s.2.1 * ind I s.2.2)
      = fun s : Fin n × (Fin n × Fin n) =>
          ind I s.1 * (fun q : Fin n × Fin n => ind I q.1 * ind I q.2) s.2 from
        funext fun s => (mul_assoc _ _ _),
    avg_mul_prod (ind I) (fun q : Fin n × Fin n => ind I q.1 * ind I q.2),
    avg_mul_prod (ind I) (ind I), mul_assoc]

/-- The per-agent `{0,1}` contribution: whether a majority of the sample
triple `s` lies in `I`. Independent of the agent index `v`; kept as a
function `Fin n → (Fin n × Fin n × Fin n) → ℝ` to match the shape
`Chernoff.lean`'s tail bounds expect. -/
def Y_maj (I : Finset (Fin n)) (_ : Fin n) (s : Fin n × Fin n × Fin n) : ℝ :=
  if 2 ≤ sampleCountOf I s then 1 else 0

lemma Y_maj_zero_one (I : Finset (Fin n)) (v : Fin n) (s : Fin n × Fin n × Fin n) :
    Y_maj I v s = 0 ∨ Y_maj I v s = 1 := by
  unfold Y_maj; split_ifs <;> simp

/-- `(step I r).card` decomposes as the sum, over agents `v`, of the
per-agent `{0,1}` contributions `Y_maj I v (r v)`. -/
lemma card_step_eq_sum (I : Finset (Fin n)) (r : Tgt3 n) :
    ((step I r).card : ℝ) = ∑ v : Fin n, Y_maj I v (r v) := by
  unfold Y_maj
  rw [show (step I r) = univ.filter (fun v => 2 ≤ sampleCountOf I (r v)) from rfl]
  rw [Finset.card_filter]
  push_cast
  rfl

lemma avg_Y_maj_eq (I : Finset (Fin n)) [Nonempty (Fin n)] (v : Fin n) :
    avg (Y_maj I v)
      = avg (ind I) * avg (ind I) * 3 - 2 * (avg (ind I) * avg (ind I) * avg (ind I)) := by
  unfold Y_maj
  rw [show (fun s : Fin n × Fin n × Fin n => if 2 ≤ sampleCountOf I s then (1 : ℝ) else 0)
      = fun s : Fin n × Fin n × Fin n =>
          ind I s.1 * ind I s.2.1 + ind I s.2.1 * ind I s.2.2 + ind I s.1 * ind I s.2.2
            - 2 * (ind I s.1 * ind I s.2.1 * ind I s.2.2)
      from funext (majorityIndicator_eq I)]
  rw [avg_sub, avg_add, avg_add, avg_ind_mul_fst_snd1, avg_ind_mul_snd1_snd2,
    avg_ind_mul_fst_snd2, avg_const_mul, avg_ind_mul_triple]
  ring

/-- The sum, over all `n` agents, of the average per-agent contribution:
`n · p(x)`, `p(x) = 3x² - 2x³`, `x = |I|/n`. -/
lemma sum_avg_Y_maj (hn : 1 ≤ n) (I : Finset (Fin n)) :
    ∑ v : Fin n, avg (Y_maj I v)
      = (n : ℝ) * (3 * (avg (ind I))^2 - 2 * (avg (ind I))^3) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [show (fun v : Fin n => avg (Y_maj I v))
      = fun _ : Fin n =>
          avg (ind I) * avg (ind I) * 3 - 2 * (avg (ind I) * avg (ind I) * avg (ind I))
      from funext (avg_Y_maj_eq I)]
  rw [Finset.sum_const, card_univ, Fintype.card_fin]
  push_cast
  ring

/-- **Exact one-round drift**: the average number of agents adopting
opinion `1` after one round equals `n · p(x)`, `p(x) = 3x²-2x³`, `x = |I|/n`. -/
lemma avg_card_step (hn : 1 ≤ n) (I : Finset (Fin n)) :
    avg (fun r : Tgt3 n => ((step I r).card : ℝ))
      = (n : ℝ) * (3 * (avg (ind I))^2 - 2 * (avg (ind I))^3) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [show (fun r : Tgt3 n => ((step I r).card : ℝ))
      = fun r : Tgt3 n => ∑ v : Fin n, Y_maj I v (r v) from funext (card_step_eq_sum I)]
  rw [avg_sum]
  rw [show (fun v : Fin n => avg (fun r : Tgt3 n => Y_maj I v (r v)))
      = fun v : Fin n => avg (Y_maj I v)
      from funext fun v => avg_eval n v (Y_maj I v)]
  rw [sum_avg_Y_maj hn I]

/-- The complementary per-agent `{0,1}` contribution: whether agent `v`
adopts opinion `0` (dissents), i.e. `1 - Y_maj`. -/
def Y_dis (I : Finset (Fin n)) (v : Fin n) (s : Fin n × Fin n × Fin n) : ℝ :=
  1 - Y_maj I v s

lemma Y_dis_zero_one (I : Finset (Fin n)) (v : Fin n) (s : Fin n × Fin n × Fin n) :
    Y_dis I v s = 0 ∨ Y_dis I v s = 1 := by
  unfold Y_dis
  rcases Y_maj_zero_one I v s with h | h <;> rw [h] <;> norm_num

/-- `n - (step I r).card` decomposes as the sum, over agents `v`, of the
per-agent dissent contributions `Y_dis I v (r v)`. -/
lemma card_dissent_eq_sum (I : Finset (Fin n)) (r : Tgt3 n) :
    ((n : ℝ) - (step I r).card) = ∑ v : Fin n, Y_dis I v (r v) := by
  unfold Y_dis
  rw [Finset.sum_sub_distrib, Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
    ← card_step_eq_sum]

lemma sum_avg_Y_dis (hn : 1 ≤ n) (I : Finset (Fin n)) :
    ∑ v : Fin n, avg (Y_dis I v)
      = (n : ℝ) - (n : ℝ) * (3 * (avg (ind I))^2 - 2 * (avg (ind I))^3) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hpt : (fun v : Fin n => avg (Y_dis I v)) = fun v : Fin n => 1 - avg (Y_maj I v) := by
    funext v
    unfold Y_dis
    rw [show (fun s : Fin n × Fin n × Fin n => 1 - Y_maj I v s)
        = fun s : Fin n × Fin n × Fin n => (fun _ => (1:ℝ)) s - Y_maj I v s from rfl,
      avg_sub, avg_const]
  rw [hpt]
  rw [show (fun v : Fin n => (1:ℝ) - avg (Y_maj I v))
      = fun v : Fin n => (fun _ : Fin n => (1:ℝ)) v - (fun v => avg (Y_maj I v)) v from rfl]
  rw [Finset.sum_sub_distrib, Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
    sum_avg_Y_maj hn I]

end ThreeMajority
