import RumorSpread.Bounds
import RumorSpread.Model
import RumorSpread.Prob

/-!
# One-round estimates

The only place in the development where a probability is *computed* rather
than estimated: for `u ∉ I`, the probability that `u` is not contacted in one
round is exactly `(1 - 1/(n-1)) ^ |I|` (`avg_not_contacted`), by counting
round configurations coordinate-by-coordinate.

From it we derive the three estimates of Section 4 of the paper:

* `avg_card_step` — the exact expected size of `step I r`;
* `prob_goodRound` — a good round has probability `≥ 1/8`
  (expected growth + reverse Markov);
* `avg_uninformed_le` — above half, the expected number of uninformed
  nodes contracts by `2/3`.
-/

namespace RumorPush

open Finset

variable {n : ℕ}

lemma card_tgt (n : ℕ) : Fintype.card (Tgt n) = (n - 1) ^ n := by
  rw [show Fintype.card (Tgt n)
      = Fintype.card (∀ v : Fin n, {u : Fin n // u ≠ v}) from rfl,
    Fintype.card_pi]
  have h : ∀ v : Fin n, Fintype.card {u : Fin n // u ≠ v} = n - 1 := fun v => by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, Fintype.card_fin]
  simp [h]

/-- The configurations avoiding `u` on all of `I` form a product of subtypes. -/
private def notContactedEquiv (I : Finset (Fin n)) (u : Fin n) :
    {r : Tgt n // ∀ v ∈ I, ((r v) : Fin n) ≠ u}
      ≃ ∀ v : Fin n, {x : Fin n // x ≠ v ∧ (v ∈ I → x ≠ u)} where
  toFun r v := ⟨((r.1 v) : Fin n), (r.1 v).2, fun hv => r.2 v hv⟩
  invFun f := ⟨fun v => ⟨(f v).1, (f v).2.1⟩, fun v hv => (f v).2.2 hv⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma card_subtype_ne_ne {v u : Fin n} (hvu : v ≠ u) :
    Fintype.card {x : Fin n // x ≠ v ∧ x ≠ u} = n - 2 := by
  rw [Fintype.card_subtype]
  have h : (univ.filter fun x : Fin n => x ≠ v ∧ x ≠ u) = univ \ {v, u} := by
    ext x
    simp [not_or]
  rw [h, card_sdiff, inter_univ, card_univ, Fintype.card_fin, card_pair hvu]

lemma card_filter_not_contacted (I : Finset (Fin n)) (u : Fin n) (hu : u ∉ I) :
    (univ.filter fun r : Tgt n => ∀ v ∈ I, ((r v) : Fin n) ≠ u).card
      = (n - 2) ^ I.card * (n - 1) ^ (n - I.card) := by
  rw [← Fintype.card_subtype, Fintype.card_congr (notContactedEquiv I u),
    Fintype.card_pi]
  have hval : ∀ v : Fin n,
      Fintype.card {x : Fin n // x ≠ v ∧ (v ∈ I → x ≠ u)}
        = if v ∈ I then n - 2 else n - 1 := by
    intro v
    by_cases hv : v ∈ I
    · rw [if_pos hv]
      have e : {x : Fin n // x ≠ v ∧ (v ∈ I → x ≠ u)}
          ≃ {x : Fin n // x ≠ v ∧ x ≠ u} :=
        Equiv.subtypeEquivRight fun x => by simp [hv]
      rw [Fintype.card_congr e]
      exact card_subtype_ne_ne fun h => hu (h ▸ hv)
    · rw [if_neg hv]
      have e : {x : Fin n // x ≠ v ∧ (v ∈ I → x ≠ u)}
          ≃ {x : Fin n // x ≠ v} :=
        Equiv.subtypeEquivRight fun x => by simp [hv]
      rw [Fintype.card_congr e, Fintype.card_subtype_compl,
        Fintype.card_subtype_eq, Fintype.card_fin]
  calc ∏ v : Fin n, Fintype.card {x : Fin n // x ≠ v ∧ (v ∈ I → x ≠ u)}
      = ∏ v : Fin n, (if v ∈ I then n - 2 else n - 1) :=
        Finset.prod_congr rfl fun v _ => hval v
    _ = (∏ _v ∈ univ.filter (· ∈ I), (n - 2))
          * ∏ _v ∈ univ.filter (fun v => ¬ v ∈ I), (n - 1) :=
        Finset.prod_ite _ _
    _ = (n - 2) ^ I.card * (n - 1) ^ (n - I.card) := by
        rw [Finset.prod_const, Finset.prod_const, filter_mem_eq_inter,
          univ_inter, Finset.filter_not, filter_mem_eq_inter, univ_inter,
          ← compl_eq_univ_sdiff, card_compl, Fintype.card_fin]

/-- **Contact probability**: a fixed uninformed node is missed by all pushes
with probability exactly `(1 - 1/(n-1)) ^ |I|`. -/
lemma avg_not_contacted (hn : 2 ≤ n) (I : Finset (Fin n)) (u : Fin n)
    (hu : u ∉ I) :
    avg (fun r : Tgt n => if u ∈ step I r then (0 : ℝ) else 1)
      = (1 - 1 / ((n : ℝ) - 1)) ^ I.card := by
  have hcard : I.card ≤ n := by
    simpa using card_le_card (subset_univ I)
  have hind : ∀ r : Tgt n, (if u ∈ step I r then (0 : ℝ) else 1)
      = (if ∀ v ∈ I, ((r v) : Fin n) ≠ u then (1 : ℝ) else 0) := by
    intro r
    by_cases h : u ∈ step I r
    · rw [if_pos h, if_neg]
      rw [mem_step] at h
      rcases h with h | ⟨v, hv, hvu⟩
      · exact absurd h hu
      · push_neg
        exact ⟨v, hv, hvu⟩
    · rw [if_neg h, if_pos]
      intro v hv hvu
      exact h (mem_step.2 (Or.inr ⟨v, hv, hvu⟩))
  rw [show (fun r : Tgt n => if u ∈ step I r then (0 : ℝ) else 1)
      = fun r : Tgt n => if ∀ v ∈ I, ((r v) : Fin n) ≠ u then (1 : ℝ) else 0
      from funext hind]
  rw [avg_indicator, card_filter_not_contacted I u hu, card_tgt]
  -- now pure real arithmetic with casts
  have hn1 : (1 : ℝ) ≤ (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hne : ((n : ℝ) - 1) ≠ 0 := by linarith
  have hc2 : ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := by
    have : (2 : ℕ) ≤ n := hn
    push_cast [Nat.cast_sub this]
    ring
  have hc1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    have : (1 : ℕ) ≤ n := le_trans (by norm_num) hn
    push_cast [Nat.cast_sub this]
    ring
  push_cast [hc2, hc1]
  have hsplit : ((n : ℝ) - 1) ^ n
      = ((n : ℝ) - 1) ^ I.card * ((n : ℝ) - 1) ^ (n - I.card) := by
    rw [← pow_add, Nat.add_sub_cancel' hcard]
  rw [hsplit]
  have hpow_ne : ((n : ℝ) - 1) ^ (n - I.card) ≠ 0 := pow_ne_zero _ hne
  rw [mul_div_mul_right _ _ hpow_ne]
  have hx : 1 - 1 / ((n : ℝ) - 1) = ((n : ℝ) - 2) / ((n : ℝ) - 1) := by
    field_simp
    ring
  rw [hx, div_pow]

/-- **Expected one-round growth** (exact formula). -/
lemma avg_card_step (hn : 2 ≤ n) (I : Finset (Fin n)) :
    avg (fun r : Tgt n => ((step I r).card : ℝ))
      = I.card + ((n : ℝ) - I.card)
          * (1 - (1 - 1 / ((n : ℝ) - 1)) ^ I.card) := by
  haveI := tgt_nonempty hn
  have hpt : ∀ r : Tgt n, ((step I r).card : ℝ)
      = I.card + ∑ u ∈ Iᶜ, (if u ∈ step I r then (1 : ℝ) else 0) := by
    intro r
    have hsplit : (step I r \ I).card + I.card = (step I r).card :=
      card_sdiff_add_card_eq_card (subset_step I r)
    have hfilter : step I r \ I = Iᶜ.filter (· ∈ step I r) := by
      ext u
      simp [mem_sdiff, and_comm]
    have hsum : ∑ u ∈ Iᶜ, (if u ∈ step I r then (1 : ℝ) else 0)
        = ((Iᶜ.filter (· ∈ step I r)).card : ℝ) := by
      rw [sum_boole]
    rw [hsum, ← hfilter]
    push_cast [← hsplit]
    ring
  rw [show (fun r : Tgt n => ((step I r).card : ℝ))
      = fun r : Tgt n =>
          (I.card : ℝ) + ∑ u ∈ Iᶜ, (if u ∈ step I r then (1 : ℝ) else 0)
      from funext hpt]
  rw [avg_add, avg_const, avg_sum]
  have hper : ∀ u ∈ Iᶜ,
      avg (fun r : Tgt n => if u ∈ step I r then (1 : ℝ) else 0)
        = 1 - (1 - 1 / ((n : ℝ) - 1)) ^ I.card := by
    intro u hu
    have hu' : u ∉ I := mem_compl.1 hu
    have hpt' : ∀ r : Tgt n, (if u ∈ step I r then (1 : ℝ) else 0)
        = 1 - (if u ∈ step I r then (0 : ℝ) else 1) := by
      intro r
      by_cases h : u ∈ step I r <;> simp [h]
    rw [show (fun r : Tgt n => if u ∈ step I r then (1 : ℝ) else 0)
        = fun r : Tgt n => (1 : ℝ) - (if u ∈ step I r then (0 : ℝ) else 1)
        from funext hpt']
    rw [show (fun r : Tgt n => (1 : ℝ) - (if u ∈ step I r then (0 : ℝ) else 1))
        = fun r : Tgt n =>
            (fun _ : Tgt n => (1 : ℝ)) r - (fun r : Tgt n =>
              (if u ∈ step I r then (0 : ℝ) else 1)) r from rfl]
    rw [avg_sub, avg_const, avg_not_contacted hn I u hu']
  rw [Finset.sum_congr rfl hper, Finset.sum_const, card_compl, Fintype.card_fin,
    nsmul_eq_mul]
  have hcard : I.card ≤ n := by simpa using card_le_card (subset_univ I)
  have : ((n - I.card : ℕ) : ℝ) = (n : ℝ) - I.card := by
    push_cast [Nat.cast_sub hcard]
    ring
  rw [this]

/-- **A good round has probability at least `1/8`** (reverse Markov). -/
lemma prob_goodRound (hn : 2 ≤ n) (I : Finset (Fin n)) (hI : I.Nonempty) :
    (1 : ℝ) / 8 ≤ avg (fun r : Tgt n => if goodRound I r then (1 : ℝ) else 0) := by
  haveI := tgt_nonempty hn
  by_cases hbig : n < 2 * I.card
  · rw [show (fun r : Tgt n => if goodRound I r then (1 : ℝ) else 0)
        = fun _ : Tgt n => (1 : ℝ)
        from funext fun r => if_pos (Or.inr hbig)]
    rw [avg_const]
    norm_num
  · push_neg at hbig
    -- pointwise reverse Markov: |step I r| ≤ 9m/8 + m·1[good]
    have hpt : ∀ r : Tgt n, ((step I r).card : ℝ)
        ≤ 9 * I.card / 8 + I.card * (if goodRound I r then (1 : ℝ) else 0) := by
      intro r
      by_cases hg : goodRound I r
      · rw [if_pos hg]
        have h2 : ((step I r).card : ℝ) ≤ 2 * I.card := by
          exact_mod_cast card_step_le I r
        linarith
      · rw [if_neg hg]
        have h9 : ¬ 9 * I.card ≤ 8 * (step I r).card := fun h => hg (Or.inl h)
        push_neg at h9
        have : (8 : ℝ) * (step I r).card < 9 * I.card := by exact_mod_cast h9
        linarith
    have havg := avg_le_avg hpt
    rw [show (fun r : Tgt n => 9 * (I.card : ℝ) / 8
          + I.card * (if goodRound I r then (1 : ℝ) else 0))
        = fun r : Tgt n => (fun _ : Tgt n => 9 * (I.card : ℝ) / 8) r
            + (fun r : Tgt n => (I.card : ℝ)
                * (if goodRound I r then (1 : ℝ) else 0)) r from rfl] at havg
    rw [avg_add, avg_const, avg_const_mul] at havg
    -- expected growth: m + m/4 ≤ E|step|
    have hgrow : (I.card : ℝ) + I.card / 4
        ≤ avg (fun r : Tgt n => ((step I r).card : ℝ)) := by
      rw [avg_card_step hn I]
      have hm1 : (1 : ℝ) ≤ (I.card : ℝ) := by exact_mod_cast hI.card_pos
      have hmn : (2 : ℝ) * I.card ≤ (n : ℝ) := by exact_mod_cast hbig
      have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      set m : ℝ := (I.card : ℝ) with hm
      set x : ℝ := 1 / ((n : ℝ) - 1) with hxdef
      have hn1 : (1 : ℝ) ≤ (n : ℝ) - 1 := by linarith
      have hx0 : 0 ≤ x := by positivity
      have hx1 : x ≤ 1 := by
        rw [hxdef]
        rw [div_le_one (by linarith)]
        linarith
      have hxmul : x * ((n : ℝ) - 1) = 1 := by
        rw [hxdef]
        field_simp
      have hmx : m * x ≤ 1 := by
        have hmn1 : m ≤ (n : ℝ) - 1 := by linarith
        calc m * x ≤ ((n : ℝ) - 1) * x := by
              apply mul_le_mul_of_nonneg_right hmn1 hx0
          _ = 1 := by rw [mul_comm]; exact hxmul
      have hkey := half_mul_le_one_sub_pow hx0 hx1 (m := I.card) hmx
      -- (n - m) * (1 - (1-x)^m) ≥ (n - m) * (m x / 2) ≥ m/4
      have hnm : (0 : ℝ) ≤ (n : ℝ) - m := by linarith
      have h1 : ((n : ℝ) - m) * (m * x / 2)
          ≤ ((n : ℝ) - m) * (1 - (1 - x) ^ I.card) :=
        mul_le_mul_of_nonneg_left hkey hnm
      have hnmx : (1 : ℝ) / 2 ≤ ((n : ℝ) - m) * x := by
        rw [hxdef, mul_one_div, le_div_iff₀ (by linarith : (0:ℝ) < (n:ℝ) - 1)]
        linarith
      have h2 : m / 4 ≤ ((n : ℝ) - m) * (m * x / 2) := by
        nlinarith [mul_le_mul_of_nonneg_right hnmx
          (by linarith : (0:ℝ) ≤ m / 2)]
      linarith
    have hm1 : (1 : ℝ) ≤ (I.card : ℝ) := by exact_mod_cast hI.card_pos
    set p := avg (fun r : Tgt n => if goodRound I r then (1 : ℝ) else 0)
    nlinarith

/-- **Contraction above one half**: once `|I| ≥ n/2`, the expected number of
uninformed nodes shrinks by a factor `2/3` in one round. -/
lemma avg_uninformed_le (hn : 2 ≤ n) (I : Finset (Fin n))
    (hhalf : n ≤ 2 * I.card) :
    avg (fun r : Tgt n => (n : ℝ) - (step I r).card)
      ≤ 2 / 3 * ((n : ℝ) - I.card) := by
  haveI := tgt_nonempty hn
  rw [show (fun r : Tgt n => (n : ℝ) - ((step I r).card : ℝ))
      = fun r : Tgt n => (fun _ : Tgt n => (n : ℝ)) r
          - (fun r : Tgt n => ((step I r).card : ℝ)) r from rfl]
  rw [avg_sub, avg_const, avg_card_step hn I]
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hmn : (n : ℝ) ≤ 2 * I.card := by exact_mod_cast hhalf
  have hcardn : I.card ≤ n := by simpa using card_le_card (subset_univ I)
  have hcard : (I.card : ℝ) ≤ n := by exact_mod_cast hcardn
  set m : ℝ := (I.card : ℝ) with hm
  set x : ℝ := 1 / ((n : ℝ) - 1) with hxdef
  have hn1 : (1 : ℝ) ≤ (n : ℝ) - 1 := by linarith
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1 := by
    rw [hxdef, div_le_one (by linarith)]
    linarith
  have hb := pow_one_sub_le_one_div hx0 hx1 I.card
  have hmx : (1 : ℝ) / 2 ≤ m * x := by
    rw [hxdef, mul_one_div, le_div_iff₀ (by linarith : (0:ℝ) < (n:ℝ) - 1)]
    linarith
  have hb23 : (1 - x) ^ I.card ≤ 2 / 3 := by
    have h32 : (3 : ℝ) / 2 ≤ 1 + m * x := by linarith
    have : 1 / (1 + m * x) ≤ 1 / (3 / 2) :=
      one_div_le_one_div_of_le (by norm_num) h32
    calc (1 - x) ^ I.card ≤ 1 / (1 + m * x) := by
          simpa [hm] using hb
      _ ≤ 1 / (3 / 2) := this
      _ = 2 / 3 := by norm_num
  have hnm : (0 : ℝ) ≤ (n : ℝ) - m := by linarith
  have : ((n : ℝ) - m) * (1 - x) ^ I.card ≤ ((n : ℝ) - m) * (2 / 3) :=
    mul_le_mul_of_nonneg_left hb23 hnm
  calc (n : ℝ) - (m + ((n : ℝ) - m) * (1 - (1 - x) ^ I.card))
      = ((n : ℝ) - m) * (1 - x) ^ I.card := by ring
    _ ≤ ((n : ℝ) - m) * (2 / 3) := this
    _ = 2 / 3 * ((n : ℝ) - m) := by ring

end RumorPush
