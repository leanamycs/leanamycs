import RumorSpread.Prob

/-!
# Faithfulness of the transition-operator expectation

`expList α T F` was *defined* by recursion (average out the first draw, then
recurse).  This file proves it equals the textbook object: the uniform
average of `F` over **all** length-`T` sequences of draws, i.e. over the
product probability space `Fin T → α` of `T` i.i.d. uniform rounds.
-/

namespace RumorPush

open Finset

variable {α : Type*} [Fintype α]

lemma expList_eq_avg_ofFn (T : ℕ) (F : List α → ℝ) :
    expList α T F = avg (fun ω : Fin T → α => F (List.ofFn ω)) := by
  induction T generalizing F with
  | zero =>
    have h : (fun ω : Fin 0 → α => F (List.ofFn ω)) = fun _ => F [] := by
      funext ω
      simp
    rw [expList_zero, h, avg_const]
  | succ T ih =>
    rw [expList_succ]
    have h : (fun a : α => expList α T fun l => F (a :: l))
        = fun a : α => avg (fun ω : Fin T → α => F (a :: List.ofFn ω)) := by
      funext a
      rw [ih]
    rw [h]
    rcases isEmpty_or_nonempty α with hα | hα
    · simp [avg]
    · -- Fubini: sum over `Fin (T+1) → α` as a double sum
      have hsum : ∑ ω : Fin (T + 1) → α, F (List.ofFn ω)
          = ∑ a : α, ∑ ω : Fin T → α, F (a :: List.ofFn ω) := by
        rw [← Equiv.sum_comp (Fin.consEquiv fun _ => α)
          (fun ω : Fin (T + 1) → α => F (List.ofFn ω)), Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun ω _ => ?_
        congr 1
        simp [Fin.consEquiv, List.ofFn_succ]
      have hcard : (Fintype.card (Fin (T + 1) → α) : ℝ)
          = (Fintype.card α : ℝ) * (Fintype.card (Fin T → α) : ℝ) := by
        rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_fin,
          Fintype.card_fin, pow_succ]
        push_cast
        ring
      have hc : (Fintype.card α : ℝ) ≠ 0 := ne_of_gt card_cast_pos
      have hcT : (Fintype.card (Fin T → α) : ℝ) ≠ 0 := ne_of_gt card_cast_pos
      unfold avg
      rw [hsum, hcard, ← Finset.sum_div, div_div, mul_comm]

end RumorPush
