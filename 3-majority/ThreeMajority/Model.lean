import Mathlib

/-!
# The 3-majority opinion-dynamics process on the complete graph

* `Tgt3 n` — a round configuration: every agent draws an ordered triple of
  samples, independently and uniformly, *with* replacement (an agent may
  sample itself, and may sample the same agent twice — harmless, since a
  majority of three Boolean values always exists, with no ties).
* `step I r` — one round: every agent adopts the majority opinion among its
  three samples' current membership in the opinion-`1` set `I`.
* `run I l` — the opinion-`1` set after consuming the list `l` of rounds.
* `step_mono` — the *monotone coupling*: for a fixed round `r`, `I ⊆ I'`
  implies `step I r ⊆ step I' r`. Unlike the push protocol's informed set,
  `step` is *not* monotone in the round index (an unlucky round can shrink
  `step I r` below `I`), but it *is* monotone in `I` itself for a fixed `r`.
  This is the single structural fact that lets every tail bound below be
  proved for a *reference* set of a specific size and then transported to
  an arbitrary set that is merely `⊆` or `⊇` that reference — replacing the
  martingale/optional-stopping machinery that a non-monotone process would
  otherwise need.
-/

namespace ThreeMajority

open Finset

/-- A round configuration: every agent draws an ordered triple of samples,
independently and uniformly, with replacement. -/
def Tgt3 (n : ℕ) := Fin n → Fin n × Fin n × Fin n

instance (n : ℕ) : Fintype (Tgt3 n) :=
  inferInstanceAs (Fintype (Fin n → Fin n × Fin n × Fin n))

instance (n : ℕ) : DecidableEq (Tgt3 n) :=
  inferInstanceAs (DecidableEq (Fin n → Fin n × Fin n × Fin n))

lemma tgt3_nonempty {n : ℕ} (hn : 1 ≤ n) : Nonempty (Tgt3 n) :=
  ⟨fun _ => (⟨0, hn⟩, ⟨0, hn⟩, ⟨0, hn⟩)⟩

variable {n : ℕ}

/-- The number (`0`, `1`, `2`, or `3`) of a sample triple `s` that currently
lie in `I`. -/
def sampleCountOf (I : Finset (Fin n)) (s : Fin n × Fin n × Fin n) : ℕ :=
  (if s.1 ∈ I then 1 else 0) + (if s.2.1 ∈ I then 1 else 0) + (if s.2.2 ∈ I then 1 else 0)

/-- The number (`0`, `1`, `2`, or `3`) of agent `v`'s three samples, under
round `r`, that currently lie in `I`. -/
def sampleCount (I : Finset (Fin n)) (r : Tgt3 n) (v : Fin n) : ℕ :=
  sampleCountOf I (r v)

/-- One round of the 3-majority process: every agent adopts the majority
opinion among its three samples. -/
def step (I : Finset (Fin n)) (r : Tgt3 n) : Finset (Fin n) :=
  univ.filter (fun v => 2 ≤ sampleCount I r v)

lemma mem_step {I : Finset (Fin n)} {r : Tgt3 n} {v : Fin n} :
    v ∈ step I r ↔ 2 ≤ sampleCount I r v := by
  simp [step]

private lemma ite_mem_mono {I I' : Finset (Fin n)} (h : I ⊆ I') {x : Fin n} :
    (if x ∈ I then (1 : ℕ) else 0) ≤ (if x ∈ I' then 1 else 0) := by
  split_ifs with ha hb hb
  · exact le_refl 1
  · exact absurd (h ha) hb
  · exact Nat.zero_le 1
  · exact le_refl 0

lemma sampleCount_mono {I I' : Finset (Fin n)} (h : I ⊆ I') (r : Tgt3 n) (v : Fin n) :
    sampleCount I r v ≤ sampleCount I' r v := by
  unfold sampleCount sampleCountOf
  have h1 := ite_mem_mono (x := (r v).1) h
  have h2 := ite_mem_mono (x := (r v).2.1) h
  have h3 := ite_mem_mono (x := (r v).2.2) h
  omega

/-- **Monotone coupling**: for a *fixed* round `r`, `step` is monotone in
the current opinion-`1` set. This is purely combinatorial (no probability
involved). -/
lemma step_mono {I I' : Finset (Fin n)} (h : I ⊆ I') (r : Tgt3 n) :
    step I r ⊆ step I' r := by
  intro v hv
  rw [mem_step] at hv ⊢
  exact hv.trans (sampleCount_mono h r v)

lemma card_step_le (I : Finset (Fin n)) (r : Tgt3 n) : (step I r).card ≤ n := by
  simpa using card_le_card (subset_univ (step I r))

/-- The opinion-`1` set after consuming a list of rounds. -/
def run (I : Finset (Fin n)) : List (Tgt3 n) → Finset (Fin n)
  | [] => I
  | r :: l => run (step I r) l

@[simp] lemma run_nil (I : Finset (Fin n)) : run I [] = I := rfl

@[simp] lemma run_cons (I : Finset (Fin n)) (r : Tgt3 n) (l : List (Tgt3 n)) :
    run I (r :: l) = run (step I r) l := rfl

lemma run_append (I : Finset (Fin n)) (l₁ l₂ : List (Tgt3 n)) :
    run I (l₁ ++ l₂) = run (run I l₁) l₂ := by
  induction l₁ generalizing I with
  | nil => simp
  | cons r l ih => simp [ih]

/-- **Monotone coupling, iterated over a whole trajectory.** -/
lemma run_mono {I I' : Finset (Fin n)} (h : I ⊆ I') (l : List (Tgt3 n)) :
    run I l ⊆ run I' l := by
  induction l generalizing I I' with
  | nil => simpa using h
  | cons r l ih => exact ih (step_mono h r)

end ThreeMajority
