import Bf.Decider
import Bf.Expand

namespace Bf

open scoped Program Machine

def Bounded (B : Nat) (q : Program) : Prop :=
  ∀ (p : Program) (k : Nat), p° → p ⊑ q → p ⇓ k → k ≤ B

namespace Bounded

theorem of_halts {B t : Nat} {q : Program} :
    q ⇓ t → t ≤ B → Bounded B q := by
  intro hq ht p k _ hpq hk
  rw [Machine.HaltsIn.unique (hk SpecTape) (hpq.haltsIn hq SpecTape)]
  exact ht

theorem of_diverges {B : Nat} {q : Program} :
    q⇑ → Bounded B q := by
  intro hq p k _ hpq hk
  exact absurd ⟨k, hk SpecTape⟩ (Machine.not_halts_of_diverges (hpq.diverges hq SpecTape))

theorem of_expand {e : Expander} {B : Nat} {q : Program} (i : Fin q.numGaps) :
    (∀ c ∈ e.expand q i, Bounded B c) → Bounded B q := by
  intro hcs p k hp hpq hk
  obtain ⟨c, hc, p', hp', hp'c, heq⟩ := e.cover i hp hpq
  exact hcs c hc p' k hp' hp'c ((heq k).mp hk)

theorem upper {B n : Nat} :
    Bounded B (Program.gap? n) →
    ∀ (p : Program) (k : Nat), p° → ‖p‖ = n → p ⇓ k → k ≤ B := by
  intro h p k hp hn hk
  exact h p k hp (Program.refines_gap? hp hn) hk

end Bounded


/-- Settle `q` with the decider, expanding a gap whenever execution gets stuck on it.
Returns the partial programs that could not be bounded by `B`; an empty list means
every program refining `q` halts within `B` steps or never halts. -/
def search (e : Expander) (d : Decider) (B : Nat) (q : Program) : List Program :=
  match d.decide q with
  | .halts t  => if t ≤ B then [] else [q]
  | .diverges => []
  | .stuck i  =>
    if h : i < q.numGaps then
      (e.expand q ⟨i, h⟩).attach.flatMap fun c => search e d B c.1
    else [q]
  | .unknown  => [q]
termination_by q.gapSum
decreasing_by exact e.decreasing c.2

theorem search_bounded {e : Expander} {d : Decider} {B : Nat} (q : Program) :
    (∀ r ∈ search e d B q, Bounded B r) → Bounded B q := by
  intro h
  have hsound := d.sound q
  rw [search] at h
  cases hv : d.decide q with
  | halts t =>
    rw [hv] at h hsound
    simp only at h hsound
    by_cases ht : t ≤ B
    · exact Bounded.of_halts hsound ht
    · simp only [ht, ↓reduceIte] at h
      exact h q (List.mem_singleton_self _)
  | diverges =>
    rw [hv] at hsound
    exact Bounded.of_diverges hsound
  | stuck i =>
    rw [hv] at h
    simp only at h
    by_cases hi : i < q.numGaps
    · simp only [hi, ↓reduceDIte] at h
      refine Bounded.of_expand (e := e) ⟨i, hi⟩ fun c hc =>
        search_bounded (e := e) (d := d) c fun r hr => h r ?_
      exact List.mem_flatMap.mpr ⟨⟨c, hc⟩, List.mem_attach _ _, hr⟩
    · simp only [hi, ↓reduceDIte] at h
      exact h q (List.mem_singleton_self _)
  | unknown =>
    rw [hv] at h
    exact h q (List.mem_singleton_self _)
termination_by q.gapSum
decreasing_by exact e.decreasing hc

end Bf
