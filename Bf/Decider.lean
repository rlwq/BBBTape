import Bf.Config
import Bf.Verdict

namespace Bf

def Verdict.Correct : Verdict → Program → Prop
  | .halts n,  p => p.init.HaltsIn n
  | .nonhalts, p => ¬ p.init.Halts
  | .unknown,  _ => True

@[ext] structure Decider where
  run   : Program → Verdict
  sound : ∀ p : Program, (run p).Correct p

namespace Decider

def unknown : Decider where
  run := fun (_ : Program) => .unknown
  sound := fun (_ : Program) => trivial

def orElse (d₁ d₂ : Decider) : Decider where
  run := fun (p : Program) => match d₁.run p with
    | .unknown => d₂.run p
    | v        => v
  sound := fun (p : Program) => by
    have h₁ := d₁.sound p
    cases hv : d₁.run p <;> simp only [hv] at h₁ ⊢ <;> first | exact h₁ | exact d₂.sound p

instance : OrElse Decider := ⟨fun (d₁ : Decider) (d₂ : Unit → Decider) => d₁.orElse (d₂ ())⟩

theorem unknown_orElse (d : Decider) : unknown.orElse d = d := rfl

theorem orElse_unknown (d : Decider) : d.orElse unknown = d := by
  ext p; simp only [orElse, unknown]; split <;> simp_all

theorem orElse_assoc (a b c : Decider) : (a.orElse b).orElse c = a.orElse (b.orElse c) := by
  ext p; simp only [orElse]; cases a.run p <;> rfl

def any (ds : List Decider) : Decider := ds.foldr orElse unknown

def summary (d : Decider) (ps : List Program) : Verdict := Verdict.summary (ps.map d.run)

theorem summary_halts {d : Decider} {ps : List Program} {s : Nat} (h : d.summary ps = .halts s) :
    (∃ p ∈ ps, p.init.HaltsIn s) ∧ ∀ p ∈ ps, ∀ k : Nat, p.init.HaltsIn k → k ≤ s := by
  unfold summary at h
  constructor
  · rcases Verdict.summary_eq_nonhalts_or_mem (ps.map d.run) with e | e
    · rw [h] at e; cases e
    · rw [h] at e
      obtain ⟨p, hp, hrun⟩ := List.mem_map.mp e
      have hsound := d.sound p
      rw [hrun] at hsound
      exact ⟨p, hp, hsound⟩
  · intro p hp k hk
    have hmem : d.run p ∈ ps.map d.run := List.mem_map.mpr ⟨p, hp, rfl⟩
    have hle := Verdict.sup_summary_of_mem hmem
    rw [h] at hle
    have hsound := d.sound p
    rcases Verdict.of_sup_halts hle with e | ⟨j, hj, e⟩
    · rw [e] at hsound
      exact absurd ⟨k, hk⟩ hsound
    · rw [e] at hsound
      rw [hk.unique hsound]
      exact hj

end Decider

end Bf
