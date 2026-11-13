import Bf.Decider

namespace Bf

def Config.haltTime : Nat → Config → Option Nat
  | fuel, c => match c.step, fuel with
    | none,    _     => some 0
    | some _,  0     => none
    | some c', f + 1 => (haltTime f c').map (· + 1)

theorem Config.haltsIn_of_haltTime {fuel : Nat} {c : Config} {n : Nat}
    (h : haltTime fuel c = some n) : c.HaltsIn n := by
  induction fuel generalizing c n with
  | zero =>
    unfold haltTime at h
    cases hs : c.step with
    | none => simp [hs] at h; subst h; exact ⟨c, rfl, hs⟩
    | some c' => simp [hs] at h
  | succ f ih =>
    unfold haltTime at h
    cases hs : c.step with
    | none => simp [hs] at h; subst h; exact ⟨c, rfl, hs⟩
    | some c' =>
      simp [hs] at h
      obtain ⟨k, hk, rfl⟩ := h
      exact (haltsIn_succ hs).mpr (ih hk)

def Decider.simulator (fuel : Nat) : Decider where
  run := fun (p : Program) => match p.init.haltTime fuel with
    | some n => .halts n
    | none   => .unknown
  sound := fun (p : Program) => by
    cases h : p.init.haltTime fuel with
    | some n => exact Config.haltsIn_of_haltTime h
    | none   => trivial

end Bf
