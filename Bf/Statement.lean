import Bf.Machine

namespace Bf

abbrev SpecTape : Type := Int → Bool

instance : Tape SpecTape where
  cells t i := t i
  blank _ := false
  flip t i := if i = 0 then !t 0 else t i
  moveL t i := t (i - 1)
  moveR t i := t (i + 1)
  cells_blank _ := rfl
  cells_flip _ _ := rfl
  cells_moveL _ _ := rfl
  cells_moveR _ _ := rfl

open scoped Program Machine

abbrev ℒ (n : Nat) := { p : Program // p° ∧ ‖p‖ = n }

instance {n : Nat} : Executable (ℒ n) where
  HaltsIn  p k := p.val ⇓ k
  Diverges p   := p.val⇑

structure IsBB (n v : Nat) : Prop where
  upper : ∀ (p : ℒ n) (k : Nat), p ⇓ k → k ≤ v
  lower : ∃ (p : ℒ n),           p ⇓ v

end Bf
