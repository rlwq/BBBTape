import Bf.Core.Machine

namespace Bf

open scoped Program Machine

abbrev ℒ (n : Nat) := { p : Program // p° ∧ ‖p‖ = n }

instance {n : Nat} : Executable (ℒ n) where
  HaltsIn  p k := p.val ⇓ k
  Diverges p   := p.val⇑

structure IsBB (n v : Nat) : Prop where
  upper : ∀ (p : ℒ n) (k : Nat), p ⇓ k → k ≤ v
  lower : ∃ (p : ℒ n),           p ⇓ v

end Bf
