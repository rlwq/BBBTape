import Bf.Config

namespace Bf

def Reachable (n k : Nat) : Prop := ∃ p : Program, p.Closed ∧ p.size = n ∧ p.init.HaltsIn k

def IsBB (n s : Nat) : Prop := Reachable n s ∧ ∀ k : Nat, Reachable n k → k ≤ s

theorem IsBB.unique {n s s' : Nat} (h : IsBB n s) (h' : IsBB n s') : s = s' :=
  Nat.le_antisymm (h'.2 s h.1) (h.2 s' h'.1)

end Bf
