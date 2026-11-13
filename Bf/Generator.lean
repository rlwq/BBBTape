import Bf.Config

namespace Bf

structure Generator where
  gen   : Nat → List Program
  size  : ∀ {n : Nat} {q : Program}, q ∈ gen n → q.size = n
  cover : ∀ p : Program, ∃ q ∈ gen p.size, p.SameTime q

end Bf
