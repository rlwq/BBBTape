import Bf.Decider

namespace Bf

def Decider.loopFree : Decider where
  run := fun (p : Program) => if p.loopFree then .halts p.size else .unknown
  sound := fun (p : Program) => by
    by_cases h : p.loopFree
    · simp only [h, ↓reduceIte]; exact Program.haltsIn_size_of_loopFree h _
    · simp only [h]; trivial

end Bf
