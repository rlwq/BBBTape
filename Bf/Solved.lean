import Bf.Decider

namespace Bf

structure Solved where
  prog    : Program
  verdict : Verdict
  correct : verdict.Correct prog

def Solved.decider (ms : List Solved) : Decider where
  run := fun (p : Program) =>
    match ms.find? (fun (m : Solved) => m.prog == p) with
    | some m => m.verdict
    | none   => .unknown
  sound := fun (p : Program) => by
    split
    · next m hm =>
      have hb : (m.prog == p) = true := List.find?_some (p := fun (m : Solved) => m.prog == p) hm
      have hp : m.prog = p := beq_iff_eq.mp hb
      exact hp ▸ m.correct
    · trivial

end Bf
