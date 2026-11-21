import Bf.Core.Decider

namespace Bf

namespace Trace

open scoped Program Machine

variable {T : Type} [Tape T]

/-- Extend the trace up to `limit` steps; return `halts` or `stuck` if execution ended earlier. -/
@[inline] def advance {q : Program} (limit : Nat) (tr : Trace T q) : Verdict T q :=
  let tr' := tr.extend limit
  match hp : tr'.last.machine.prog with
  | ε          => .halts (tr'.frames.size - 1) (tr'.haltsIn_last hp)
  | .gap _ _ _ =>
    match tr'.stuckGap? with
    | some g => .stuck g
    | none   => .unknown tr'
  | _          => .unknown tr'

end Trace

@[inline] def Decider.simulator {T : Type} [Tape T] (limit : Nat) : Decider T :=
  fun _ tr => tr.advance limit

end Bf
