@[ext] structure Tape where
  cells : Int → Bool
  deriving Inhabited

namespace Tape

def blank : Tape := ⟨fun _ => false⟩

def head (t : Tape) : Bool := t.cells 0

def moveL (t : Tape) : Tape := ⟨fun i => t.cells (i - 1)⟩

def moveR (t : Tape) : Tape := ⟨fun i => t.cells (i + 1)⟩

def flip (t : Tape) : Tape := ⟨fun i => if i = 0 then !t.cells 0 else t.cells i⟩

end Tape

inductive Program where
  | nil
  | left  (after : Program)
  | right (after : Program)
  | flip  (after : Program)
  | loop  (body : Program) (after : Program)
  deriving BEq, DecidableEq, Repr, Inhabited

def Program.append : Program → Program → Program
  | .nil,          q => q
  | .left p,       q => .left (p.append q)
  | .right p,      q => .right (p.append q)
  | .flip p,       q => .flip (p.append q)
  | .loop body p,  q => .loop body (p.append q)

instance : Append Program := ⟨Program.append⟩

@[ext] structure Machine where
  tape    : Tape
  program : Program
  deriving Inhabited

def Machine.step : Machine → Machine
  | ⟨t, .nil⟩          => ⟨t, .nil⟩
  | ⟨t, .left p⟩       => ⟨t.moveL, p⟩
  | ⟨t, .right p⟩      => ⟨t.moveR, p⟩
  | ⟨t, .flip p⟩       => ⟨t.flip, p⟩
  | ⟨t, .loop body p⟩  =>
      if t.head then ⟨t, body ++ .loop body p⟩ else ⟨t, p⟩

def Machine.run : Nat → Machine → Machine
  | 0,     m => m
  | n + 1, m => run n m.step

def Machine.halted (m : Machine) : Prop := m.program = .nil

instance (m : Machine) : Decidable m.halted := by
  unfold Machine.halted; infer_instance

def Machine.halts (m : Machine) : Prop := ∃ n, (m.run n).halted

def Program.toMachine (p : Program) : Machine := ⟨.blank, p⟩

def Machine.haltsIn (m : Machine) (k : Nat) : Prop :=
  (m.run k).halted ∧ ∀ j < k, ¬ (m.run j).halted
