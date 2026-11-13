namespace Bf

@[ext] structure Tape where
  cells : Int → Bool

namespace Tape

def blank : Tape := ⟨fun (_ : Int) => false⟩

def head (t : Tape) : Bool := t.cells 0

def flip (t : Tape) : Tape := ⟨fun (i : Int) => if i = 0 then !t.head else t.cells i⟩

def moveL (t : Tape) : Tape := ⟨fun (i : Int) => t.cells (i - 1)⟩

def moveR (t : Tape) : Tape := ⟨fun (i : Int) => t.cells (i + 1)⟩

end Tape

end Bf
