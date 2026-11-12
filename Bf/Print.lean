import Bf.Basic

def Program.toString : Program → String
  | .nil         => ""
  | .left p      => "<" ++ p.toString
  | .right p     => ">" ++ p.toString
  | .flip p      => "*" ++ p.toString
  | .loop body p => "[" ++ body.toString ++ "]" ++ p.toString

instance : ToString Program := ⟨Program.toString⟩

def Program.size : Program → Nat
  | .nil         => 0
  | .left p      => p.size + 1
  | .right p     => p.size + 1
  | .flip p      => p.size + 1
  | .loop body p => body.size + p.size + 2

theorem Program.length_toString (p : Program) : p.toString.length = p.size := by
  have : "<".length = 1 ∧ ">".length = 1 ∧ "*".length = 1 ∧ "[".length = 1 ∧ "]".length = 1 := by
    decide
  induction p <;> simp [toString, size, String.length_append, *] <;> omega

def Program.enumerate : Nat → List Program
  | 0     => [.nil]
  | n + 1 =>
    (enumerate n).flatMap (fun p => [.left p, .right p, .flip p]) ++
    (List.finRange n).flatMap fun ⟨k, _⟩ =>
      (enumerate k).flatMap fun body => (enumerate (n - 1 - k)).map (.loop body)
termination_by n => n
decreasing_by all_goals omega
