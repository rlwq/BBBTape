import Bf.Tape

namespace Bf

inductive Program where
  | nil
  | left (rest : Program)
  | right (rest : Program)
  | flip (rest : Program)
  | loop (body rest : Program)
  deriving DecidableEq, Repr

namespace Program

def append : Program → Program → Program
  | nil,      q => q
  | left p,   q => left (p.append q)
  | right p,  q => right (p.append q)
  | flip p,   q => flip (p.append q)
  | loop b p, q => loop b (p.append q)

instance : Append Program := ⟨append⟩

@[simp] theorem nil_append (q : Program) : nil ++ q = q := rfl
@[simp] theorem left_append (p q : Program) : left p ++ q = left (p ++ q) := rfl
@[simp] theorem right_append (p q : Program) : right p ++ q = right (p ++ q) := rfl
@[simp] theorem flip_append (p q : Program) : flip p ++ q = flip (p ++ q) := rfl
@[simp] theorem loop_append (b p q : Program) : loop b p ++ q = loop b (p ++ q) := rfl

theorem append_assoc (p q r : Program) : p ++ q ++ r = p ++ (q ++ r) := by
  induction p with
  | nil => rfl
  | left p ih | right p ih | flip p ih => simp [ih]
  | loop b p _ ih => simp [ih]

def size : Program → Nat
  | nil      => 0
  | left p   => p.size + 1
  | right p  => p.size + 1
  | flip p   => p.size + 1
  | loop b p => b.size + p.size + 2

def toString : Program → String
  | nil       => ""
  | left p    => "<" ++ p.toString
  | right p   => ">" ++ p.toString
  | flip p    => "*" ++ p.toString
  | loop b p  => "[" ++ b.toString ++ "]" ++ p.toString

instance : ToString Program := ⟨toString⟩

theorem length_toString (p : Program) : p.toString.length = p.size := by
  have : "<".length = 1
       ∧ ">".length = 1
       ∧ "*".length = 1
       ∧ "[".length = 1
       ∧ "]".length = 1
       := by decide
  induction p
    <;> simp [toString, size, String.length_append, *] <;> omega

def stars : Nat → Program
  | 0     => nil
  | n + 1 => flip (stars n)

@[simp] theorem size_stars (n : Nat) : (stars n).size = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [stars, size, ih]

def loopFree : Program → Bool
  | nil      => true
  | left p   => p.loopFree
  | right p  => p.loopFree
  | flip p   => p.loopFree
  | loop _ _ => false

theorem loopFree_stars (n : Nat) : (stars n).loopFree = true := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

end Program

end Bf
