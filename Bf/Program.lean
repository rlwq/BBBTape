import Bf.Tape

namespace Bf

inductive Program where
  | nil
  | left (rest : Program)
  | right (rest : Program)
  | flip (rest : Program)
  | loop (body rest : Program)
  | hole (id size : Nat)
  deriving DecidableEq, Repr, Hashable

namespace Program

def append : Program → Program → Program
  | nil,      q => q
  | left p,   q => left (p.append q)
  | right p,  q => right (p.append q)
  | flip p,   q => flip (p.append q)
  | loop b p, q => loop b (p.append q)
  | hole i k, _ => hole i k

instance : Append Program := ⟨append⟩

@[simp] theorem nil_append (q : Program) : nil ++ q = q := rfl
@[simp] theorem left_append (p q : Program) : left p ++ q = left (p ++ q) := rfl
@[simp] theorem right_append (p q : Program) : right p ++ q = right (p ++ q) := rfl
@[simp] theorem flip_append (p q : Program) : flip p ++ q = flip (p ++ q) := rfl
@[simp] theorem loop_append (b p q : Program) : loop b p ++ q = loop b (p ++ q) := rfl
@[simp] theorem hole_append (i k : Nat) (q : Program) : hole i k ++ q = hole i k := rfl

theorem append_assoc (p q r : Program) : p ++ q ++ r = p ++ (q ++ r) := by
  induction p with
  | nil => rfl
  | left p ih | right p ih | flip p ih => simp [ih]
  | loop b p _ ih => simp [ih]
  | hole => rfl

def size : Program → Nat
  | nil      => 0
  | left p   => p.size + 1
  | right p  => p.size + 1
  | flip p   => p.size + 1
  | loop b p => b.size + p.size + 2
  | hole _ k => k

def toString : Program → String
  | nil       => ""
  | left p    => "<" ++ p.toString
  | right p   => ">" ++ p.toString
  | flip p    => "*" ++ p.toString
  | loop b p  => "[" ++ b.toString ++ "]" ++ p.toString
  | hole _ k  => String.ofList (List.replicate k '?')

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
  | hole _ _ => false

def isHole : Program → Bool
  | hole _ _ => true
  | _        => false

def Closed : Program → Prop
  | nil      => True
  | left p   => p.Closed
  | right p  => p.Closed
  | flip p   => p.Closed
  | loop b p => b.Closed ∧ p.Closed
  | hole _ _ => False

theorem closed_stars (n : Nat) : (stars n).Closed := by
  induction n with
  | zero => trivial
  | succ n ih => exact ih

theorem loopFree_stars (n : Nat) : (stars n).loopFree = true := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

end Program

end Bf
