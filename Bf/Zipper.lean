import Bf.Tape

namespace Bf

structure Zipper where
  left  : List Bool
  head  : Bool
  right : List Bool

namespace Zipper

def blank : Zipper := ⟨[], false, []⟩

def flip (t : Zipper) : Zipper := ⟨t.left, !t.head, t.right⟩

def moveL (t : Zipper) : Zipper := ⟨t.left.tail, t.left.headD false, t.head :: t.right⟩

def moveR (t : Zipper) : Zipper := ⟨t.head :: t.left, t.right.headD false, t.right.tail⟩

@[inline] def cells (t : Zipper) : Int → Bool
  | .ofNat 0       => t.head
  | .ofNat (n + 1) => t.right.getD n false
  | .negSucc n     => t.left.getD n false

theorem getD_tail (l : List Bool) (n : Nat) : l.tail.getD n false = l.getD (n + 1) false := by
  cases l <;> simp

theorem headD_eq_getD (l : List Bool) : l.headD false = l.getD 0 false := by
  cases l <;> rfl

theorem cells_blank (i : Int) : blank.cells i = false := by
  cases i with
  | ofNat n => cases n <;> simp [blank, cells]
  | negSucc n => simp [blank, cells]

theorem cells_flip (t : Zipper) (i : Int) :
    t.flip.cells i = if i = 0 then !t.cells 0 else t.cells i := by
  cases i with
  | ofNat n =>
    cases n with
    | zero => rfl
    | succ n =>
      simp [flip, cells]
      intro h; omega
  | negSucc n => simp [flip, cells]

theorem cells_moveR (t : Zipper) (i : Int) : t.moveR.cells i = t.cells (i + 1) := by
  cases i with
  | ofNat n =>
    cases n with
    | zero => exact headD_eq_getD t.right
    | succ n => exact getD_tail t.right n
  | negSucc n =>
    cases n with
    | zero => rfl
    | succ n => rfl

theorem cells_moveL (t : Zipper) (i : Int) : t.moveL.cells i = t.cells (i - 1) := by
  cases i with
  | ofNat n =>
    cases n with
    | zero => exact headD_eq_getD t.left
    | succ n =>
      cases n with
      | zero => rfl
      | succ n =>
        rw [show Int.ofNat (n + 1 + 1) - 1 = Int.ofNat (n + 1) by simp [Int.ofNat_eq_natCast]]
        rfl
  | negSucc n => exact getD_tail t.left n

@[inline] instance : Tape Zipper where
  cells       := cells
  blank       := blank
  flip        := flip
  moveL       := moveL
  moveR       := moveR
  cells_blank := cells_blank
  cells_flip  := cells_flip
  cells_moveL := cells_moveL
  cells_moveR := cells_moveR

end Zipper

end Bf
