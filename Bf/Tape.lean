set_option linter.deprecated false

namespace Bf

def Cells.cons (b : Bool) (l : List Bool) : List Bool :=
  if l = [] ∧ b = false then [] else b :: l

theorem Cells.getLast_cons (b : Bool) (l : List Bool) (h : l.getLast? ≠ some false) :
    (Cells.cons b l).getLast? ≠ some false := by
  unfold Cells.cons
  split
  · simp
  · next hc =>
    cases l with
    | nil => cases b <;> simp_all
    | cons x xs => rw [List.getLast?_cons_cons]; exact h

theorem Cells.getLast_tail (l : List Bool) (h : l.getLast? ≠ some false) :
    l.tail.getLast? ≠ some false := by
  cases l with
  | nil => simp
  | cons x xs =>
    cases xs with
    | nil => simp
    | cons y ys => rw [List.getLast?_cons_cons] at h; exact h

theorem Cells.getD_cons (b : Bool) (l : List Bool) (n : Nat) :
    (Cells.cons b l).getD n false = (b :: l).getD n false := by
  unfold Cells.cons
  split
  · next h => obtain ⟨rfl, rfl⟩ := h; cases n <;> simp
  · rfl

theorem Cells.eq_nil (l : List Bool) (h : l.getLast? ≠ some false)
    (hz : ∀ n : Nat, l.getD n false = false) : l = [] := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    have hx : x = false := by simpa using hz 0
    have hxs : xs = [] := by
      apply ih
      · cases xs with
        | nil => simp
        | cons y ys => rw [List.getLast?_cons_cons] at h; exact h
      · intro n; simpa using hz (n + 1)
    subst hx hxs
    simp at h

theorem Cells.eq (l m : List Bool) (hl : l.getLast? ≠ some false) (hm : m.getLast? ≠ some false)
    (h : ∀ n : Nat, l.getD n false = m.getD n false) : l = m := by
  induction l generalizing m with
  | nil => exact (Cells.eq_nil m hm fun (n : Nat) => by rw [← h n]; simp).symm
  | cons x xs ih =>
    cases m with
    | nil => exact Cells.eq_nil _ hl fun (n : Nat) => by rw [h n]; simp
    | cons y ys =>
      have hxy : x = y := by simpa using h 0
      have hxs : xs = ys := by
        apply ih
        · exact Cells.getLast_tail (x :: xs) hl
        · exact Cells.getLast_tail (y :: ys) hm
        · intro n; simpa using h (n + 1)
      rw [hxy, hxs]

theorem Cells.getD_tail (l : List Bool) (n : Nat) : l.tail.getD n false = l.getD (n + 1) false := by
  cases l <;> simp

structure Tape where
  left  : List Bool
  head  : Bool
  right : List Bool
  wfL   : left.getLast? ≠ some false
  wfR   : right.getLast? ≠ some false

namespace Tape

def blank : Tape := ⟨[], false, [], by simp, by simp⟩

def flip (t : Tape) : Tape := ⟨t.left, !t.head, t.right, t.wfL, t.wfR⟩

def moveL (t : Tape) : Tape :=
  ⟨t.left.tail, t.left.headD false, Cells.cons t.head t.right,
    Cells.getLast_tail _ t.wfL, Cells.getLast_cons _ _ t.wfR⟩

def moveR (t : Tape) : Tape :=
  ⟨Cells.cons t.head t.left, t.right.headD false, t.right.tail,
    Cells.getLast_cons _ _ t.wfL, Cells.getLast_tail _ t.wfR⟩

def cells (t : Tape) (i : Int) : Bool :=
  if i = 0 then t.head
  else if 0 < i then t.right.getD (i.toNat - 1) false
  else t.left.getD ((-i).toNat - 1) false

theorem cells_zero (t : Tape) : t.cells 0 = t.head := rfl

theorem cells_blank (i : Int) : blank.cells i = false := by
  unfold cells blank
  split
  · rfl
  · split <;> simp

theorem cells_flip (t : Tape) (i : Int) :
    t.flip.cells i = if i = 0 then !t.cells 0 else t.cells i := by
  unfold cells flip
  by_cases h : i = 0 <;> simp [h]

theorem cells_moveR (t : Tape) (i : Int) : t.moveR.cells i = t.cells (i + 1) := by
  unfold cells moveR
  by_cases h0 : i = 0
  · subst h0
    simp only [↓reduceIte, Int.zero_add, Int.one_ne_zero, Int.zero_lt_one]
    cases t.right <;> rfl
  · rw [if_neg h0]
    by_cases hp : 0 < i
    · rw [if_pos hp, if_neg (by omega), if_pos (by omega)]
      rw [show (i + 1).toNat - 1 = (i.toNat - 1) + 1 by omega]
      exact Cells.getD_tail _ _
    · rw [if_neg hp, Cells.getD_cons]
      by_cases hm : i = -1
      · subst hm; simp
      · rw [if_neg (by omega), if_neg (by omega)]
        rw [show (-i).toNat - 1 = ((-(i + 1)).toNat - 1) + 1 by omega]
        simp

theorem cells_moveL (t : Tape) (i : Int) : t.moveL.cells i = t.cells (i - 1) := by
  unfold cells moveL
  by_cases h0 : i = 0
  · subst h0
    simp only [↓reduceIte]
    rw [if_neg (by omega), if_neg (by omega)]
    cases t.left <;> rfl
  · rw [if_neg h0]
    by_cases hp : 0 < i
    · rw [if_pos hp, Cells.getD_cons]
      by_cases h1 : i = 1
      · subst h1; simp
      · rw [if_neg (by omega), if_pos (by omega)]
        rw [show i.toNat - 1 = ((i - 1).toNat - 1) + 1 by omega]
        simp
    · rw [if_neg hp, if_neg (by omega), if_neg (by omega)]
      rw [show (-(i - 1)).toNat - 1 = ((-i).toNat - 1) + 1 by omega]
      exact Cells.getD_tail _ _

@[ext] theorem ext {t u : Tape} (h : ∀ i : Int, t.cells i = u.cells i) : t = u := by
  obtain ⟨l, x, r, hl, hr⟩ := t
  obtain ⟨l', x', r', hl', hr'⟩ := u
  have hx : x = x' := h 0
  have hrr : r = r' := Cells.eq r r' hr hr' fun (n : Nat) => by
    have := h ((n : Int) + 1)
    unfold cells at this
    simpa [show ((n : Int) + 1) ≠ 0 by omega, show (0 : Int) < (n : Int) + 1 by omega] using this
  have hll : l = l' := Cells.eq l l' hl hl' fun (n : Nat) => by
    have := h (-((n : Int) + 1))
    unfold cells at this
    simpa [show -((n : Int) + 1) ≠ 0 by omega, show ¬ ((0 : Int) < -((n : Int) + 1)) by omega,
      show ¬ ((n : Int) + 1 < 0) by omega] using this
  subst hx hrr hll
  rfl

end Tape

end Bf
