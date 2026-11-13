import Bf.Config

namespace Bf

inductive Cmd where
  | flip
  | left
  | right
  deriving DecidableEq, Repr

namespace Cmd

def prepend : Cmd → Program → Program
  | flip,  p => .flip p
  | left,  p => .left p
  | right, p => .right p

def app : Cmd → Tape → Tape
  | flip,  t => t.flip
  | left,  t => t.moveL
  | right, t => t.moveR

def rank : Cmd → Nat
  | flip  => 0
  | left  => 1
  | right => 2

end Cmd

abbrev Seg := List Cmd

namespace Seg

def prepend (s : Seg) (p : Program) : Program := s.foldr Cmd.prepend p

def lt (s s' : Seg) : Bool := decide (s.map Cmd.rank < s'.map Cmd.rank)

def apply : Seg → Tape → Tape
  | [],     t => t
  | c :: s, t => apply s (c.app t)

def disp : Seg → Int
  | []          => 0
  | .flip :: s  => disp s
  | .left :: s  => disp s - 1
  | .right :: s => disp s + 1

def par : Seg → Int → Bool
  | [],          _ => false
  | .flip :: s,  j => (decide (j = 0)).xor (par s j)
  | .left :: s,  j => par s (j + 1)
  | .right :: s, j => par s (j - 1)

theorem prepend_append (s : Seg) (p x : Program) : prepend s p ++ x = prepend s (p ++ x) := by
  induction s with
  | nil => rfl
  | cons c s ih => cases c <;> simp [prepend, Cmd.prepend] at * <;> exact ih

theorem size_prepend (s : Seg) (p : Program) : (prepend s p).size = s.length + p.size := by
  induction s with
  | nil => simp [prepend]
  | cons c s ih =>
    cases c <;> simp only [prepend, List.foldr, Cmd.prepend, Program.size] at * <;>
      simp only [List.length_cons] <;> omega

theorem steps_prepend (s : Seg) (t : Tape) (p : Program) :
    (Config.mk t (prepend s p)).steps s.length = some ⟨apply s t, p⟩ := by
  induction s generalizing t with
  | nil => rfl
  | cons c s ih => cases c <;> exact ih _

theorem disp_bound (s : Seg) : -(s.length : Int) ≤ disp s ∧ disp s ≤ s.length := by
  induction s with
  | nil => simp [disp]
  | cons c s ih => cases c <;> simp only [disp, List.length_cons] <;> omega

theorem par_eq_false (s : Seg) (j : Int) (h : (s.length : Int) < j ∨ j < -(s.length : Int)) :
    par s j = false := by
  induction s generalizing j with
  | nil => rfl
  | cons c s ih =>
    simp only [List.length_cons] at h
    cases c with
    | flip => simp only [par]; rw [ih j (by omega)]; simp; omega
    | left => exact ih _ (by omega)
    | right => exact ih _ (by omega)

theorem cells_apply (s : Seg) (t : Tape) (i : Int) :
    (apply s t).cells i = (t.cells (i + disp s)).xor (par s (i + disp s)) := by
  induction s generalizing t with
  | nil => simp [apply, disp, par]
  | cons c s ih =>
    cases c with
    | flip =>
      simp only [apply, Cmd.app, ih, disp, par, Tape.flip, Tape.head]
      by_cases h : i + disp s = 0
      · simp only [h, ↓reduceIte, decide_true]; cases t.cells 0 <;> cases par s 0 <;> rfl
      · simp [h]
    | left =>
      simp only [apply, Cmd.app, ih, disp, par, Tape.moveL]
      congr 2 <;> omega
    | right =>
      simp only [apply, Cmd.app, ih, disp, par, Tape.moveR]
      congr 2 <;> omega

def window (f : Int → Bool) (r : Nat) : List Bool :=
  (List.range (2 * r + 1)).map fun (k : Nat) => f ((k : Int) - r)

theorem eq_of_window {f g : Int → Bool} {r : Nat} (h : window f r = window g r)
    (i : Int) (hi : -(r : Int) ≤ i ∧ i ≤ r) : f i = g i := by
  have hk := List.map_inj_left.mp h (i + r).toNat (List.mem_range.mpr (by omega))
  rwa [Int.toNat_of_nonneg (by omega), Int.add_sub_cancel] at hk

def support (f : Int → Bool) (r : Nat) : List Int :=
  ((List.range (2 * r + 1)).map fun (k : Nat) => (k : Int) - r).filter f

def walk (p d : Int) (G : List Int) : Nat :=
  let lo : Int := G.foldl min (min p d)
  let hi : Int := G.foldl max (max p d)
  min ((p - lo).natAbs + (hi - lo).natAbs + (hi - d).natAbs)
      ((hi - p).natAbs + (hi - lo).natAbs + (d - lo).natAbs)

def feasible (p d : Int) (G : List Int) (m : Nat) : Bool :=
  let c : Nat := G.length + walk p d G
  c ≤ m && (m - c) % 2 == 0

def toggle (G : List Int) (x : Int) : List Int :=
  if x ∈ G then G.erase x else x :: G

def greedy (d : Int) : Nat → Int → List Int → Seg
  | 0,     _, _ => []
  | m + 1, p, G =>
    if feasible p d (toggle G p) m then .flip :: greedy d m p (toggle G p)
    else if feasible (p - 1) d G m then .left :: greedy d m (p - 1) G
    else .right :: greedy d m (p + 1) G

end Seg

namespace Program

def splitSeg : Program → Seg × Program
  | left p  => ((.left :: (splitSeg p).1), (splitSeg p).2)
  | right p => ((.right :: (splitSeg p).1), (splitSeg p).2)
  | flip p  => ((.flip :: (splitSeg p).1), (splitSeg p).2)
  | p       => ([], p)

theorem prepend_splitSeg (p : Program) : Seg.prepend (splitSeg p).1 (splitSeg p).2 = p := by
  induction p with
  | nil => rfl
  | loop => rfl
  | left p ih | right p ih | flip p ih =>
    simp only [splitSeg, Seg.prepend, List.foldr] at *
    rw [ih]; rfl

end Program

end Bf
