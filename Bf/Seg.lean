import Std.Data.HashSet
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
      simp only [apply, Cmd.app, ih, disp, par, Tape.cells_flip]
      by_cases h : i + disp s = 0
      · simp only [h, ↓reduceIte, decide_true]; cases t.cells 0 <;> cases par s 0 <;> rfl
      · simp [h]
    | left =>
      simp only [apply, Cmd.app, ih, disp, par, Tape.cells_moveL]
      congr 2 <;> omega
    | right =>
      simp only [apply, Cmd.app, ih, disp, par, Tape.cells_moveR]
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
  | hole => rfl
  | left p ih | right p ih | flip p ih =>
    simp only [splitSeg, Seg.prepend, List.foldr] at *
    rw [ih]; rfl

end Program

namespace Seg

def eff (s : Seg) : Int × List Bool := (disp s, window (par s) s.length)

theorem apply_eq_of_eff {s s' : Seg} (hl : s.length = s'.length) (he : eff s = eff s')
    (t : Tape) : apply s t = apply s' t := by
  obtain ⟨hd, hw⟩ := Prod.mk.inj he
  rw [hl] at hw
  have hpar : ∀ j : Int, par s j = par s' j := by
    intro j
    by_cases hj : -(s'.length : Int) ≤ j ∧ j ≤ s'.length
    · exact eq_of_window hw j hj
    · rw [par_eq_false s j (by omega), par_eq_false s' j (by omega)]
  ext i
  rw [cells_apply, cells_apply, hd, hpar]

def canon (s : Seg) : Seg :=
  let w : Seg := greedy (disp s) s.length 0 (support (par s) s.length)
  if w.length = s.length ∧ eff w = eff s then w else s

theorem length_canon (s : Seg) : (canon s).length = s.length := by
  unfold canon; dsimp only; split
  · next h => exact h.1
  · rfl

theorem apply_canon (s : Seg) (t : Tape) : apply (canon s) t = apply s t := by
  unfold canon; dsimp only; split
  · next h => exact apply_eq_of_eff h.1 h.2 t
  · rfl

end Seg


deriving instance Hashable for Cmd

namespace Seg

def ofLength : Nat → List Seg
  | 0     => [[]]
  | L + 1 => (ofLength L).flatMap fun (s : Seg) => [.flip :: s, .left :: s, .right :: s]

theorem mem_ofLength (s : Seg) : s ∈ ofLength s.length := by
  induction s with
  | nil => simp [ofLength]
  | cons c s ih =>
    simp only [List.length_cons, ofLength, List.mem_flatMap]
    exact ⟨s, ih, by cases c <;> simp⟩

def dedup (xs : List Seg) : List Seg :=
  (xs.foldl (fun (m : Std.HashSet Seg) (x : Seg) => m.insert x) ∅).toList

theorem mem_dedup {xs : List Seg} {a : Seg} : a ∈ dedup xs ↔ a ∈ xs := by
  have h : ∀ (ys : List Seg) (m : Std.HashSet Seg),
      a ∈ ys.foldl (fun (m : Std.HashSet Seg) (x : Seg) => m.insert x) m ↔ a ∈ m ∨ a ∈ ys := by
    intro ys
    induction ys with
    | nil => intro m; simp
    | cons y ys ih =>
      intro m
      rw [List.foldl_cons, ih, Std.HashSet.mem_insert, beq_iff_eq, List.mem_cons]
      constructor
      · rintro ((rfl | h) | h)
        · exact .inr (.inl rfl)
        · exact .inl h
        · exact .inr (.inr h)
      · rintro (h | rfl | h)
        · exact .inl (.inr h)
        · exact .inl (.inl rfl)
        · exact .inr h
  unfold dedup
  rw [Std.HashSet.mem_toList, h]
  simp [Std.HashSet.not_mem_empty]

def mids (L : Nat) : List Seg := dedup ((ofLength L).map canon)

theorem canon_mem_mids (s : Seg) : canon s ∈ mids s.length :=
  mem_dedup.mpr (List.mem_map.mpr ⟨s, mem_ofLength s, rfl⟩)

theorem length_of_mem_ofLength {L : Nat} {s : Seg} (h : s ∈ ofLength L) : s.length = L := by
  induction L generalizing s with
  | zero => simp [ofLength] at h; simp [h]
  | succ L ih =>
    simp only [ofLength, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at h
    obtain ⟨t, ht, rfl | rfl | rfl⟩ := h <;> simp [ih ht]

theorem length_of_mem_mids {L : Nat} {s : Seg} (h : s ∈ mids L) : s.length = L := by
  simp only [mids, mem_dedup, List.mem_map] at h
  obtain ⟨t, ht, rfl⟩ := h
  rw [length_canon, length_of_mem_ofLength ht]

theorem prepend_replicate (n : Nat) : prepend (List.replicate n .flip) .nil = Program.stars n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [prepend, List.replicate, Cmd.prepend, Program.stars] at *; exact ih

end Seg

end Bf
