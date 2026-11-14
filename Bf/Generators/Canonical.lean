import Std.Data.HashSet
import Bf.Generator
import Bf.Canons.Segments
import Bf.Canons.FirstSegment
import Bf.Canons.LastSegment
import Bf.Canons.DeadLoops

namespace Bf

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

def firsts (L : Nat) : List Seg := dedup ((mids L).map canonFirst)

theorem canon_mem_mids (s : Seg) : canon s ∈ mids s.length :=
  mem_dedup.mpr (List.mem_map.mpr ⟨s, mem_ofLength s, rfl⟩)

theorem canonFirst_mem_firsts (s : Seg) : canonFirst (canon s) ∈ firsts s.length :=
  mem_dedup.mpr (List.mem_map.mpr ⟨canon s, canon_mem_mids s, rfl⟩)

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

theorem length_of_mem_firsts {L : Nat} {s : Seg} (h : s ∈ firsts L) : s.length = L := by
  simp only [firsts, mem_dedup, List.mem_map] at h
  obtain ⟨t, ht, rfl⟩ := h
  rw [(canonFirst_spec t).1, length_of_mem_mids ht]

theorem canonFirst_nil : canonFirst [] = [] :=
  List.length_eq_zero_iff.mp (canonFirst_spec []).1

theorem prepend_replicate (n : Nat) : prepend (List.replicate n .flip) .nil = Program.stars n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [prepend, List.replicate, Cmd.prepend, Program.stars] at *; exact ih

end Seg

namespace Program

theorem loopFree_prepend_nil (s : Seg) : (Seg.prepend s nil).loopFree = true := by
  induction s with
  | nil => rfl
  | cons c s ih => cases c <;> exact ih

theorem loopFree_prepend_loop (s : Seg) (b q : Program) :
    (Seg.prepend s (loop b q)).loopFree = false := by
  induction s with
  | nil => rfl
  | cons c s ih => cases c <;> exact ih

theorem canonLast_prepend_nil (s : Seg) : canonLast (Seg.prepend s nil) = stars s.length := by
  unfold canonLast
  rw [ite_eq_left (loopFree_prepend_nil s), Seg.size_prepend]
  rfl

theorem canonLast_prepend_loop (s : Seg) (b q : Program) :
    canonLast (Seg.prepend s (loop b q)) = Seg.prepend s (loop b (canonLast q)) := by
  induction s with
  | nil =>
    show canonLast (loop b q) = loop b (canonLast q)
    rw [canonLast]
    simp [loopFree]
  | cons c s ih =>
    have hl := loopFree_prepend_loop s b q
    cases c with
    | flip =>
      show canonLast (Program.flip (Seg.prepend s (loop b q))) = Program.flip (Seg.prepend s (loop b (canonLast q)))
      rw [canonLast, ite_eq_right (by simp [loopFree, hl])]
      exact congrArg Program.flip ih
    | left =>
      show canonLast (Program.left (Seg.prepend s (loop b q))) = Program.left (Seg.prepend s (loop b (canonLast q)))
      rw [canonLast, ite_eq_right (by simp [loopFree, hl])]
      exact congrArg Program.left ih
    | right =>
      show canonLast (Program.right (Seg.prepend s (loop b q))) = Program.right (Seg.prepend s (loop b (canonLast q)))
      rw [canonLast, ite_eq_right (by simp [loopFree, hl])]
      exact congrArg Program.right ih

theorem splitSeg_prepend (s : Seg) (X : Program) (hX : X = nil ∨ ∃ b q, X = loop b q) :
    splitSeg (Seg.prepend s X) = (s, X) := by
  induction s with
  | nil => rcases hX with rfl | ⟨b, q, rfl⟩ <;> rfl
  | cons c s ih =>
    cases c <;> simp [Seg.prepend, Cmd.prepend, splitSeg] at ih ⊢ <;> simp [ih]

theorem canonFirstSeg_prepend_nil (s : Seg) :
    canonFirstSeg (Seg.prepend s nil) = Seg.prepend (Seg.canonFirst s) nil := by
  have h := splitSeg_prepend s nil (.inl rfl)
  cases s with
  | nil => simp [Seg.prepend, canonFirstSeg, canonHead, splitSeg, Seg.canonFirst_nil]
  | cons c s =>
    cases c <;>
    · simp only [Seg.prepend, List.foldr, Cmd.prepend, canonFirstSeg, canonHead] at h ⊢
      rw [h]

theorem canonFirstSeg_prepend_loop (s : Seg) (b q : Program) :
    canonFirstSeg (Seg.prepend s (loop b q)) =
      if s = [] then loop b (canonFirstSeg q) else Seg.prepend (Seg.canonFirst s) (loop b q) := by
  have h := splitSeg_prepend s (loop b q) (.inr ⟨b, q, rfl⟩)
  cases s with
  | nil => rfl
  | cons c s =>
    cases c <;>
    · simp only [Seg.prepend, List.foldr, Cmd.prepend, canonFirstSeg, canonHead, reduceCtorEq,
        ↓reduceIte] at h ⊢
      rw [h]

end Program

namespace Program

inductive Dead : DeadMode → Program → Prop
  | nil {m : DeadMode} : Dead m nil
  | left {m : DeadMode} {p : Program} : Dead .live p → Dead m (left p)
  | right {m : DeadMode} {p : Program} : Dead .live p → Dead m (right p)
  | flip {m : DeadMode} {p : Program} : Dead .live p → Dead m (flip p)
  | live {b p : Program} : Dead .live b → Dead .dead p → Dead .live (loop b p)
  | dead {S : Nat} {p : Program} : Dead .chain p → Dead .dead (loop (stars S) p)
  | chain {p : Program} : Dead .chain p → Dead .chain (loop nil p)

theorem dead_canonDead (m : DeadMode) (p : Program) : Dead m (canonDead m p) := by
  induction p generalizing m with
  | nil => cases m <;> exact .nil
  | left p ih => cases m <;> exact .left (ih .live)
  | right p ih => cases m <;> exact .right (ih .live)
  | flip p ih => cases m <;> exact .flip (ih .live)
  | loop b p ihb ih =>
    cases m
    · exact .live (ihb .live) (ih .dead)
    · exact .dead (ih .chain)
    · exact .chain (ih .chain)

end Program

namespace Generator.canonical

open Program

def eff (m : DeadMode) : Seg → DeadMode
  | []     => m
  | _ :: _ => .live

def next : DeadMode → DeadMode
  | .live  => .dead
  | .dead  => .chain
  | .chain => .chain

theorem eff_of_length (m : DeadMode) {s t : Seg} (h : s.length = t.length) : eff m s = eff m t := by
  cases s <;> cases t <;> simp_all [eff]

theorem eff_canon (m : DeadMode) (s : Seg) : eff m (Seg.canon s) = eff m s :=
  eff_of_length m (Seg.length_canon s)

theorem eff_canonFirst (m : DeadMode) (s : Seg) : eff m (Seg.canonFirst s) = eff m s :=
  eff_of_length m (Seg.canonFirst_spec s).1

theorem eff_reverse (m : DeadMode) (s : Seg) : eff m s.reverse = eff m s :=
  eff_of_length m (List.length_reverse)

theorem canon_nil : Seg.canon [] = [] :=
  List.length_eq_zero_iff.mp (Seg.length_canon [])

def pick (M : DeadMode) (a : Nat) (live : List Program) : List Program :=
  match M with
  | .live  => live
  | .dead  => [canonSegs [] (stars a)]
  | .chain => if a = 0 then [nil] else []

def body (m : DeadMode) (n : Nat) : List Program :=
    ((Seg.mids n).map fun (s : Seg) => Seg.prepend s nil) ++
    (List.range n).flatMap fun (L : Nat) => (Seg.mids L).flatMap fun (s : Seg) =>
      (List.range n).flatMap fun (a : Nat) => (List.range n).flatMap fun (b : Nat) =>
        if L + a + b + 2 = n then
          (pick (eff m s) a (body .live a)).flatMap fun (x : Program) =>
          (body (next (eff m s)) b).map fun (y : Program) => Seg.prepend s (loop x y)
        else []
termination_by n
decreasing_by all_goals omega

def top (seen : Bool) (m : DeadMode) (n : Nat) : List Program :=
    [stars n] ++
    (List.range n).flatMap fun (L : Nat) => (if seen then Seg.mids L else Seg.firsts L).flatMap
      fun (s : Seg) => (List.range n).flatMap fun (a : Nat) => (List.range n).flatMap fun (b : Nat) =>
        if L + a + b + 2 = n then
          (pick (eff m s) a (body .live a)).flatMap fun (x : Program) =>
          (top (seen || !s.isEmpty) (next (eff m s)) b).map fun (y : Program) =>
            Seg.prepend s (loop x y)
        else []
termination_by n
decreasing_by all_goals omega

def nf : Bool → Seg → Program → Program
  | _,    acc, nil      => stars acc.length
  | seen, acc, left p   => nf seen (.left :: acc) p
  | seen, acc, right p  => nf seen (.right :: acc) p
  | seen, acc, Program.flip p => nf seen (.flip :: acc) p
  | seen, acc, loop b p =>
    let s : Seg := if seen then Seg.canon acc.reverse else Seg.canonFirst (Seg.canon acc.reverse)
    Seg.prepend s (loop (canonSegs [] b) (nf (seen || !s.isEmpty) [] p))

theorem nf_true (acc : Seg) (p : Program) : nf true acc p = canonLast (canonSegs acc p) := by
  induction p generalizing acc with
  | nil =>
    simp only [nf, canonSegs, canonLast_prepend_nil, Seg.length_canon, List.length_reverse]
  | left p ih | right p ih | flip p ih => simp only [nf, canonSegs, ih]
  | loop b p _ ih =>
    simp only [nf, canonSegs, canonLast_prepend_loop, ↓reduceIte, Bool.true_or, ih]

theorem nf_false (acc : Seg) (p : Program) :
    nf false acc p = canonLast (canonFirstSeg (canonSegs acc p)) := by
  induction p generalizing acc with
  | nil =>
    simp only [nf, canonSegs, canonFirstSeg_prepend_nil, canonLast_prepend_nil,
      (Seg.canonFirst_spec _).1, Seg.length_canon, List.length_reverse]
  | left p ih | right p ih | flip p ih => simp only [nf, canonSegs, ih]
  | loop b p _ ih =>
    simp only [nf, canonSegs, canonFirstSeg_prepend_loop, Bool.false_or, Bool.false_eq_true,
      ↓reduceIte]
    by_cases hs : Seg.canon acc.reverse = []
    · rw [hs, Seg.canonFirst_nil]
      simp only [↓reduceIte, List.isEmpty_nil, Bool.not_true, ih]
      exact (canonLast_prepend_loop [] _ _).symm
    · have hne : (Seg.canonFirst (Seg.canon acc.reverse)).isEmpty = false := by
        rw [List.isEmpty_eq_false_iff, ne_eq, ← List.length_eq_zero_iff, (Seg.canonFirst_spec _).1,
          List.length_eq_zero_iff]
        exact hs
      simp only [hs, ↓reduceIte, hne, Bool.not_false, nf_true, canonLast_prepend_loop]


theorem size_of_mem_pick {M : DeadMode} {a : Nat} {live : List Program} {x : Program}
    (ih : ∀ {q : Program}, q ∈ live → q.size = a) (h : x ∈ pick M a live) : x.size = a := by
  cases M with
  | live => exact ih h
  | dead =>
    simp only [pick, List.mem_singleton] at h
    subst h
    simpa using size_canonSegs (stars a) []
  | chain =>
    simp only [pick] at h
    split at h
    · next ha => simp only [List.mem_singleton] at h; subst h; simp [ha, Program.size]
    · simp at h

theorem size_of_mem_body {m : DeadMode} {n : Nat} {q : Program} (h : q ∈ body m n) :
    q.size = n := by
  induction n using Nat.strongRecOn generalizing m q with
  | _ n ih =>
    rw [body] at h
    simp only [List.mem_append, List.mem_map, List.mem_flatMap, List.mem_range] at h
    rcases h with ⟨s, hs, rfl⟩ | ⟨L, hL, s, hs, a, ha, b, hb, h⟩
    · simp [Seg.size_prepend, Seg.length_of_mem_mids hs, Program.size]
    · split at h
      · next he =>
        simp only [List.mem_flatMap, List.mem_map] at h
        obtain ⟨x, hx, y, hy, rfl⟩ := h
        have hxs := size_of_mem_pick (fun {q : Program} (hq : q ∈ body .live a) => ih a ha hq) hx
        simp only [Seg.size_prepend, Program.size, Seg.length_of_mem_mids hs, hxs, ih b hb hy]
        omega
      · simp at h

theorem size_of_mem_top {seen : Bool} {m : DeadMode} {n : Nat} {q : Program}
    (h : q ∈ top seen m n) : q.size = n := by
  induction n using Nat.strongRecOn generalizing seen m q with
  | _ n ih =>
    rw [top] at h
    simp only [List.mem_append, List.mem_singleton, List.mem_flatMap, List.mem_range] at h
    rcases h with rfl | ⟨L, hL, s, hs, a, ha, b, hb, h⟩
    · simp
    · split at h
      · next he =>
        simp only [List.mem_flatMap, List.mem_map] at h
        obtain ⟨x, hx, y, hy, rfl⟩ := h
        have hsL : s.length = L := by
          split at hs
          · exact Seg.length_of_mem_mids hs
          · exact Seg.length_of_mem_firsts hs
        have hxs := size_of_mem_pick (fun {q : Program} (hq : q ∈ body .live a) => size_of_mem_body hq) hx
        simp only [Seg.size_prepend, Program.size, hsL, hxs, ih b hb hy]
        omega
      · simp at h

theorem canonSegs_mem_body (p : Program) : ∀ (m M : DeadMode) (acc : Seg), M = eff m acc →
    Dead M p → canonSegs acc p ∈ body m (acc.length + p.size) := by
  induction p with
  | nil =>
    intro m M acc _ _
    rw [body]
    refine List.mem_append_left _ (List.mem_map.mpr ⟨Seg.canon acc.reverse, ?_, rfl⟩)
    have := Seg.canon_mem_mids acc.reverse
    simpa [Program.size] using this
  | left p ih =>
    intro m M acc _ hp
    cases hp with
    | left hp =>
      have := ih m .live (.left :: acc) rfl hp
      simp only [List.length_cons, Program.size] at this ⊢
      rw [canonSegs, show acc.length + (p.size + 1) = acc.length + 1 + p.size by omega]
      exact this
  | right p ih =>
    intro m M acc _ hp
    cases hp with
    | right hp =>
      have := ih m .live (.right :: acc) rfl hp
      simp only [List.length_cons, Program.size] at this ⊢
      rw [canonSegs, show acc.length + (p.size + 1) = acc.length + 1 + p.size by omega]
      exact this
  | flip p ih =>
    intro m M acc _ hp
    cases hp with
    | flip hp =>
      have := ih m .live (.flip :: acc) rfl hp
      simp only [List.length_cons, Program.size] at this ⊢
      rw [canonSegs, show acc.length + (p.size + 1) = acc.length + 1 + p.size by omega]
      exact this
  | loop b p ihb ih =>
    intro m M acc hM hp
    rw [body]
    refine List.mem_append_right _ ?_
    simp only [List.mem_flatMap, List.mem_range]
    have hE : eff m (Seg.canon acc.reverse) = M := by rw [eff_canon, eff_reverse, hM]
    refine ⟨acc.length, by simp only [Program.size]; omega, Seg.canon acc.reverse, ?_,
      b.size, by simp only [Program.size]; omega, p.size, by simp only [Program.size]; omega, ?_⟩
    · simpa using Seg.canon_mem_mids acc.reverse
    · rw [ite_eq_left (by simp only [Program.size]; omega), hE]
      simp only [List.mem_flatMap, List.mem_map]
      refine ⟨canonSegs [] b, ?_, canonSegs [] p, ?_, rfl⟩
      · cases hp with
        | live hb hp' => simpa [pick] using ihb .live .live [] rfl hb
        | dead hp' => simp [pick, size_stars]
        | chain hp' => simp [pick, Program.size, canonSegs, canon_nil, Seg.prepend]
      · cases hp with
        | live hb hp' => simpa [next] using ih .dead .dead [] rfl hp'
        | dead hp' => simpa [next] using ih .chain .chain [] rfl hp'
        | chain hp' => simpa [next] using ih .chain .chain [] rfl hp'

theorem nf_mem_top (p : Program) : ∀ (seen : Bool) (m M : DeadMode) (acc : Seg), M = eff m acc →
    Dead M p → nf seen acc p ∈ top seen m (acc.length + p.size) := by
  induction p with
  | nil =>
    intro seen m M acc _ _
    rw [top]
    simp [nf, Program.size]
  | left p ih =>
    intro seen m M acc _ hp
    cases hp with
    | left hp =>
      have := ih seen m .live (.left :: acc) rfl hp
      simp only [List.length_cons, Program.size] at this ⊢
      rw [nf, show acc.length + (p.size + 1) = acc.length + 1 + p.size by omega]
      exact this
  | right p ih =>
    intro seen m M acc _ hp
    cases hp with
    | right hp =>
      have := ih seen m .live (.right :: acc) rfl hp
      simp only [List.length_cons, Program.size] at this ⊢
      rw [nf, show acc.length + (p.size + 1) = acc.length + 1 + p.size by omega]
      exact this
  | flip p ih =>
    intro seen m M acc _ hp
    cases hp with
    | flip hp =>
      have := ih seen m .live (.flip :: acc) rfl hp
      simp only [List.length_cons, Program.size] at this ⊢
      rw [nf, show acc.length + (p.size + 1) = acc.length + 1 + p.size by omega]
      exact this
  | loop b p _ ih =>
    intro seen m M acc hM hp
    rw [top]
    refine List.mem_append_right _ ?_
    simp only [List.mem_flatMap, List.mem_range]
    have hlen : (if seen then Seg.canon acc.reverse else Seg.canonFirst (Seg.canon acc.reverse)).length =
        acc.length := by
      split
      · simp [Seg.length_canon]
      · simp [(Seg.canonFirst_spec _).1, Seg.length_canon]
    have hE : eff m (if seen then Seg.canon acc.reverse else Seg.canonFirst (Seg.canon acc.reverse)) = M := by
      rw [eff_of_length m (t := acc) (by rw [hlen]), hM]
    refine ⟨acc.length, by simp only [Program.size]; omega,
      if seen then Seg.canon acc.reverse else Seg.canonFirst (Seg.canon acc.reverse), ?_,
      b.size, by simp only [Program.size]; omega, p.size, by simp only [Program.size]; omega, ?_⟩
    · cases seen
      · simpa using Seg.canonFirst_mem_firsts acc.reverse
      · simpa using Seg.canon_mem_mids acc.reverse
    · rw [ite_eq_left (by simp only [Program.size]; omega), hE]
      simp only [List.mem_flatMap, List.mem_map]
      refine ⟨canonSegs [] b, ?_, _, ?_, rfl⟩
      · cases hp with
        | live hb hp' => simpa [pick] using canonSegs_mem_body b .live .live [] rfl hb
        | dead hp' => simp [pick, size_stars]
        | chain hp' => simp [pick, Program.size, canonSegs, canon_nil, Seg.prepend]
      · cases hp with
        | live hb hp' => simpa [next] using ih _ .dead .dead [] rfl hp'
        | dead hp' => simpa [next] using ih _ .chain .chain [] rfl hp'
        | chain hp' => simpa [next] using ih _ .chain .chain [] rfl hp'

end Generator.canonical

def Generator.canonical : Generator where
  gen   := Generator.canonical.top false .dead
  size  := Generator.canonical.size_of_mem_top
  cover := fun (p : Program) => by
    refine ⟨Generator.canonical.nf false [] (Program.canonDead .dead p), ?_, ?_⟩
    · have h := Generator.canonical.nf_mem_top (Program.canonDead .dead p) false .dead .dead [] rfl
        (Program.dead_canonDead .dead p)
      rw [show (Program.canonDead .dead p).size = p.size by simpa using Program.size_canonDead p .dead] at h
      simpa using h
    · rw [Generator.canonical.nf_false]
      exact ((((Canon.deadLoops.sound p).trans (Canon.segments.sound _)).trans
        (Canon.firstSeg.sound _)).trans (Canon.lastSeg.sound _))

end Bf
