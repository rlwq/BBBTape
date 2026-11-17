import Bf.Search
import Bf.Normal

namespace Bf

namespace Program

def mkHole (i k : Nat) : Program := if k = 0 then nil else hole i k

theorem fills_mkHole (i : Nat) {k : Nat} {p : Program} (hc : p.Closed) (hs : p.size = k) :
    Fills (mkHole i k) p := by
  unfold mkHole
  split
  · next h =>
    subst h
    cases p with
    | nil => exact .nil
    | hole => exact absurd hc id
    | left | right | flip | loop => simp [size] at hs
  · exact .hole i hc hs

theorem fills_self {p : Program} (h : p.Closed) : Fills p p := by
  induction p with
  | nil => exact .nil
  | hole => exact absurd h id
  | left p ih => exact .left (ih h)
  | right p ih => exact .right (ih h)
  | flip p ih => exact .flip (ih h)
  | loop b p ihb ih => exact .loop (ihb h.1) (ih h.2)

theorem fills_prepend (s : Seg) {x y : Program} (h : Fills x y) :
    Fills (Seg.prepend s x) (Seg.prepend s y) := by
  induction s with
  | nil => exact h
  | cons c s ih =>
    cases c
    · exact .flip ih
    · exact .left ih
    · exact .right ih

theorem splitSeg_snd (p : Program) :
    (splitSeg p).2 = nil ∨ (∃ b r : Program, (splitSeg p).2 = loop b r) ∨
      ∃ i k : Nat, (splitSeg p).2 = hole i k := by
  induction p with
  | nil => exact .inl rfl
  | hole i k => exact .inr (.inr ⟨i, k, rfl⟩)
  | loop b r => exact .inr (.inl ⟨b, r, rfl⟩)
  | left p ih | right p ih | flip p ih => exact ih

theorem exists_prepend {p : Program} (h : p.Closed) :
    ∃ (s : Seg) (x : Program), p = Seg.prepend s x ∧ (x = nil ∨ ∃ b r : Program, x = loop b r) := by
  refine ⟨(splitSeg p).1, (splitSeg p).2, (prepend_splitSeg p).symm, ?_⟩
  rcases splitSeg_snd p with h₁ | h₁ | ⟨i, k, h₁⟩
  · exact .inl h₁
  · exact .inr h₁
  · have hc := (closed_prepend (splitSeg p).1 (splitSeg p).2).mp (by rw [prepend_splitSeg]; exact h)
    rw [h₁] at hc
    exact absurd hc id

def shapesC (tbl : Nat → List Seg) (top : Bool) (i fresh k : Nat) : List Program :=
  (match top with
    | true  => [stars k]
    | false => (tbl k).map fun (s : Seg) => Seg.prepend s nil) ++
  (List.range (k - 1)).flatMap fun (j : Nat) => (tbl j).flatMap fun (s : Seg) =>
    (List.range (k - j - 1)).map fun (a : Nat) =>
      Seg.prepend s (loop (mkHole fresh a) (mkHole i (k - j - 2 - a)))

theorem shapesC_cover {tbl : Nat → List Seg} (htbl : ∀ j : Nat, tbl j = Seg.mids j) (top : Bool)
    (i fresh : Nat) {k : Nat} {p : Program} (hc : p.Closed) (hs : p.size = k)
    (hn : Normal top [] p) : ∃ c ∈ shapesC tbl top i fresh k, Fills c p := by
  obtain ⟨s, x, rfl, hx⟩ := exists_prepend hc
  have hn' := (normal_prepend top s [] x).mp hn
  rw [Seg.size_prepend] at hs
  have hcx := (closed_prepend s x).mp hc
  rcases hx with rfl | ⟨b, r, rfl⟩
  · simp only [size, Nat.add_zero] at hs
    subst hs
    cases top with
    | false =>
      have hm : s ∈ Seg.mids s.length := by
        simpa [Normal] using hn'
      exact ⟨Seg.prepend s nil, List.mem_append_left _ (List.mem_map.mpr ⟨s, by rw [htbl]; exact hm, rfl⟩),
        fills_self hc⟩
    | true =>
      have hall : ∀ c ∈ s, c = Cmd.flip := by
        simpa [Normal] using hn'
      have hrep : s = List.replicate s.length Cmd.flip := List.eq_replicate_iff.mpr ⟨rfl, hall⟩
      have hst : Seg.prepend s nil = stars s.length := by
        rw [hrep, Seg.prepend_replicate, List.length_replicate]
      refine ⟨stars s.length, List.mem_append_left _ (List.mem_singleton_self _), ?_⟩
      rw [hst]
      exact fills_self (closed_stars _)
  · have hm : s ∈ Seg.mids s.length := by
      simpa using hn'.1
    simp only [size] at hs
    refine ⟨Seg.prepend s (loop (mkHole fresh b.size) (mkHole i (k - s.length - 2 - b.size))),
      List.mem_append_right _ (List.mem_flatMap.mpr ⟨s.length, List.mem_range.mpr (by omega),
        List.mem_flatMap.mpr ⟨s, by rw [htbl]; exact hm,
          List.mem_map.mpr ⟨b.size, List.mem_range.mpr (by omega), rfl⟩⟩⟩),
      fills_prepend s (.loop (fills_mkHole fresh hcx.1 rfl) (fills_mkHole i hcx.2 (by omega)))⟩

def expandC (tbl : Nat → List Seg) (i fresh : Nat) : Bool → Bool → Program → Option (List Program)
  | _,   _,     nil      => none
  | top, _,     left p   => (expandC tbl i fresh top false p).map fun (cs : List Program) => cs.map left
  | top, _,     right p  => (expandC tbl i fresh top false p).map fun (cs : List Program) => cs.map right
  | top, _,     flip p   => (expandC tbl i fresh top false p).map fun (cs : List Program) => cs.map flip
  | top, _,     loop b p => match expandC tbl i fresh false true b with
    | some cs => some (cs.map fun (c : Program) => loop c p)
    | none    => (expandC tbl i fresh top true p).map fun (cs : List Program) => cs.map (loop b)
  | top, start, hole j k => if j = i ∧ start = true then some (shapesC tbl top i fresh k) else none

theorem expandC_cover {tbl : Nat → List Seg} (htbl : ∀ j : Nat, tbl j = Seg.mids j) {i fresh : Nat}
    {top start : Bool} {q p : Program} {cs : List Program} {acc : Seg}
    (he : expandC tbl i fresh top start q = some cs) (h : Fills q p) (hacc : start = true → acc = [])
    (hn : Normal top acc p) : ∃ c ∈ cs, Fills c p := by
  induction h generalizing top start cs acc with
  | nil => simp [expandC] at he
  | left _ ih =>
    simp only [expandC, Option.map_eq_some_iff] at he
    obtain ⟨ds, hd, rfl⟩ := he
    obtain ⟨c, hc, hf⟩ := ih hd (acc := .left :: acc) (fun (h : false = true) => by cases h) hn
    exact ⟨_, List.mem_map.mpr ⟨c, hc, rfl⟩, .left hf⟩
  | right _ ih =>
    simp only [expandC, Option.map_eq_some_iff] at he
    obtain ⟨ds, hd, rfl⟩ := he
    obtain ⟨c, hc, hf⟩ := ih hd (acc := .right :: acc) (fun (h : false = true) => by cases h) hn
    exact ⟨_, List.mem_map.mpr ⟨c, hc, rfl⟩, .right hf⟩
  | flip _ ih =>
    simp only [expandC, Option.map_eq_some_iff] at he
    obtain ⟨ds, hd, rfl⟩ := he
    obtain ⟨c, hc, hf⟩ := ih hd (acc := .flip :: acc) (fun (h : false = true) => by cases h) hn
    exact ⟨_, List.mem_map.mpr ⟨c, hc, rfl⟩, .flip hf⟩
  | @loop b b' q p hb hq ihb ih =>
    simp only [expandC] at he
    cases hx : expandC tbl i fresh false true b with
    | some ds =>
      rw [hx] at he
      cases he
      obtain ⟨c, hc, hf⟩ := ihb hx (acc := []) (fun (_ : true = true) => rfl) hn.2.1
      exact ⟨_, List.mem_map.mpr ⟨c, hc, rfl⟩, .loop hf hq⟩
    | none =>
      rw [hx] at he
      simp only [Option.map_eq_some_iff] at he
      obtain ⟨ds, hd, rfl⟩ := he
      obtain ⟨c, hc, hf⟩ := ih hd (acc := []) (fun (_ : true = true) => rfl) hn.2.2
      exact ⟨_, List.mem_map.mpr ⟨c, hc, rfl⟩, .loop hb hf⟩
  | hole j hc hs =>
    simp only [expandC] at he
    split at he
    · next hcond =>
      cases he
      obtain rfl := hacc hcond.2
      exact shapesC_cover htbl top i fresh hc hs hn
    · cases he

end Program

def segTable (n : Nat) : Array (List Seg) := ((List.range (n + 1)).map Seg.mids).toArray

def segLookup (arr : Array (List Seg)) (j : Nat) : List Seg :=
  if h : j < arr.size then arr[j] else Seg.mids j

theorem segLookup_segTable (n j : Nat) : segLookup (segTable n) j = Seg.mids j := by
  unfold segLookup
  split
  · simp [segTable]
  · rfl

def Brancher.canonical (n : Nat) : Brancher :=
  let arr : Array (List Seg) := segTable n
  { P := Program.Normal true []
    expand := fun (i fresh : Nat) (q : Program) => Program.expandC (segLookup arr) i fresh true true q
    cover := fun {i fresh : Nat} {q p : Program} {cs : List Program}
      (he : Program.expandC (segLookup arr) i fresh true true q = some cs) (h : q.Fills p)
      (hP : Program.Normal true [] p) =>
      Program.expandC_cover (segLookup_segTable n) he h (fun (_ : true = true) => rfl) hP
    norm := fun (p : Program) (hc : p.Closed) => ⟨p.norm, Program.norm_spec hc⟩ }

end Bf
