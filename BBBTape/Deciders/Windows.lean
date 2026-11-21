import Std.Data.HashSet
import BBBTape.Core.Decider
import BBBTape.Tapes.Zipper

namespace BBBTape

namespace Windows

open scoped Program Machine

def win (n : Nat) (l : List Bool) : List Bool := (List.range n).map fun (k : Nat) => l.getD k false

theorem win_succ_cons (m : Nat) (h : Bool) (l : List Bool) :
    win (m + 1) (h :: l) = h :: win m l := by
  unfold win
  rw [List.range_succ_eq_map]
  simp

theorem win_succ (m : Nat) (l : List Bool) : win (m + 1) l = win m l ++ [l.getD m false] := by
  unfold win
  rw [List.range_succ]
  simp

theorem win_tail (m : Nat) (l : List Bool) :
    win (m + 1) l.tail = (win (m + 1) l).tail ++ [l.getD (m + 1) false] := by
  have h1 : win (m + 1 + 1) l = l.getD 0 false :: win (m + 1) l.tail := by
    unfold win
    rw [List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map]
    congr 1
    congr 1
    funext k
    cases l <;> simp
  have h2 := win_succ (m + 1) l
  rw [h1] at h2
  have h3 : (win (m + 1) l).tail ++ [l.getD (m + 1) false] =
      (win (m + 1) l ++ [l.getD (m + 1) false]).tail := by
    cases hw : win (m + 1) l with
    | nil => simp [win] at hw
    | cons a w => simp
  rw [h3, ← h2]
  rfl

theorem win_dropLast (m : Nat) (l : List Bool) : win m l = (win (m + 1) l).dropLast := by
  rw [win_succ, List.dropLast_concat]

theorem win_cons (m : Nat) (h : Bool) (l : List Bool) :
    win (m + 1) (h :: l) = h :: (win (m + 1) l).dropLast := by
  rw [win_succ_cons, win_dropLast]

theorem win_cons_drop (n j : Nat) (h : Bool) (l : List Bool) :
    win n ((h :: l).drop (j + 1)) = win n (l.drop j) := by
  rw [List.drop_succ_cons]

theorem win_tail_drop (n k : Nat) (l : List Bool) :
    win n (l.tail.drop k) = win n (l.drop (k + 1)) := by
  rw [List.drop_tail]

theorem headD_win (m : Nat) (l : List Bool) : (win (m + 1) l).headD false = l.headD false := by
  unfold win
  rw [List.range_succ_eq_map]
  cases l <;> simp

theorem win_nil_drop (n k : Nat) : win n (([] : List Bool).drop k) = List.replicate n false := by
  unfold win
  simp [List.map_const']

structure Loc where
  prog  : Program
  left  : List Bool
  head  : Bool
  right : List Bool
  deriving DecidableEq, Hashable

def succs (LS RS : Std.HashSet (List Bool)) (s : Loc) : List Loc :=
  match s.prog with
  | ε          => []
  | .gap _ _ _ => []
  | .flip p    => [⟨p, s.left, !s.head, s.right⟩]
  | .loop b q  => [⟨if s.head then b ++ .loop b q else q, s.left, s.head, s.right⟩]
  | .right p   =>
    ([false, true].filter fun (x : Bool) => RS.contains (s.right.tail ++ [x])).map fun (x : Bool) =>
      ⟨p, s.head :: s.left.dropLast, s.right.headD false, s.right.tail ++ [x]⟩
  | .left p    =>
    ([false, true].filter fun (x : Bool) => LS.contains (s.left.tail ++ [x])).map fun (x : Bool) =>
      ⟨p, s.left.tail ++ [x], s.left.headD false, s.head :: s.right.dropLast⟩

def gramOK (LS RS : Std.HashSet (List Bool)) (s : Loc) : Bool :=
  match s.prog with
  | .right _ => LS.contains (s.head :: s.left.dropLast)
  | .left _  => RS.contains (s.head :: s.right.dropLast)
  | _        => true

def closed (S : Std.HashSet Loc) (LS RS : Std.HashSet (List Bool)) : Bool :=
  S.toList.all fun (s : Loc) => s.prog.alive && (succs LS RS s).all S.contains && gramOK LS RS s

def Rep (m : Nat) (S : Std.HashSet Loc) (LS RS : Std.HashSet (List Bool)) (c : Machine Zipper) : Prop :=
  (⟨c.prog, win (m + 1) c.tape.left, c.tape.head, win (m + 1) c.tape.right⟩ : Loc) ∈ S ∧
  (∀ k : Nat, win (m + 1) (c.tape.left.drop k) ∈ LS) ∧
  (∀ k : Nat, win (m + 1) (c.tape.right.drop k) ∈ RS)

theorem Rep.step {m : Nat} {S : Std.HashSet Loc} {LS RS : Std.HashSet (List Bool)}
    (hc : closed S LS RS = true) {c : Machine Zipper} (h : Rep m S LS RS c) :
    ∃ c' : Machine Zipper, c⇒ = some c' ∧ Rep m S LS RS c' := by
  obtain ⟨hS, hL, hR⟩ := h
  have hcl := List.all_eq_true.mp hc _ (Std.HashSet.mem_toList.mpr hS)
  simp only [Bool.and_eq_true, List.all_eq_true] at hcl
  obtain ⟨⟨halive, hsucc⟩, hgram⟩ := hcl
  obtain ⟨t, p⟩ := c
  cases p with
  | nil => simp [Program.alive] at halive
  | gap => simp [Program.alive] at halive
  | flip p =>
    refine ⟨⟨t.flip, p⟩, rfl, ?_, hL, hR⟩
    exact Std.HashSet.mem_iff_contains.mpr (hsucc _ (by simp [succs]; exact ⟨rfl, rfl, rfl⟩))
  | loop b q =>
    refine ⟨⟨t, if t.head then b ++ .loop b q else q⟩, rfl, ?_, hL, hR⟩
    exact Std.HashSet.mem_iff_contains.mpr (hsucc _ (by simp [succs]))
  | right p =>
    refine ⟨⟨t.moveR, p⟩, rfl, ?_, ?_, ?_⟩
    · apply Std.HashSet.mem_iff_contains.mpr
      apply hsucc
      simp only [succs, List.mem_map, List.mem_filter]
      refine ⟨t.right.getD (m + 1) false, ⟨by cases t.right.getD (m + 1) false <;> simp, ?_⟩, ?_⟩
      · rw [← win_tail]
        exact Std.HashSet.mem_iff_contains.mp (by simpa using hR 1)
      · show (⟨p, t.head :: (win (m + 1) t.left).dropLast, (win (m + 1) t.right).headD false,
          (win (m + 1) t.right).tail ++ [t.right.getD (m + 1) false]⟩ : Loc) =
          ⟨p, win (m + 1) (t.head :: t.left), t.right.headD false, win (m + 1) t.right.tail⟩
        rw [win_cons, headD_win, win_tail]
    · intro k
      show win (m + 1) ((t.head :: t.left).drop k) ∈ LS
      cases k with
      | zero =>
        simp only [List.drop_zero]
        rw [win_cons]
        exact Std.HashSet.mem_iff_contains.mpr (by simpa [gramOK] using hgram)
      | succ j =>
        rw [win_cons_drop]
        exact hL j
    · intro k
      show win (m + 1) (t.right.tail.drop k) ∈ RS
      rw [win_tail_drop]
      exact hR (k + 1)
  | left p =>
    refine ⟨⟨t.moveL, p⟩, rfl, ?_, ?_, ?_⟩
    · apply Std.HashSet.mem_iff_contains.mpr
      apply hsucc
      simp only [succs, List.mem_map, List.mem_filter]
      refine ⟨t.left.getD (m + 1) false, ⟨by cases t.left.getD (m + 1) false <;> simp, ?_⟩, ?_⟩
      · rw [← win_tail]
        exact Std.HashSet.mem_iff_contains.mp (by simpa using hL 1)
      · show (⟨p, (win (m + 1) t.left).tail ++ [t.left.getD (m + 1) false],
          (win (m + 1) t.left).headD false, t.head :: (win (m + 1) t.right).dropLast⟩ : Loc) =
          ⟨p, win (m + 1) t.left.tail, t.left.headD false, win (m + 1) (t.head :: t.right)⟩
        rw [win_cons, headD_win, win_tail]
    · intro k
      show win (m + 1) (t.left.tail.drop k) ∈ LS
      rw [win_tail_drop]
      exact hL (k + 1)
    · intro k
      show win (m + 1) ((t.head :: t.right).drop k) ∈ RS
      cases k with
      | zero =>
        simp only [List.drop_zero]
        rw [win_cons]
        exact Std.HashSet.mem_iff_contains.mpr (by simpa [gramOK] using hgram)
      | succ j =>
        rw [win_cons_drop]
        exact hR j

theorem Rep.diverges {m : Nat} {S : Std.HashSet Loc} {LS RS : Std.HashSet (List Bool)}
    (hc : closed S LS RS = true) {c : Machine Zipper} (h : Rep m S LS RS c) : c⇑ := by
  intro k
  induction k generalizing c with
  | zero => rfl
  | succ k ih =>
    obtain ⟨c', hs, hr⟩ := Rep.step hc h
    simp only [Machine.steps, hs, Option.bind_some]
    exact ih hr

def zeros (m : Nat) : List Bool := List.replicate (m + 1) false

/-- Semi-naive fixpoint growth on hash sets: each round expands only newly added states, plus
previously seen moving states whose side's window set just grew. -/
def grow (m fuel : Nat) (q : Program) :
    Option (Std.HashSet Loc × Std.HashSet (List Bool) × Std.HashSet (List Bool)) := Id.run do
  let z := zeros m
  let init : Loc := ⟨q, z, false, z⟩
  if !init.prog.alive then return none
  let mut S  : Std.HashSet Loc := (∅ : Std.HashSet Loc).insert init
  let mut LS : Std.HashSet (List Bool) := (∅ : Std.HashSet (List Bool)).insert z
  let mut RS : Std.HashSet (List Bool) := (∅ : Std.HashSet (List Bool)).insert z
  let mut new    : Array Loc := #[init]
  let mut lefts  : Array Loc := #[]
  let mut rights : Array Loc := #[]
  let mut lsGrew := false
  let mut rsGrew := false
  for _ in [0:fuel] do
    let mut added : Array Loc := #[]
    for s in new do
      for x in succs LS RS s do
        if !x.prog.alive then return none
        if !S.contains x then
          S := S.insert x
          added := added.push x
    if lsGrew then
      for s in lefts do
        for x in succs LS RS s do
          if !x.prog.alive then return none
          if !S.contains x then
            S := S.insert x
            added := added.push x
    if rsGrew then
      for s in rights do
        for x in succs LS RS s do
          if !x.prog.alive then return none
          if !S.contains x then
            S := S.insert x
            added := added.push x
    let lsPrev := LS.size
    let rsPrev := RS.size
    for s in new do
      match s.prog with
      | .right _ => LS := LS.insert (s.head :: s.left.dropLast); rights := rights.push s
      | .left _  => RS := RS.insert (s.head :: s.right.dropLast); lefts := lefts.push s
      | _        => pure ()
    lsGrew := LS.size != lsPrev
    rsGrew := RS.size != rsPrev
    if added.isEmpty && !lsGrew && !rsGrew then
      return some (S, LS, RS)
    if 5000 < S.size then
      return none
    new := added
  return none

def check (m fuel : Nat) (q : Program) : Bool :=
  let z := zeros m
  let init : Loc := ⟨q, z, false, z⟩
  match grow m fuel q with
  | some (S, LS, RS) => closed S LS RS && S.contains init && LS.contains z && RS.contains z
  | none => false

theorem rep_init {m : Nat} {q : Program} {S : Std.HashSet Loc} {LS RS : Std.HashSet (List Bool)}
    (h0 : (⟨q, zeros m, false, zeros m⟩ : Loc) ∈ S) (hl : zeros m ∈ LS) (hr : zeros m ∈ RS) :
    Rep m S LS RS (q.init Zipper) := by
  refine ⟨?_, fun (k : Nat) => ?_, fun (k : Nat) => ?_⟩
  · have e : win (m + 1) ([] : List Bool) = zeros m := by
      simpa [zeros] using win_nil_drop (m + 1) 0
    show (⟨q, win (m + 1) [], false, win (m + 1) []⟩ : Loc) ∈ S
    rw [e]
    exact h0
  · show win (m + 1) (([] : List Bool).drop k) ∈ LS
    rw [win_nil_drop]
    exact hl
  · show win (m + 1) (([] : List Bool).drop k) ∈ RS
    rw [win_nil_drop]
    exact hr

theorem check_sound {m fuel : Nat} {q : Program} :
    check m fuel q = true → q⇑ := by
  intro h
  unfold check at h
  dsimp only at h
  split at h
  · simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨hc, h0⟩, hl⟩, hr⟩ := h
    exact Program.diverges_of (Rep.diverges hc (rep_init
      (Std.HashSet.mem_iff_contains.mpr h0)
      (Std.HashSet.mem_iff_contains.mpr hl)
      (Std.HashSet.mem_iff_contains.mpr hr)))
  · cases h

structure PLoc where
  prog  : Program
  phase : Bool
  left  : List Bool
  head  : Bool
  right : List Bool
  deriving DecidableEq, Hashable

def pSuccs (LS RS : Std.HashSet (Bool × List Bool)) (s : PLoc) : List PLoc :=
  match s.prog with
  | ε          => []
  | .gap _ _ _ => []
  | .flip p    => [⟨p, s.phase, s.left, !s.head, s.right⟩]
  | .loop b q  => [⟨if s.head then b ++ .loop b q else q, s.phase, s.left, s.head, s.right⟩]
  | .right p   =>
    ([false, true].filter fun (x : Bool) => RS.contains (!s.phase, s.right.tail ++ [x])).map fun (x : Bool) =>
      ⟨p, !s.phase, s.head :: s.left.dropLast, s.right.headD false, s.right.tail ++ [x]⟩
  | .left p    =>
    ([false, true].filter fun (x : Bool) => LS.contains (!s.phase, s.left.tail ++ [x])).map fun (x : Bool) =>
      ⟨p, !s.phase, s.left.tail ++ [x], s.left.headD false, s.head :: s.right.dropLast⟩

def pGramOK (LS RS : Std.HashSet (Bool × List Bool)) (s : PLoc) : Bool :=
  match s.prog with
  | .right _ => LS.contains (!s.phase, s.head :: s.left.dropLast)
  | .left _  => RS.contains (!s.phase, s.head :: s.right.dropLast)
  | _        => true

def pClosed (S : Std.HashSet PLoc) (LS RS : Std.HashSet (Bool × List Bool)) : Bool :=
  S.toList.all fun (s : PLoc) => s.prog.alive && (pSuccs LS RS s).all S.contains && pGramOK LS RS s

def phaseAt (ph : Bool) (k : Nat) : Bool :=
  if k % 2 == 0 then ph else !ph

theorem phaseAt_zero (ph : Bool) : phaseAt ph 0 = ph := rfl

theorem phaseAt_one (ph : Bool) : phaseAt ph 1 = !ph := rfl

theorem phaseAt_succ (ph : Bool) (k : Nat) : phaseAt ph (k + 1) = phaseAt (!ph) k := by
  unfold phaseAt
  have h1 : (k + 1) % 2 = 1 - k % 2 := by omega
  rcases Nat.mod_two_eq_zero_or_one k with h0 | h2
  · rw [h1, h0]; cases ph <;> rfl
  · rw [h1, h2]; cases ph <;> rfl

theorem phaseAt_not_succ (ph : Bool) (k : Nat) : phaseAt (!ph) (k + 1) = phaseAt ph k := by
  rw [phaseAt_succ, Bool.not_not]

def PRep (m : Nat) (S : Std.HashSet PLoc) (LS RS : Std.HashSet (Bool × List Bool))
    (c : Machine Zipper) : Prop :=
  ∃ ph : Bool,
    (⟨c.prog, ph, win (m + 1) c.tape.left, c.tape.head, win (m + 1) c.tape.right⟩ : PLoc) ∈ S ∧
    (∀ k : Nat, (phaseAt ph k, win (m + 1) (c.tape.left.drop k)) ∈ LS) ∧
    (∀ k : Nat, (phaseAt ph k, win (m + 1) (c.tape.right.drop k)) ∈ RS)

theorem PRep.step {m : Nat} {S : Std.HashSet PLoc} {LS RS : Std.HashSet (Bool × List Bool)}
    (hc : pClosed S LS RS = true) {c : Machine Zipper} (h : PRep m S LS RS c) :
    ∃ c' : Machine Zipper, c⇒ = some c' ∧ PRep m S LS RS c' := by
  obtain ⟨ph, hS, hL, hR⟩ := h
  have hcl := List.all_eq_true.mp hc _ (Std.HashSet.mem_toList.mpr hS)
  simp only [Bool.and_eq_true, List.all_eq_true] at hcl
  obtain ⟨⟨halive, hsucc⟩, hgram⟩ := hcl
  obtain ⟨t, p⟩ := c
  cases p with
  | nil => simp [Program.alive] at halive
  | gap => simp [Program.alive] at halive
  | flip p =>
    refine ⟨⟨t.flip, p⟩, rfl, ph, ?_, hL, hR⟩
    exact Std.HashSet.mem_iff_contains.mpr (hsucc _ (by simp [pSuccs]; exact ⟨rfl, rfl, rfl⟩))
  | loop b q =>
    refine ⟨⟨t, if t.head then b ++ .loop b q else q⟩, rfl, ph, ?_, hL, hR⟩
    exact Std.HashSet.mem_iff_contains.mpr (hsucc _ (by simp [pSuccs]))
  | right p =>
    refine ⟨⟨t.moveR, p⟩, rfl, !ph, ?_, ?_, ?_⟩
    · apply Std.HashSet.mem_iff_contains.mpr
      apply hsucc
      simp only [pSuccs, List.mem_map, List.mem_filter]
      refine ⟨t.right.getD (m + 1) false, ⟨by cases t.right.getD (m + 1) false <;> simp, ?_⟩, ?_⟩
      · rw [← win_tail]
        have hr1 := hR 1
        rw [phaseAt_one, List.drop_one] at hr1
        exact Std.HashSet.mem_iff_contains.mp hr1
      · show (⟨p, !ph, t.head :: (win (m + 1) t.left).dropLast, (win (m + 1) t.right).headD false,
          (win (m + 1) t.right).tail ++ [t.right.getD (m + 1) false]⟩ : PLoc) =
          ⟨p, !ph, win (m + 1) (t.head :: t.left), t.right.headD false, win (m + 1) t.right.tail⟩
        rw [win_cons, headD_win, win_tail]
    · intro k
      show (phaseAt (!ph) k, win (m + 1) ((t.head :: t.left).drop k)) ∈ LS
      cases k with
      | zero =>
        simp only [List.drop_zero, phaseAt_zero]
        rw [win_cons]
        exact Std.HashSet.mem_iff_contains.mpr (by simpa [pGramOK] using hgram)
      | succ j =>
        rw [win_cons_drop, phaseAt_not_succ]
        exact hL j
    · intro k
      show (phaseAt (!ph) k, win (m + 1) (t.right.tail.drop k)) ∈ RS
      rw [win_tail_drop, ← phaseAt_succ]
      exact hR (k + 1)
  | left p =>
    refine ⟨⟨t.moveL, p⟩, rfl, !ph, ?_, ?_, ?_⟩
    · apply Std.HashSet.mem_iff_contains.mpr
      apply hsucc
      simp only [pSuccs, List.mem_map, List.mem_filter]
      refine ⟨t.left.getD (m + 1) false, ⟨by cases t.left.getD (m + 1) false <;> simp, ?_⟩, ?_⟩
      · rw [← win_tail]
        have hl1 := hL 1
        rw [phaseAt_one, List.drop_one] at hl1
        exact Std.HashSet.mem_iff_contains.mp hl1
      · show (⟨p, !ph, (win (m + 1) t.left).tail ++ [t.left.getD (m + 1) false],
          (win (m + 1) t.left).headD false, t.head :: (win (m + 1) t.right).dropLast⟩ : PLoc) =
          ⟨p, !ph, win (m + 1) t.left.tail, t.left.headD false, win (m + 1) (t.head :: t.right)⟩
        rw [win_cons, headD_win, win_tail]
    · intro k
      show (phaseAt (!ph) k, win (m + 1) (t.left.tail.drop k)) ∈ LS
      rw [win_tail_drop, ← phaseAt_succ]
      exact hL (k + 1)
    · intro k
      show (phaseAt (!ph) k, win (m + 1) ((t.head :: t.right).drop k)) ∈ RS
      cases k with
      | zero =>
        simp only [List.drop_zero, phaseAt_zero]
        rw [win_cons]
        exact Std.HashSet.mem_iff_contains.mpr (by simpa [pGramOK] using hgram)
      | succ j =>
        rw [win_cons_drop, phaseAt_not_succ]
        exact hR j

theorem PRep.diverges {m : Nat} {S : Std.HashSet PLoc} {LS RS : Std.HashSet (Bool × List Bool)}
    (hc : pClosed S LS RS = true) {c : Machine Zipper} (h : PRep m S LS RS c) : c⇑ := by
  intro k
  induction k generalizing c with
  | zero => rfl
  | succ k ih =>
    obtain ⟨c', hs, hr⟩ := PRep.step hc h
    simp only [Machine.steps, hs, Option.bind_some]
    exact ih hr

def pGrow (m fuel : Nat) (q : Program) :
    Option (Std.HashSet PLoc × Std.HashSet (Bool × List Bool) × Std.HashSet (Bool × List Bool)) := Id.run do
  let z := zeros m
  let init : PLoc := ⟨q, false, z, false, z⟩
  if !init.prog.alive then return none
  let mut S  : Std.HashSet PLoc := (∅ : Std.HashSet PLoc).insert init
  let mut LS : Std.HashSet (Bool × List Bool) := ((∅ : Std.HashSet (Bool × List Bool)).insert (false, z)).insert (true, z)
  let mut RS : Std.HashSet (Bool × List Bool) := ((∅ : Std.HashSet (Bool × List Bool)).insert (false, z)).insert (true, z)
  let mut new    : Array PLoc := #[init]
  let mut lefts  : Array PLoc := #[]
  let mut rights : Array PLoc := #[]
  let mut lsGrew := false
  let mut rsGrew := false
  for _ in [0:fuel] do
    let mut added : Array PLoc := #[]
    for s in new do
      for x in pSuccs LS RS s do
        if !x.prog.alive then return none
        if !S.contains x then
          S := S.insert x
          added := added.push x
    if lsGrew then
      for s in lefts do
        for x in pSuccs LS RS s do
          if !x.prog.alive then return none
          if !S.contains x then
            S := S.insert x
            added := added.push x
    if rsGrew then
      for s in rights do
        for x in pSuccs LS RS s do
          if !x.prog.alive then return none
          if !S.contains x then
            S := S.insert x
            added := added.push x
    let lsPrev := LS.size
    let rsPrev := RS.size
    for s in new do
      match s.prog with
      | .right _ => LS := LS.insert (!s.phase, s.head :: s.left.dropLast); rights := rights.push s
      | .left _  => RS := RS.insert (!s.phase, s.head :: s.right.dropLast); lefts := lefts.push s
      | _        => pure ()
    lsGrew := LS.size != lsPrev
    rsGrew := RS.size != rsPrev
    if added.isEmpty && !lsGrew && !rsGrew then
      return some (S, LS, RS)
    if 5000 < S.size then
      return none
    new := added
  return none

def pCheck (m fuel : Nat) (q : Program) : Bool :=
  let z := zeros m
  let init : PLoc := ⟨q, false, z, false, z⟩
  match pGrow m fuel q with
  | some (S, LS, RS) =>
    pClosed S LS RS && S.contains init &&
      LS.contains (false, z) && LS.contains (true, z) &&
      RS.contains (false, z) && RS.contains (true, z)
  | none => false

theorem pRep_init {m : Nat} {q : Program} {S : Std.HashSet PLoc} {LS RS : Std.HashSet (Bool × List Bool)}
    (h0 : (⟨q, false, zeros m, false, zeros m⟩ : PLoc) ∈ S)
    (hl0 : (false, zeros m) ∈ LS) (hl1 : (true, zeros m) ∈ LS)
    (hr0 : (false, zeros m) ∈ RS) (hr1 : (true, zeros m) ∈ RS) :
    PRep m S LS RS (q.init Zipper) := by
  refine ⟨false, ?_, fun (k : Nat) => ?_, fun (k : Nat) => ?_⟩
  · have e : win (m + 1) ([] : List Bool) = zeros m := by
      simpa [zeros] using win_nil_drop (m + 1) 0
    show (⟨q, false, win (m + 1) [], false, win (m + 1) []⟩ : PLoc) ∈ S
    rw [e]; exact h0
  · show (phaseAt false k, win (m + 1) (([] : List Bool).drop k)) ∈ LS
    rw [win_nil_drop]; cases phaseAt false k <;> assumption
  · show (phaseAt false k, win (m + 1) (([] : List Bool).drop k)) ∈ RS
    rw [win_nil_drop]; cases phaseAt false k <;> assumption

theorem pCheck_sound {m fuel : Nat} {q : Program} :
    pCheck m fuel q = true → q⇑ := by
  intro h
  unfold pCheck at h
  dsimp only at h
  split at h
  · simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨hc, h0⟩, hl0⟩, hl1⟩, hr0⟩, hr1⟩ := h
    exact Program.diverges_of (PRep.diverges hc (pRep_init
      (Std.HashSet.mem_iff_contains.mpr h0)
      (Std.HashSet.mem_iff_contains.mpr hl0)
      (Std.HashSet.mem_iff_contains.mpr hl1)
      (Std.HashSet.mem_iff_contains.mpr hr0)
      (Std.HashSet.mem_iff_contains.mpr hr1)))
  · cases h

end Windows

def Decider.windows (m fuel : Nat) : Decider := fun q =>
  if h : Windows.check m fuel q then .diverges (Windows.check_sound h) else .unknown

def Decider.windows2 (m fuel : Nat) : Decider := fun q =>
  if h : Windows.pCheck m fuel q then .diverges (Windows.pCheck_sound h) else .unknown

end BBBTape
