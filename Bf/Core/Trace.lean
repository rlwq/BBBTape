import Bf.Core.Mirror

namespace Bf

namespace Machine

open scoped Program Machine

variable {T : Type} [Tape T]

@[inline] def δ (c : Machine T) : Int :=
  match c.prog with
  | .left _  => -1
  | .right _ => 1
  | _        => 0

@[specialize] def disp (c : Machine T) : Nat → Int
  | 0     => 0
  | n + 1 =>
    match c⇒ with
    | none    => 0
    | some c' => c.δ + c'.disp n

/-- Every cell outside the absolute interval `[lo, hi]` is `false` (relative to head at `pos`). -/
def BoundedTape (t : T) (pos lo hi : Int) : Prop :=
  ∀ i : Int, pos + i < lo ∨ hi < pos + i → Tape.cells t i = false

theorem boundedTape_blank : BoundedTape (Tape.blank : T) 0 0 0 :=
  fun i _ => Tape.cells_blank i

theorem BoundedTape.mono {t : T} {pos lo lo' hi hi' : Int}
    (h : BoundedTape t pos lo hi) (hlo : lo' ≤ lo) (hhi : hi ≤ hi') :
    BoundedTape t pos lo' hi' :=
  fun i hi' => h i (by omega)

@[inline] def nextLo (c : Machine T) (pos lo : Int) : Int :=
  match c.prog with
  | .flip _ => min lo pos
  | _       => lo

@[inline] def nextHi (c : Machine T) (pos hi : Int) : Int :=
  match c.prog with
  | .flip _ => max hi pos
  | _       => hi

omit [Tape T] in
theorem nextLo_le (c : Machine T) (pos lo : Int) : nextLo c pos lo ≤ lo := by
  unfold nextLo; cases c.prog <;> simp [Int.min_le_left]

omit [Tape T] in
theorem le_nextHi (c : Machine T) (pos hi : Int) : hi ≤ nextHi c pos hi := by
  unfold nextHi; cases c.prog <;> simp [Int.le_max_left]

theorem BoundedTape.step {c c' : Machine T} {pos lo hi : Int}
    (hs : c⇒ = some c') (hb : BoundedTape c.tape pos lo hi) :
    BoundedTape c'.tape (pos + c.δ) (nextLo c pos lo) (nextHi c pos hi) := by
  obtain ⟨t, p⟩ := c
  cases p with
  | nil | gap => cases hs
  | left =>
    cases hs
    intro i h
    show Tape.cells (Tape.moveL t) i = false
    rw [Tape.cells_moveL]
    exact hb (i - 1) (by simp only [δ, nextLo, nextHi] at h; omega)
  | right =>
    cases hs
    intro i h
    show Tape.cells (Tape.moveR t) i = false
    rw [Tape.cells_moveR]
    exact hb (i + 1) (by simp only [δ, nextLo, nextHi] at h; omega)
  | flip =>
    cases hs
    intro i h
    show Tape.cells (Tape.flip t) i = false
    simp only [δ, Int.add_zero, nextLo, nextHi] at h
    have hi0 : i ≠ 0 := by omega
    rw [Tape.cells_flip]
    simp only [hi0, ↓reduceIte]
    exact hb i (by omega)
  | loop =>
    cases hs
    intro i h
    exact hb i (by simp only [δ, Int.add_zero, nextLo, nextHi] at h; omega)

@[inline] def nextIds (m : Machine T) (ids : List Nat) : List Nat :=
  match m.prog with
  | .loop b _ => if Tape.cells m.tape 0 then ids.take b.numGaps ++ ids else ids.drop b.numGaps
  | _         => ids

end Machine

structure Frame (T : Type) where
  machine : Machine T
  pos     : Int

open scoped Machine in
/-- A verified execution prefix of `q` starting from `q.init T`, shared across deciders. -/
structure Trace (T : Type) [Tape T] (q : Program) where
  frames   : Array (Frame T)
  lo       : Int
  hi       : Int
  nonempty : 0 < frames.size
  init_eq  : frames[0]'nonempty = ⟨q.init T, 0⟩
  step_eq  : ∀ k (h : k + 1 < frames.size),
    let f := frames[k]'(Nat.lt_of_succ_lt h)
    f.machine⇒ = some (frames[k + 1]'h).machine ∧ (frames[k + 1]'h).pos = f.pos + f.machine.δ
  bounded  : ∀ k (h : k < frames.size),
    Machine.BoundedTape (frames[k]'h).machine.tape (frames[k]'h).pos lo hi

namespace Trace

open scoped Program Machine

variable {T : Type} [Tape T]

instance {q : Program} : Executable (Trace T q) where
  HaltsIn  _ k := q ⇓ k
  Diverges _   := q⇑

def init (T : Type) [Tape T] (q : Program) : Trace T q where
  frames   := #[⟨q.init T, 0⟩]
  lo       := 0
  hi       := 0
  nonempty := Nat.zero_lt_one
  init_eq  := rfl
  step_eq  := fun k h => absurd h (by simp)
  bounded  := fun k h => by
    have hk : k = 0 := by simp at h; omega
    subst hk
    exact Machine.boundedTape_blank

@[inline] def last {q : Program} (tr : Trace T q) : Frame T :=
  tr.frames[tr.frames.size - 1]'(Nat.sub_lt tr.nonempty Nat.zero_lt_one)

theorem reached {q : Program} (tr : Trace T q) :
    ∀ k (h : k < tr.frames.size), (q.init T) ⇒ k = some (tr.frames[k]'h).machine := by
  intro k
  induction k with
  | zero =>
    intro h
    simp [Machine.steps, tr.init_eq]
  | succ k ih =>
    intro h
    have hk : k < tr.frames.size := Nat.lt_of_succ_lt h
    have hstep := (tr.step_eq k h).1
    rw [Machine.steps_add, ih hk]
    simp [Machine.steps, hstep]

theorem steps_eq {q : Program} (tr : Trace T q) (k : Nat) :
    ∀ L (h : k + L < tr.frames.size),
      (tr.frames[k]'(by omega)).machine ⇒ L = some (tr.frames[k + L]'h).machine := by
  intro L
  induction L with
  | zero =>
    intro h
    rfl
  | succ L ih =>
    intro h
    have hL : k + L < tr.frames.size := by omega
    have hstep := (tr.step_eq (k + L) (by omega)).1
    rw [Machine.steps_add, ih hL]
    simp only [Machine.steps, hstep, Option.bind_some, Option.some.injEq]
    rfl

theorem disp_eq {q : Program} (tr : Trace T q) :
    ∀ L k (h : k + L < tr.frames.size),
      (tr.frames[k]'(by omega)).machine.disp L =
        (tr.frames[k + L]'h).pos - (tr.frames[k]'(by omega)).pos := by
  intro L
  induction L with
  | zero =>
    intro k h
    simp [Machine.disp]
  | succ L ih =>
    intro k h
    have h1 : k + 1 < tr.frames.size := by omega
    obtain ⟨hs, hp⟩ := tr.step_eq k h1
    have ih' := ih (k + 1) (by omega)
    have hp_eq : (tr.frames[k + 1 + L]'(by omega)).pos = (tr.frames[k + (L + 1)]'h).pos := by
      simp only [Nat.add_assoc, Nat.add_comm 1 L]
    simp only [Machine.disp, hs]
    rw [ih', hp_eq, hp]
    omega

theorem haltsIn_last {q : Program} (tr : Trace T q)
    (hp : tr.last.machine.prog = ε) : q ⇓ (tr.frames.size - 1) := by
  apply Program.haltsIn_of (T := T)
  have hr := tr.reached (tr.frames.size - 1) (Nat.sub_lt tr.nonempty Nat.zero_lt_one)
  refine ⟨tr.last.machine.tape, ?_⟩
  rw [hr]
  show some tr.last.machine = some ⟨tr.last.machine.tape, ε⟩
  cases h : tr.last.machine with
  | mk t p =>
    rw [h] at hp
    cases hp
    rfl

private structure Inv (q : Program) (frames : Array (Frame T)) (lo hi : Int) : Prop where
  nonempty : 0 < frames.size
  init_eq  : frames[0]'nonempty = ⟨q.init T, 0⟩
  step_eq  : ∀ k (h : k + 1 < frames.size),
    let f := frames[k]'(Nat.lt_of_succ_lt h)
    f.machine⇒ = some (frames[k + 1]'h).machine ∧ (frames[k + 1]'h).pos = f.pos + f.machine.δ
  bounded  : ∀ k (h : k < frames.size),
    Machine.BoundedTape (frames[k]'h).machine.tape (frames[k]'h).pos lo hi

@[specialize] def extendRaw :
    Nat → Array (Frame T) → Machine T → Int → Int → Int → Array (Frame T) × Int × Int
  | 0,        frames, _, _,   lo, hi => (frames, lo, hi)
  | fuel + 1, frames, m, pos, lo, hi =>
    match m⇒ with
    | none    => (frames, lo, hi)
    | some m' =>
      let pos' := pos + m.δ
      let lo'  := Machine.nextLo m pos lo
      let hi'  := Machine.nextHi m pos hi
      extendRaw fuel (frames.push ⟨m', pos'⟩) m' pos' lo' hi'

private theorem inv_push {q : Program} {frames : Array (Frame T)} {m m' : Machine T}
    {pos lo hi : Int}
    (hinv : Inv q frames lo hi)
    (hlast : frames[frames.size - 1]'(Nat.sub_lt hinv.nonempty Nat.zero_lt_one) = ⟨m, pos⟩)
    (hs : m⇒ = some m') :
    Inv q (frames.push ⟨m', pos + m.δ⟩) (Machine.nextLo m pos lo) (Machine.nextHi m pos hi) := by
  have hlo : Machine.nextLo m pos lo ≤ lo := Machine.nextLo_le m pos lo
  have hhi : hi ≤ Machine.nextHi m pos hi := Machine.le_nextHi m pos hi
  refine ⟨by simp, ?_, ?_, ?_⟩
  · rw [Array.getElem_push_lt hinv.nonempty]
    exact hinv.init_eq
  · intro k hk
    simp only [Array.size_push] at hk
    by_cases hlt : k + 1 < frames.size
    · rw [Array.getElem_push_lt (Nat.lt_of_succ_lt hlt), Array.getElem_push_lt hlt]
      exact hinv.step_eq k hlt
    · have hk_eq : k = frames.size - 1 := by omega
      have hk1_eq : k + 1 = frames.size := by omega
      have hfk : (frames.push ⟨m', pos + m.δ⟩)[k]'(by simp; omega) = ⟨m, pos⟩ := by
        rw [Array.getElem_push_lt (by omega)]
        simpa [hk_eq] using hlast
      have hfk1 : (frames.push ⟨m', pos + m.δ⟩)[k + 1]'(by simp; omega) = ⟨m', pos + m.δ⟩ := by
        simp [hk1_eq]
      dsimp only
      rw [hfk, hfk1]
      exact ⟨hs, rfl⟩
  · intro k hk
    simp only [Array.size_push] at hk
    by_cases hlt : k < frames.size
    · rw [Array.getElem_push_lt hlt]
      exact (hinv.bounded k hlt).mono hlo hhi
    · have hk_eq : k = frames.size := by omega
      have hfk : (frames.push ⟨m', pos + m.δ⟩)[k]'(by simp; omega) = ⟨m', pos + m.δ⟩ := by
        simp [hk_eq]
      rw [hfk]
      have hbm := hinv.bounded (frames.size - 1) (Nat.sub_lt hinv.nonempty Nat.zero_lt_one)
      rw [hlast] at hbm
      exact hbm.step hs

private theorem extendRaw_inv {q : Program} :
    ∀ (fuel : Nat) (frames : Array (Frame T)) (m : Machine T) (pos lo hi : Int),
      Inv q frames lo hi →
      (∀ h, frames[frames.size - 1]'h = ⟨m, pos⟩) →
      let r := extendRaw fuel frames m pos lo hi
      Inv q r.1 r.2.1 r.2.2
  | 0, _, _, _, _, _, hinv, _ => hinv
  | fuel + 1, frames, m, pos, lo, hi, hinv, hlast => by
    unfold extendRaw
    cases hs : m⇒ with
    | none => exact hinv
    | some m' =>
      apply extendRaw_inv fuel _ m' (pos + m.δ) (Machine.nextLo m pos lo) (Machine.nextHi m pos hi)
      · exact inv_push hinv (hlast _) hs
      · intro h
        simp [Array.size_push]

/-- Extend the trace up to step `target` (or until execution halts or hits a gap). -/
@[inline] def extend {q : Program} (target : Nat) (tr : Trace T q) : Trace T q :=
  if target < tr.frames.size then tr
  else
    let ⟨frames, lo, hi, hne, hinit, hstep, hbd⟩ := tr
    let last := frames[frames.size - 1]'(Nat.sub_lt hne Nat.zero_lt_one)
    let fuel := target + 1 - frames.size
    let hinv : Inv q frames lo hi := ⟨hne, hinit, hstep, hbd⟩
    let res := extendRaw fuel frames last.machine last.pos lo hi
    have hres : Inv q res.1 res.2.1 res.2.2 :=
      extendRaw_inv fuel frames last.machine last.pos lo hi hinv (fun _ => rfl)
    ⟨res.1, res.2.1, res.2.2, hres.nonempty, hres.init_eq, hres.step_eq, hres.bounded⟩

/-- Replay only `nextIds` along already-computed frames to find which gap of `q` was hit. -/
def trackIdsLoop (frames : Array (Frame T)) (idx : Nat) (ids : List Nat) : List Nat :=
  if h : idx + 1 < frames.size then
    trackIdsLoop frames (idx + 1) ((frames[idx]'(Nat.lt_of_succ_lt h)).machine.nextIds ids)
  else ids
termination_by frames.size - idx
decreasing_by omega

def stuckGap? {q : Program} (tr : Trace T q) : Option (Fin q.numGaps) :=
  match trackIdsLoop tr.frames 0 (List.range q.numGaps) with
  | i :: _ => if h : i < q.numGaps then some ⟨i, h⟩ else none
  | []     => none

end Trace

end Bf
