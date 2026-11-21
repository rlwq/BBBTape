import Bf.Core.Decider
import Bf.Tapes.Zipper

namespace Bf

namespace Machine

open scoped Machine

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

theorem disp_add {c c₁ : Machine T} {a : Nat} (h : c ⇒ a = some c₁) (b : Nat) :
    c.disp (a + b) = c.disp a + c₁.disp b := by
  induction a generalizing c with
  | zero => cases h; simp [disp]
  | succ a ih =>
    simp only [steps] at h
    cases hs : c⇒ with
    | none => simp [hs] at h
    | some c' =>
      simp only [hs, Option.bind_some] at h
      rw [Nat.succ_add]
      simp only [disp, hs, ih h, Int.add_assoc]

/-- Every cell outside the absolute interval `[lo, hi]` is `false` (relative to head at `pos`). -/
def BoundedTape (t : T) (pos lo hi : Int) : Prop :=
  ∀ i : Int, pos + i < lo ∨ hi < pos + i → Tape.cells t i = false

theorem boundedTape_blank : BoundedTape (Tape.blank : T) 0 0 0 :=
  fun i _ => Tape.cells_blank i

theorem BoundedTape.mono {t : T} {pos lo lo' hi hi' : Int}
    (h : BoundedTape t pos lo hi) (hlo : lo' ≤ lo) (hhi : hi ≤ hi') :
    BoundedTape t pos lo' hi' :=
  fun i h' => h i (by omega)

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

def Agree (lo : Int) (c d : Machine T) : Prop :=
  c.prog = d.prog ∧ ∀ i : Int, lo ≤ i → Tape.cells c.tape i = Tape.cells d.tape i

theorem Agree.mono {lo lo' : Int} {c d : Machine T} (h : Agree lo' c d) (hl : lo' ≤ lo) :
    Agree lo c d :=
  ⟨h.1, fun (i : Int) (hi : lo ≤ i) => h.2 i (by omega)⟩

theorem Agree.step {lo : Int} {c d : Machine T} (h : Agree lo c d) (hlo : lo ≤ 0) :
    (c⇒ = none ∧ d⇒ = none) ∨
      ∃ c' d' : Machine T, c⇒ = some c' ∧ d⇒ = some d' ∧ Agree (lo - c.δ) c' d' := by
  obtain ⟨t, p⟩ := c
  obtain ⟨u, q⟩ := d
  obtain ⟨hp, hc⟩ := h
  dsimp only at hp hc
  subst hp
  cases p with
  | nil => exact .inl ⟨rfl, rfl⟩
  | gap => exact .inl ⟨rfl, rfl⟩
  | left =>
    refine .inr ⟨_, _, rfl, rfl, rfl, fun (i : Int) (hi : _ ≤ i) => ?_⟩
    show Tape.cells (Tape.moveL t) i = Tape.cells (Tape.moveL u) i
    rw [Tape.cells_moveL, Tape.cells_moveL]
    exact hc (i - 1) (by simp only [δ] at hi; omega)
  | right =>
    refine .inr ⟨_, _, rfl, rfl, rfl, fun (i : Int) (hi : _ ≤ i) => ?_⟩
    show Tape.cells (Tape.moveR t) i = Tape.cells (Tape.moveR u) i
    rw [Tape.cells_moveR, Tape.cells_moveR]
    exact hc (i + 1) (by simp only [δ] at hi; omega)
  | flip =>
    refine .inr ⟨_, _, rfl, rfl, rfl, fun (i : Int) (hi : _ ≤ i) => ?_⟩
    simp only [δ, Int.sub_zero] at hi
    show Tape.cells (Tape.flip t) i = Tape.cells (Tape.flip u) i
    rw [Tape.cells_flip, Tape.cells_flip, hc 0 hlo, hc i hi]
  | loop b p =>
    have e : Tape.cells t 0 = Tape.cells u 0 := hc 0 hlo
    refine .inr ⟨_, _, rfl, rfl, ?_,
      fun (i : Int) (hi : _ ≤ i) => hc i (by simp only [δ] at hi; omega)⟩
    show (if Tape.cells t 0 then _ else _) = (if Tape.cells u 0 then _ else _)
    rw [e]

theorem Agree.steps (s : Nat) {lo : Int} {c d c' : Machine T} (h : Agree lo c d)
    (hlo : lo + s ≤ 0) (hs : c ⇒ s = some c') :
    ∃ d' : Machine T, d ⇒ s = some d' ∧ Agree (lo - c.disp s) c' d' ∧ c.disp s = d.disp s := by
  induction s generalizing lo c d with
  | zero =>
    cases hs
    exact ⟨d, rfl, by simpa [disp] using h, rfl⟩
  | succ s ih =>
    have hδ : c.δ = d.δ := by
      unfold δ
      rw [h.1]
    rcases h.step (by omega) with ⟨h₁, -⟩ | ⟨c₁, d₁, h₁, h₂, h'⟩
    · simp [Machine.steps, h₁] at hs
    · simp only [Machine.steps, h₁, Option.bind_some] at hs
      have hb : -1 ≤ c.δ := by
        unfold δ
        split <;> omega
      obtain ⟨d', hd', ha, he⟩ := ih h' (by omega) hs
      refine ⟨d', by simp [Machine.steps, h₂, hd'], ?_, ?_⟩
      · simp only [disp, h₁]
        exact ha.mono (by omega)
      · simp only [disp, h₁, h₂, he, hδ]

def Translated (L : Nat) (c : Machine T) : Prop :=
  ∃ c' : Machine T, c ⇒ L = some c' ∧ 0 ≤ c.disp L ∧ Agree (-L) c c'

theorem Translated.progress {L : Nat} (hL : 0 < L) : Progress (Translated (T := T) L) := by
  rintro c ⟨c₂, hs, hd, ha⟩
  obtain ⟨c₃, h₃, ha₃, he⟩ := ha.steps L (by omega) hs
  exact ⟨L, c₂, hL, hs, c₃, h₃, by rw [← he]; exact hd, ha₃.mono (by omega)⟩

def AgreeLeft (hi : Int) (c d : Machine T) : Prop :=
  c.prog = d.prog ∧ ∀ i : Int, i ≤ hi → Tape.cells c.tape i = Tape.cells d.tape i

theorem AgreeLeft.mono {hi hi' : Int} {c d : Machine T} (h : AgreeLeft hi' c d) (hl : hi ≤ hi') :
    AgreeLeft hi c d :=
  ⟨h.1, fun (i : Int) (h' : i ≤ hi) => h.2 i (by omega)⟩

theorem AgreeLeft.step {hi : Int} {c d : Machine T} (h : AgreeLeft hi c d) (hhi : 0 ≤ hi) :
    (c⇒ = none ∧ d⇒ = none) ∨
      ∃ c' d' : Machine T, c⇒ = some c' ∧ d⇒ = some d' ∧ AgreeLeft (hi - c.δ) c' d' := by
  obtain ⟨t, p⟩ := c
  obtain ⟨u, q⟩ := d
  obtain ⟨hp, hc⟩ := h
  dsimp only at hp hc
  subst hp
  cases p with
  | nil => exact .inl ⟨rfl, rfl⟩
  | gap => exact .inl ⟨rfl, rfl⟩
  | left =>
    refine .inr ⟨_, _, rfl, rfl, rfl, fun (i : Int) (h' : i ≤ _) => ?_⟩
    show Tape.cells (Tape.moveL t) i = Tape.cells (Tape.moveL u) i
    rw [Tape.cells_moveL, Tape.cells_moveL]
    exact hc (i - 1) (by simp only [δ] at h'; omega)
  | right =>
    refine .inr ⟨_, _, rfl, rfl, rfl, fun (i : Int) (h' : i ≤ _) => ?_⟩
    show Tape.cells (Tape.moveR t) i = Tape.cells (Tape.moveR u) i
    rw [Tape.cells_moveR, Tape.cells_moveR]
    exact hc (i + 1) (by simp only [δ] at h'; omega)
  | flip =>
    refine .inr ⟨_, _, rfl, rfl, rfl, fun (i : Int) (h' : i ≤ _) => ?_⟩
    simp only [δ, Int.sub_zero] at h'
    show Tape.cells (Tape.flip t) i = Tape.cells (Tape.flip u) i
    rw [Tape.cells_flip, Tape.cells_flip, hc 0 hhi, hc i h']
  | loop b p =>
    have e : Tape.cells t 0 = Tape.cells u 0 := hc 0 hhi
    refine .inr ⟨_, _, rfl, rfl, ?_,
      fun (i : Int) (h' : i ≤ _) => hc i (by simp only [δ] at h'; omega)⟩
    show (if Tape.cells t 0 then _ else _) = (if Tape.cells u 0 then _ else _)
    rw [e]

theorem AgreeLeft.steps (s : Nat) {hi : Int} {c d c' : Machine T} (h : AgreeLeft hi c d)
    (hhi : (s : Int) ≤ hi) (hs : c ⇒ s = some c') :
    ∃ d' : Machine T, d ⇒ s = some d' ∧ AgreeLeft (hi - c.disp s) c' d' ∧ c.disp s = d.disp s := by
  induction s generalizing hi c d with
  | zero =>
    cases hs
    exact ⟨d, rfl, by simpa [disp] using h, rfl⟩
  | succ s ih =>
    have hδ : c.δ = d.δ := by
      unfold δ
      rw [h.1]
    rcases h.step (by omega) with ⟨h₁, -⟩ | ⟨c₁, d₁, h₁, h₂, h'⟩
    · simp [Machine.steps, h₁] at hs
    · simp only [Machine.steps, h₁, Option.bind_some] at hs
      have hb : c.δ ≤ 1 := by
        unfold δ
        split <;> omega
      obtain ⟨d', hd', ha, he⟩ := ih h' (by omega) hs
      refine ⟨d', by simp [Machine.steps, h₂, hd'], ?_, ?_⟩
      · simp only [disp, h₁]
        exact ha.mono (by omega)
      · simp only [disp, h₁, h₂, he, hδ]

def TranslatedLeft (L : Nat) (c : Machine T) : Prop :=
  ∃ c' : Machine T, c ⇒ L = some c' ∧ c.disp L ≤ 0 ∧ AgreeLeft L c c'

theorem TranslatedLeft.progress {L : Nat} (hL : 0 < L) : Progress (TranslatedLeft (T := T) L) := by
  rintro c ⟨c₂, hs, hd, ha⟩
  obtain ⟨c₃, h₃, ha₃, he⟩ := ha.steps L (by omega) hs
  exact ⟨L, c₂, hL, hs, c₃, h₃, by rw [← he]; exact hd, ha₃.mono (by omega)⟩

@[specialize] def cellsEqRange (c₁ c₂ : Machine T) (start : Int) : Nat → Bool
  | 0     => true
  | n + 1 =>
    (Tape.cells c₁.tape (start + n) == Tape.cells c₂.tape (start + n)) &&
      cellsEqRange c₁ c₂ start n

theorem cellsEqRange_true {c₁ c₂ : Machine T} {start : Int} {n : Nat} :
    cellsEqRange c₁ c₂ start n = true →
    ∀ i : Int, start ≤ i → i < start + n → Tape.cells c₁.tape i = Tape.cells c₂.tape i := by
  induction n with
  | zero => intro _ i h₁ h₂; omega
  | succ n ih =>
    intro h i h₁ h₂
    simp only [cellsEqRange, Bool.and_eq_true, beq_iff_eq] at h
    by_cases hi : i = start + n
    · rw [hi]; exact h.1
    · exact ih h.2 i h₁ (by omega)

@[specialize] def matchRight (c₁ : Machine T) (pos₁ : Int) (c₂ : Machine T) (pos₂ lo hi : Int)
    (L : Nat) : Bool :=
  if pos₁ ≤ pos₂ then
    let a := max (-(L : Int)) (lo - pos₂)
    let b := hi - pos₁
    cellsEqRange c₁ c₂ a (b + 1 - a).toNat
  else false

@[specialize] def matchLeft (c₁ : Machine T) (pos₁ : Int) (c₂ : Machine T) (pos₂ lo hi : Int)
    (L : Nat) : Bool :=
  if pos₂ ≤ pos₁ then
    let a := lo - pos₁
    let b := min (L : Int) (hi - pos₂)
    cellsEqRange c₁ c₂ a (b + 1 - a).toNat
  else false

@[specialize] def matchTranslated (c₁ : Machine T) (pos₁ : Int) (c₂ : Machine T) (pos₂ lo hi : Int)
    (L : Nat) : Bool :=
  if c₁.prog == c₂.prog then
    matchRight c₁ pos₁ c₂ pos₂ lo hi L || matchLeft c₁ pos₁ c₂ pos₂ lo hi L
  else false

theorem diverges_of_matchTranslated {c₁ c₂ : Machine T} {pos₁ pos₂ lo hi : Int} {L : Nat}
    (hL : 0 < L)
    (hs : c₁ ⇒ L = some c₂)
    (hd : c₁.disp L = pos₂ - pos₁)
    (hb₁ : BoundedTape c₁.tape pos₁ lo hi)
    (hb₂ : BoundedTape c₂.tape pos₂ lo hi)
    (hm : matchTranslated c₁ pos₁ c₂ pos₂ lo hi L = true) : c₁⇑ := by
  unfold matchTranslated at hm
  split at hm
  · next hprog =>
    have hp : c₁.prog = c₂.prog := beq_iff_eq.mp hprog
    simp only [Bool.or_eq_true] at hm
    rcases hm with hr | hl
    · unfold matchRight at hr
      split at hr
      · next hpos =>
        have heq := cellsEqRange_true hr
        refine (Translated.progress hL).diverges ⟨c₂, hs, by omega, hp, ?_⟩
        intro i hi'
        by_cases hlt : i < lo - pos₂
        · rw [hb₁ i (Or.inl (by omega)), hb₂ i (Or.inl (by omega))]
        · by_cases hgt : hi - pos₁ < i
          · rw [hb₁ i (Or.inr (by omega)), hb₂ i (Or.inr (by omega))]
          · exact heq i (by omega) (by omega)
      · cases hr
    · unfold matchLeft at hl
      split at hl
      · next hpos =>
        have heq := cellsEqRange_true hl
        refine (TranslatedLeft.progress hL).diverges ⟨c₂, hs, by omega, hp, ?_⟩
        intro i hi'
        by_cases hlt : i < lo - pos₁
        · rw [hb₁ i (Or.inl (by omega)), hb₂ i (Or.inl (by omega))]
        · by_cases hgt : hi - pos₂ < i
          · rw [hb₁ i (Or.inr (by omega)), hb₂ i (Or.inr (by omega))]
          · exact heq i (by omega) (by omega)
      · cases hl
  · cases hm

@[specialize] def simTo (c : Machine T) (pos lo hi : Int) :
    Nat → Option (Machine T × Int × Int × Int)
  | 0     => some (c, pos, lo, hi)
  | n + 1 =>
    match c⇒ with
    | none    => none
    | some c' => simTo c' (pos + c.δ) (nextLo c pos lo) (nextHi c pos hi) n

theorem simTo_sound :
    ∀ {n : Nat} {c c' : Machine T} {pos lo hi pos' lo' hi' : Int},
      BoundedTape c.tape pos lo hi →
      simTo c pos lo hi n = some (c', pos', lo', hi') →
      c ⇒ n = some c' ∧ BoundedTape c'.tape pos' lo' hi'
  | 0, _, _, _, _, _, _, _, _, hb, h => by
    cases h; exact ⟨rfl, hb⟩
  | n + 1, c, c', pos, lo, hi, pos', lo', hi', hb, h => by
    unfold simTo at h
    cases hs : c⇒ with
    | none => simp [hs] at h
    | some c₁ =>
      simp only [hs] at h
      obtain ⟨hsteps, hb'⟩ := simTo_sound (hb.step hs) h
      exact ⟨by simp [steps, hs, hsteps], hb'⟩

@[specialize] def scanLoop (c₁ : Machine T) (pos₁ : Int) (minL : Nat) :
    Nat → Nat → Machine T → Int → Int → Int → Bool
  | 0,       _, _,  _,    _,  _  => false
  | rem + 1, L, c₂, pos₂, lo, hi =>
    match c₂⇒ with
    | none     => false
    | some c₂' =>
      let L'    := L + 1
      let pos₂' := pos₂ + c₂.δ
      let lo'   := nextLo c₂ pos₂ lo
      let hi'   := nextHi c₂ pos₂ hi
      if minL ≤ L' && matchTranslated c₁ pos₁ c₂' pos₂' lo' hi' L' then true
      else scanLoop c₁ pos₁ minL rem L' c₂' pos₂' lo' hi'

theorem scanLoop_sound :
    ∀ {rem L minL : Nat} {c₁ c₂ : Machine T} {pos₁ pos₂ lo hi : Int},
      c₁ ⇒ L = some c₂ →
      c₁.disp L = pos₂ - pos₁ →
      BoundedTape c₁.tape pos₁ lo hi →
      BoundedTape c₂.tape pos₂ lo hi →
      scanLoop c₁ pos₁ minL rem L c₂ pos₂ lo hi = true →
      c₁⇑
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, h => by cases h
  | rem + 1, L, minL, c₁, c₂, pos₁, pos₂, lo, hi, hs, hd, hb₁, hb₂, h => by
    unfold scanLoop at h
    cases hstep : c₂⇒ with
    | none => simp [hstep] at h
    | some c₂' =>
      simp only [hstep] at h
      have hs' : c₁ ⇒ (L + 1) = some c₂' := by
        rw [steps_add, hs]; simp [steps, hstep]
      have hd' : c₁.disp (L + 1) = pos₂ + c₂.δ - pos₁ := by
        rw [disp_add hs 1]
        simp only [disp, hstep, Int.add_zero]
        omega
      have hb₁' : BoundedTape c₁.tape pos₁ (nextLo c₂ pos₂ lo) (nextHi c₂ pos₂ hi) :=
        hb₁.mono (nextLo_le c₂ pos₂ lo) (le_nextHi c₂ pos₂ hi)
      have hb₂' : BoundedTape c₂'.tape (pos₂ + c₂.δ) (nextLo c₂ pos₂ lo) (nextHi c₂ pos₂ hi) :=
        hb₂.step hstep
      split at h
      · next hcond =>
        simp only [Bool.and_eq_true] at hcond
        exact diverges_of_matchTranslated (Nat.succ_pos L) hs' hd' hb₁' hb₂' hcond.2
      · exact scanLoop_sound hs' hd' hb₁' hb₂' h

/-- Single-pass check for translated cycles starting at step `k` with periods in `[minL, maxL]`,
covering both left and right shifts without running the mirror program. -/
@[specialize] def isTranslatedRange (k minL maxL : Nat) (c : Machine T) : Bool :=
  match simTo c 0 0 0 k with
  | none => false
  | some (c₁, pos₁, lo, hi) => scanLoop c₁ pos₁ minL maxL 0 c₁ pos₁ lo hi

theorem diverges_of_isTranslatedRange {k minL maxL : Nat} {c : Machine T}
    (hb : BoundedTape c.tape 0 0 0) (h : c.isTranslatedRange k minL maxL = true) : c⇑ := by
  unfold isTranslatedRange at h
  split at h
  · cases h
  · next c₁ pos₁ lo hi hsim =>
    obtain ⟨hsteps, hb₁⟩ := simTo_sound hb hsim
    exact diverges_of_steps hsteps (scanLoop_sound rfl (by simp [disp]) hb₁ hb₁ h)

end Machine

namespace Decider

def translated (k L : Nat) : Decider := fun q =>
  if h : (q.init Zipper).isTranslatedRange k L L then
    .diverges (Program.diverges_of (Machine.diverges_of_isTranslatedRange Machine.boundedTape_blank h))
  else .unknown

def translatedUpTo (k maxL : Nat) : Decider := fun q =>
  if h : (q.init Zipper).isTranslatedRange k 1 maxL then
    .diverges (Program.diverges_of (Machine.diverges_of_isTranslatedRange Machine.boundedTape_blank h))
  else .unknown

end Decider

end Bf
