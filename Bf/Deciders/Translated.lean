import Bf.Deciders.Simulator

namespace Bf

namespace Machine

open scoped Machine

variable {T : Type} [Tape T]

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

end Machine

namespace Trace

open scoped Machine

variable {T : Type} [Tape T]

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

@[specialize] def checkTranslatedRight {q : Program} (tr : Trace T q) (k L : Nat) : Bool :=
  if h : 0 < L ∧ k + L < tr.frames.size then
    let f₁ := tr.frames[k]'(by omega)
    let f₂ := tr.frames[k + L]'h.2
    if f₁.pos ≤ f₂.pos then
      if f₁.machine.prog == f₂.machine.prog then
        let a := max (-(L : Int)) (tr.lo - f₂.pos)
        let b := tr.hi - f₁.pos
        cellsEqRange f₁.machine f₂.machine a (b + 1 - a).toNat
      else false
    else false
  else false

@[specialize] def checkTranslatedLeft {q : Program} (tr : Trace T q) (k L : Nat) : Bool :=
  if h : 0 < L ∧ k + L < tr.frames.size then
    let f₁ := tr.frames[k]'(by omega)
    let f₂ := tr.frames[k + L]'h.2
    if f₂.pos ≤ f₁.pos then
      if f₁.machine.prog == f₂.machine.prog then
        let a := tr.lo - f₁.pos
        let b := min (L : Int) (tr.hi - f₂.pos)
        cellsEqRange f₁.machine f₂.machine a (b + 1 - a).toNat
      else false
    else false
  else false

@[specialize] def checkTranslated {q : Program} (tr : Trace T q) (k L : Nat) : Bool :=
  checkTranslatedRight tr k L || checkTranslatedLeft tr k L

theorem diverges_of_checkTranslatedRight {q : Program} {tr : Trace T q} {k L : Nat}
    (hc : checkTranslatedRight tr k L = true) : q⇑ := by
  unfold checkTranslatedRight at hc
  split at hc
  · next h =>
    dsimp only at hc
    split at hc
    · next hpos =>
      split at hc
      · next hprog =>
        have hp : (tr.frames[k]'(by omega)).machine.prog = (tr.frames[k + L]'h.2).machine.prog :=
          beq_iff_eq.mp hprog
        have hreach := tr.reached k (by omega)
        have hsteps := tr.steps_eq k L h.2
        have hdisp  := tr.disp_eq L k h.2
        have hb₁    := tr.bounded k (by omega)
        have hb₂    := tr.bounded (k + L) h.2
        have heq    := cellsEqRange_true hc
        apply Program.diverges_of (T := T)
        refine Machine.diverges_of_steps hreach
          ((Machine.Translated.progress h.1).diverges ⟨_, hsteps, by omega, hp, ?_⟩)
        intro i hi
        by_cases hlt : i < tr.lo - (tr.frames[k + L]'h.2).pos
        · rw [hb₁ i (Or.inl (by omega)), hb₂ i (Or.inl (by omega))]
        · by_cases hgt : tr.hi - (tr.frames[k]'(by omega)).pos < i
          · rw [hb₁ i (Or.inr (by omega)), hb₂ i (Or.inr (by omega))]
          · exact heq i (by omega) (by omega)
      · cases hc
    · cases hc
  · cases hc

theorem diverges_of_checkTranslatedLeft {q : Program} {tr : Trace T q} {k L : Nat}
    (hc : checkTranslatedLeft tr k L = true) : q⇑ := by
  unfold checkTranslatedLeft at hc
  split at hc
  · next h =>
    dsimp only at hc
    split at hc
    · next hpos =>
      split at hc
      · next hprog =>
        have hp : (tr.frames[k]'(by omega)).machine.prog = (tr.frames[k + L]'h.2).machine.prog :=
          beq_iff_eq.mp hprog
        have hreach := tr.reached k (by omega)
        have hsteps := tr.steps_eq k L h.2
        have hdisp  := tr.disp_eq L k h.2
        have hb₁    := tr.bounded k (by omega)
        have hb₂    := tr.bounded (k + L) h.2
        have heq    := cellsEqRange_true hc
        apply Program.diverges_of (T := T)
        refine Machine.diverges_of_steps hreach
          ((Machine.TranslatedLeft.progress h.1).diverges ⟨_, hsteps, by omega, hp, ?_⟩)
        intro i hi
        by_cases hlt : i < tr.lo - (tr.frames[k]'(by omega)).pos
        · rw [hb₁ i (Or.inl (by omega)), hb₂ i (Or.inl (by omega))]
        · by_cases hgt : tr.hi - (tr.frames[k + L]'h.2).pos < i
          · rw [hb₁ i (Or.inr (by omega)), hb₂ i (Or.inr (by omega))]
          · exact heq i (by omega) (by omega)
      · cases hc
    · cases hc
  · cases hc

theorem diverges_of_checkTranslated {q : Program} {tr : Trace T q} {k L : Nat}
    (hc : checkTranslated tr k L = true) : q⇑ := by
  simp only [checkTranslated, Bool.or_eq_true] at hc
  rcases hc with hr | hl
  · exact diverges_of_checkTranslatedRight hr
  · exact diverges_of_checkTranslatedLeft hl

@[specialize] def checkTranslatedFrom {q : Program} (tr : Trace T q) (k lo hi : Nat) : Bool :=
  if lo ≤ hi then
    if checkTranslated tr k lo then true
    else checkTranslatedFrom tr k (lo + 1) hi
  else false
termination_by hi + 1 - lo

theorem diverges_of_checkTranslatedFrom {q : Program} {tr : Trace T q} {k lo hi : Nat} :
    checkTranslatedFrom tr k lo hi = true → q⇑ := by
  unfold checkTranslatedFrom
  split
  · split
    · next hc => intro _; exact diverges_of_checkTranslated hc
    · exact diverges_of_checkTranslatedFrom
  · intro h; cases h
termination_by hi + 1 - lo

end Trace

namespace Decider

variable {T : Type} [Tape T]

def translated (k L : Nat) : Decider T := fun _ tr =>
  match tr.advance (k + L) with
  | .unknown tr' =>
    if h : tr'.checkTranslated k L then .diverges (Trace.diverges_of_checkTranslated h)
    else .unknown tr'
  | v => v

def translatedUpTo (k maxL : Nat) : Decider T := fun _ tr =>
  match tr.advance (k + maxL) with
  | .unknown tr' =>
    if h : tr'.checkTranslatedFrom k 1 maxL then
      .diverges (Trace.diverges_of_checkTranslatedFrom h)
    else .unknown tr'
  | v => v

end Decider

end Bf
