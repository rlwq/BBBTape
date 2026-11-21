import Bf.Core.Decider
import Bf.Tapes.Zipper

namespace Bf

namespace Machine

open scoped Machine

variable {T : Type} [Tape T]

def ZeroBeyond (t : T) (r : Nat) : Prop :=
  ∀ i : Int, (r : Int) < i ∨ i < -(r : Int) → Tape.cells t i = false

theorem zeroBeyond_blank : ZeroBeyond (Tape.blank : T) 0 :=
  fun (i : Int) (_ : ((0 : Nat) : Int) < i ∨ i < -((0 : Nat) : Int)) => Tape.cells_blank i

theorem ZeroBeyond.mono {t : T} {r r' : Nat} (h : ZeroBeyond t r) (hr : r ≤ r') :
    ZeroBeyond t r' :=
  fun (i : Int) (hi : (r' : Int) < i ∨ i < -(r' : Int)) => h i (by omega)

theorem zeroBeyond_step {c c' : Machine T} {r : Nat} (hs : c⇒ = some c')
    (h : ZeroBeyond c.tape r) : ZeroBeyond c'.tape (r + 1) := by
  obtain ⟨t, p⟩ := c
  cases p with
  | nil | gap => cases hs
  | left =>
    cases hs
    intro i hi
    show Tape.cells (Tape.moveL t) i = false
    rw [Tape.cells_moveL]
    exact h (i - 1) (by omega)
  | right =>
    cases hs
    intro i hi
    show Tape.cells (Tape.moveR t) i = false
    rw [Tape.cells_moveR]
    exact h (i + 1) (by omega)
  | flip =>
    cases hs
    intro i hi
    show Tape.cells (Tape.flip t) i = false
    have hi0 : i ≠ 0 := by omega
    rw [Tape.cells_flip]
    simp only [hi0, ↓reduceIte]
    exact h i (by omega)
  | loop =>
    cases hs
    exact ZeroBeyond.mono h (by omega)

theorem zeroBeyond_steps {c c' : Machine T} {r k : Nat} :
    c ⇒ k = some c' → ZeroBeyond c.tape r → ZeroBeyond c'.tape (r + k) := by
  intro hs h
  induction k generalizing c r with
  | zero =>
    cases hs
    exact h
  | succ k ih =>
    simp only [steps] at hs
    cases h₁ : c⇒ with
    | none =>
      rw [h₁] at hs
      cases hs
    | some d =>
      rw [h₁, Option.bind_some] at hs
      have := ih hs (zeroBeyond_step h₁ h)
      rwa [Nat.add_assoc, Nat.add_comm 1 k] at this

def δ (c : Machine T) : Int :=
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

@[specialize] def isTranslated (k L : Nat) (c : Machine T) : Bool :=
  match c ⇒ k with
  | none => false
  | some c₁ =>
    match c₁ ⇒ L with
    | none => false
    | some c₂ =>
      0 < L && decide (0 ≤ c₁.disp L) && c₁.prog == c₂.prog &&
        (List.range (k + 2 * L + 1)).all fun (j : Nat) =>
          Tape.cells c₁.tape ((j : Int) - L) == Tape.cells c₂.tape ((j : Int) - L)

theorem diverges_of_isTranslated {k L : Nat} {c : Machine T} (hz : ZeroBeyond c.tape 0)
    (h : c.isTranslated k L = true) : c⇑ := by
  unfold isTranslated at h
  split at h
  · cases h
  · next c₁ h₁ =>
    split at h
    · cases h
    · next c₂ h₂ =>
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
        List.mem_range] at h
      obtain ⟨⟨⟨hL, hd⟩, hp⟩, hw⟩ := h
      have z₁ := zeroBeyond_steps h₁ hz
      have z₂ := zeroBeyond_steps h₂ z₁
      refine diverges_of_steps h₁ ((Translated.progress hL).diverges ⟨c₂, h₂, hd, hp, ?_⟩)
      intro (i : Int) (hi : -(L : Int) ≤ i)
      by_cases hik : i ≤ k + L
      · have := hw (i + L).toNat (by omega)
        rwa [Int.toNat_of_nonneg (by omega), Int.add_sub_cancel] at this
      · rw [z₁ i (by omega), z₂ i (by omega)]

end Machine

namespace Decider

def translatedRight (k L : Nat) : Decider := fun q =>
  if h : (q.init Zipper).isTranslated k L then
    .diverges (Program.diverges_of (Machine.diverges_of_isTranslated Machine.zeroBeyond_blank h))
  else .unknown

def translated (k L : Nat) : Decider :=
  translatedRight k L <|> (translatedRight k L).mirror

def translatedUpTo (k L : Nat) : Decider :=
  any ((List.range L).map fun (n : Nat) => translated k (n + 1))

end Decider

end Bf
