import Bf.Simulation
import Bf.Deciders.Mirror

namespace Bf

namespace Tape

def ZeroBeyond (t : Tape) (r : Nat) : Prop :=
  ∀ i : Int, (r : Int) < i ∨ i < -(r : Int) → t.cells i = false

theorem zeroBeyond_blank : blank.ZeroBeyond 0 :=
  fun (_ : Int) (_ : ((0 : Nat) : Int) < _ ∨ _ < -((0 : Nat) : Int)) => rfl

theorem ZeroBeyond.mono {t : Tape} {r r' : Nat} (h : t.ZeroBeyond r) (hr : r ≤ r') :
    t.ZeroBeyond r' :=
  fun (i : Int) (hi : (r' : Int) < i ∨ i < -(r' : Int)) => h i (by omega)

end Tape

namespace Config

theorem zeroBeyond_step {c c' : Config} {r : Nat} (hs : c.step = some c')
    (h : c.tape.ZeroBeyond r) : c'.tape.ZeroBeyond (r + 1) := by
  obtain ⟨t, p⟩ := c
  cases p with
  | nil => cases hs
  | left => cases hs; intro i hi; exact h (i - 1) (by omega)
  | right => cases hs; intro i hi; exact h (i + 1) (by omega)
  | flip =>
    cases hs; intro i hi
    show (if i = 0 then _ else t.cells i) = false
    have hi0 : i ≠ 0 := by omega
    simp only [hi0, ↓reduceIte]; exact h i (by omega)
  | loop => cases hs; exact h.mono (by omega)

theorem zeroBeyond_steps {c c' : Config} {r k : Nat} (hs : c.steps k = some c')
    (h : c.tape.ZeroBeyond r) : c'.tape.ZeroBeyond (r + k) := by
  induction k generalizing c r with
  | zero => cases hs; exact h
  | succ k ih =>
    simp only [steps] at hs
    cases h₁ : c.step with
    | none => rw [h₁] at hs; cases hs
    | some d =>
      rw [h₁, Option.bind_some] at hs
      have := ih hs (zeroBeyond_step h₁ h)
      rwa [Nat.add_assoc, Nat.add_comm 1 k] at this

def δ (c : Config) : Int :=
  match c.prog with
  | .left _  => -1
  | .right _ => 1
  | _        => 0

def disp : Nat → Config → Int
  | 0,     _ => 0
  | n + 1, c => match c.step with
    | none    => 0
    | some c' => c.δ + disp n c'

def Agree (lo : Int) (c d : Config) : Prop :=
  c.prog = d.prog ∧ ∀ i : Int, lo ≤ i → c.tape.cells i = d.tape.cells i

theorem Agree.mono {lo lo' : Int} {c d : Config} (h : Agree lo' c d) (hl : lo' ≤ lo) :
    Agree lo c d :=
  ⟨h.1, fun (i : Int) (hi : lo ≤ i) => h.2 i (by omega)⟩

theorem Agree.step {lo : Int} {c d : Config} (h : Agree lo c d) (hlo : lo ≤ 0) :
    (c.step = none ∧ d.step = none) ∨
      ∃ c' d' : Config, c.step = some c' ∧ d.step = some d' ∧ Agree (lo - c.δ) c' d' := by
  obtain ⟨t, p⟩ := c
  obtain ⟨u, q⟩ := d
  obtain ⟨hp, hc⟩ := h
  dsimp only at hp hc
  subst hp
  cases p with
  | nil => exact .inl ⟨rfl, rfl⟩
  | left =>
    exact .inr ⟨_, _, rfl, rfl, rfl,
      fun (i : Int) (hi : _ ≤ i) => hc (i - 1) (by simp only [δ] at hi; omega)⟩
  | right =>
    exact .inr ⟨_, _, rfl, rfl, rfl,
      fun (i : Int) (hi : _ ≤ i) => hc (i + 1) (by simp only [δ] at hi; omega)⟩
  | flip =>
    refine .inr ⟨_, _, rfl, rfl, rfl, fun (i : Int) (hi : _ ≤ i) => ?_⟩
    simp only [δ, Int.sub_zero] at hi
    show (if i = 0 then !t.cells 0 else t.cells i) = (if i = 0 then !u.cells 0 else u.cells i)
    rw [hc 0 hlo, hc i hi]
  | loop b p =>
    have e : t.head = u.head := hc 0 hlo
    refine .inr ⟨_, _, rfl, rfl, ?_, fun (i : Int) (hi : _ ≤ i) => hc i (by simp only [δ] at hi; omega)⟩
    show (if t.head then _ else _) = (if u.head then _ else _)
    rw [e]

theorem Agree.steps (s : Nat) {lo : Int} {c d c' : Config} (h : Agree lo c d)
    (hlo : lo + s ≤ 0) (hs : c.steps s = some c') :
    ∃ d' : Config, d.steps s = some d' ∧ Agree (lo - c.disp s) c' d' ∧ c.disp s = d.disp s := by
  induction s generalizing lo c d with
  | zero =>
    cases hs
    exact ⟨d, rfl, by simpa [disp] using h, rfl⟩
  | succ s ih =>
    have hδ : c.δ = d.δ := by unfold δ; rw [h.1]
    rcases h.step (by omega) with ⟨h₁, -⟩ | ⟨c₁, d₁, h₁, h₂, h'⟩
    · simp [Config.steps, h₁] at hs
    · simp only [Config.steps, h₁, Option.bind_some] at hs
      have hb : -1 ≤ c.δ := by unfold δ; split <;> omega
      obtain ⟨d', hd', ha, he⟩ := ih h' (by omega) hs
      refine ⟨d', by simp [Config.steps, h₂, hd'], ?_, ?_⟩
      · simp only [disp, h₁]
        exact ha.mono (by omega)
      · simp only [disp, h₁, h₂, he, hδ]

def Translated (L : Nat) (c : Config) : Prop :=
  ∃ c' : Config, c.steps L = some c' ∧ 0 ≤ c.disp L ∧ Agree (-L) c c'

theorem Translated.progress {L : Nat} (hL : 0 < L) : Progress (Translated L) := by
  rintro c ⟨c₂, hs, hd, ha⟩
  obtain ⟨c₃, h₃, ha₃, he⟩ := ha.steps L (by omega) hs
  exact ⟨L, c₂, hL, hs, c₃, h₃, by rw [← he]; exact hd, ha₃.mono (by omega)⟩

def isTranslated (k L : Nat) (c : Config) : Bool :=
  match c.steps k with
  | none => false
  | some c₁ =>
    match c₁.steps L with
    | none => false
    | some c₂ =>
      0 < L && decide (0 ≤ c₁.disp L) && c₁.prog == c₂.prog &&
        (List.range (k + 2 * L + 1)).all fun (j : Nat) =>
          c₁.tape.cells ((j : Int) - L) == c₂.tape.cells ((j : Int) - L)

theorem not_halts_of_isTranslated {k L : Nat} {c : Config} (hz : c.tape.ZeroBeyond 0)
    (h : c.isTranslated k L = true) : ¬ c.Halts := by
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
      refine not_halts_of_steps h₁ ((Translated.progress hL).not_halts ⟨c₂, h₂, hd, hp, ?_⟩)
      intro (i : Int) (hi : -(L : Int) ≤ i)
      by_cases hik : i ≤ k + L
      · have := hw (i + L).toNat (by omega)
        rwa [Int.toNat_of_nonneg (by omega), Int.add_sub_cancel] at this
      · rw [z₁ i (by omega), z₂ i (by omega)]

end Config

namespace Decider

def translatedRight (k L : Nat) : Decider where
  run := fun (p : Program) => if p.init.isTranslated k L then .nonhalts else .unknown
  sound := fun (p : Program) => by
    by_cases h : p.init.isTranslated k L
    · simp only [h, ↓reduceIte]
      exact Config.not_halts_of_isTranslated Tape.zeroBeyond_blank h
    · simp only [h]; trivial

def translated (k L : Nat) : Decider :=
  translatedRight k L <|> (translatedRight k L).mirror

def translatedUpTo (k L : Nat) : Decider :=
  any ((List.range L).map fun (n : Nat) => translated k (n + 1))

end Decider

end Bf
