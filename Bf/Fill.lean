import Bf.Simulation

namespace Bf

namespace Program

inductive Refines : Program → Program → Prop
  | nil : Refines nil nil
  | left {q p : Program} : Refines q p → Refines (left q) (left p)
  | right {q p : Program} : Refines q p → Refines (right q) (right p)
  | flip {q p : Program} : Refines q p → Refines (flip q) (flip p)
  | loop {b b' q p : Program} : Refines b b' → Refines q p → Refines (loop b q) (loop b' p)
  | hole (i k : Nat) (p : Program) : Refines (hole i k) p

inductive Fills : Program → Program → Prop
  | nil : Fills nil nil
  | left {q p : Program} : Fills q p → Fills (left q) (left p)
  | right {q p : Program} : Fills q p → Fills (right q) (right p)
  | flip {q p : Program} : Fills q p → Fills (flip q) (flip p)
  | loop {b b' q p : Program} : Fills b b' → Fills q p → Fills (loop b q) (loop b' p)
  | hole (i : Nat) {k : Nat} {p : Program} : p.Closed → p.size = k → Fills (hole i k) p

theorem Fills.refines {q p : Program} (h : Fills q p) : Refines q p := by
  induction h with
  | nil => exact .nil
  | left _ ih => exact .left ih
  | right _ ih => exact .right ih
  | flip _ ih => exact .flip ih
  | loop _ _ ihb ih => exact .loop ihb ih
  | hole i _ _ => exact .hole i _ _

theorem Fills.closed {q p : Program} (h : Fills q p) : p.Closed := by
  induction h with
  | nil => trivial
  | left _ ih | right _ ih | flip _ ih => exact ih
  | loop _ _ ihb ih => exact ⟨ihb, ih⟩
  | hole _ hc _ => exact hc

theorem Fills.size {q p : Program} (h : Fills q p) : p.size = q.size := by
  induction h with
  | nil => rfl
  | left _ ih | right _ ih | flip _ ih => simp [Program.size, ih]
  | loop _ _ ihb ih => simp [Program.size, ihb, ih]
  | hole _ _ hs => exact hs

def fill : Program → Program
  | nil      => nil
  | left p   => left p.fill
  | right p  => right p.fill
  | flip p   => flip p.fill
  | loop b p => loop b.fill p.fill
  | hole _ k => stars k

theorem fills_fill (q : Program) : Fills q q.fill := by
  induction q with
  | nil => exact .nil
  | left _ ih => exact .left ih
  | right _ ih => exact .right ih
  | flip _ ih => exact .flip ih
  | loop _ _ ihb ih => exact .loop ihb ih
  | hole i k => exact .hole i (closed_stars k) (size_stars k)

theorem Refines.append {q p r s : Program} (h : Refines q p) (h' : Refines r s) :
    Refines (q ++ r) (p ++ s) := by
  induction h with
  | nil => exact h'
  | left _ ih => exact .left ih
  | right _ ih => exact .right ih
  | flip _ ih => exact .flip ih
  | loop hb _ _ ih => exact .loop hb ih
  | hole i k _ => exact .hole i k _

theorem Refines.step {q p : Program} (h : Refines q p) {t : Tape} {c' : Config}
    (hs : (Config.mk t q).step = some c') :
    ∃ p' : Program, (Config.mk t p).step = some ⟨c'.tape, p'⟩ ∧ Refines c'.prog p' := by
  cases h with
  | nil => cases hs
  | hole => cases hs
  | left h => cases hs; exact ⟨_, rfl, h⟩
  | right h => cases hs; exact ⟨_, rfl, h⟩
  | flip h => cases hs; exact ⟨_, rfl, h⟩
  | @loop b b' q p hb h =>
    cases hs
    refine ⟨if t.head then b' ++ .loop b' p else p, rfl, ?_⟩
    show Refines (if t.head then b ++ .loop b q else q) _
    split
    · exact hb.append (.loop hb h)
    · exact h

theorem Refines.steps {q p : Program} (h : Refines q p) {t : Tape} {k : Nat} {c' : Config}
    (hs : (Config.mk t q).steps k = some c') :
    ∃ p' : Program, (Config.mk t p).steps k = some ⟨c'.tape, p'⟩ ∧ Refines c'.prog p' := by
  induction k generalizing q p t with
  | zero => cases hs; exact ⟨p, rfl, h⟩
  | succ k ih =>
    simp only [Config.steps] at hs ⊢
    cases hst : (Config.mk t q).step with
    | none => simp [hst] at hs
    | some c₁ =>
      rw [hst, Option.bind_some] at hs
      obtain ⟨p₁, hp₁, hr⟩ := h.step hst
      rw [hp₁, Option.bind_some]
      exact ih hr hs

theorem Refines.haltsIn {q p : Program} (h : Refines q p) {k : Nat} {t : Tape}
    (hs : q.init.steps k = some ⟨t, Program.nil⟩) : p.init.HaltsIn k := by
  obtain ⟨p', hp, hr⟩ := h.steps hs
  cases hr
  exact ⟨_, hp, rfl⟩

theorem Refines.not_halts {q p : Program} (h : Refines q p) (hq : ¬ q.init.Halts) :
    ¬ p.init.Halts := by
  refine Config.Progress.not_halts (S := fun (d : Config) =>
    ∃ c : Config, ¬ c.Halts ∧ c.tape = d.tape ∧ Refines c.prog d.prog) ?_ ⟨q.init, hq, rfl, h⟩
  rintro ⟨u, r⟩ ⟨⟨t, s⟩, hc, ht, hr⟩
  cases ht
  cases hst : (Config.mk u s).step with
  | none => exact absurd ⟨0, Config.haltsIn_zero.mpr hst⟩ hc
  | some c' =>
    obtain ⟨p', hp', hr'⟩ := Refines.step hr hst
    refine ⟨1, ⟨c'.tape, p'⟩, by omega, by simp [Config.steps, hp'], c', ?_, rfl, hr'⟩
    rintro ⟨k, hk⟩
    exact hc ⟨k + 1, (Config.haltsIn_succ hst).mpr hk⟩

end Program

end Bf
