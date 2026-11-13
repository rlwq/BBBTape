import Bf.Simulation

namespace Bf

def Program.dilate : Program → Program
  | .nil      => .nil
  | .left p   => .left (.left p.dilate)
  | .right p  => .right (.right p.dilate)
  | .flip p   => .flip p.dilate
  | .loop b p => .loop b.dilate p.dilate

theorem Program.dilate_append (p q : Program) : (p ++ q).dilate = p.dilate ++ q.dilate := by
  induction p with
  | nil => rfl
  | left _ ih | right _ ih | flip _ ih => simp [dilate, ih]
  | loop _ _ _ ih => simp [dilate, ih]

def Tape.dilate (t : Tape) : Tape :=
  ⟨fun (i : Int) => if i % 2 = 0 then t.cells (i / 2) else false⟩

theorem Tape.dilate_blank : Tape.blank.dilate = Tape.blank := by
  unfold dilate blank
  congr 1
  funext i
  split <;> rfl

namespace Config

def dilate (c : Config) : Config := ⟨c.tape.dilate, c.prog.dilate⟩

theorem dilate_step {c c' : Config} (hs : c.step = some c') :
    ∃ k : Nat, 0 < k ∧ c.dilate.steps k = some c'.dilate := by
  obtain ⟨t, p⟩ := c
  cases p with
  | nil => cases hs
  | left p =>
    cases hs
    refine ⟨2, by omega, ?_⟩
    simp only [dilate, Program.dilate, steps, step, Option.bind_some]
    congr 2
    apply Tape.ext; funext i
    simp only [Tape.dilate, Tape.moveL]
    by_cases h : i % 2 = 0
    · rw [if_pos h, if_pos (by omega)]; congr 1; omega
    · rw [if_neg h, if_neg (by omega)]
  | right p =>
    cases hs
    refine ⟨2, by omega, ?_⟩
    simp only [dilate, Program.dilate, steps, step, Option.bind_some]
    congr 2
    apply Tape.ext; funext i
    simp only [Tape.dilate, Tape.moveR]
    by_cases h : i % 2 = 0
    · rw [if_pos h, if_pos (by omega)]; congr 1; omega
    · rw [if_neg h, if_neg (by omega)]
  | flip p =>
    cases hs
    refine ⟨1, by omega, ?_⟩
    simp only [dilate, Program.dilate, steps, step, Option.bind_some]
    congr 2
    apply Tape.ext; funext i
    simp only [Tape.dilate, Tape.flip, Tape.head]
    by_cases h0 : i = 0
    · subst h0; rfl
    · rw [if_neg h0]
      by_cases h : i % 2 = 0
      · rw [if_pos h, if_pos h, if_neg (by omega)]
      · rw [if_neg h, if_neg h]
  | loop b p =>
    cases hs
    refine ⟨1, by omega, ?_⟩
    simp only [dilate, Program.dilate, steps, step, Option.bind_some]
    have hh : t.dilate.head = t.head := rfl
    rw [hh]
    split <;> simp [Program.dilate_append, Program.dilate]

theorem not_halts_dilate {c : Config} (h : ¬ c.Halts) : ¬ c.dilate.Halts := by
  refine Progress.not_halts (S := fun (d : Config) => ∃ c : Config, ¬ c.Halts ∧ d = c.dilate) ?_ ⟨c, h, rfl⟩
  rintro _ ⟨c, hc, rfl⟩
  cases hs : c.step with
  | none => exact absurd ⟨0, haltsIn_zero.mpr hs⟩ hc
  | some c' =>
    obtain ⟨k, hk, hd⟩ := dilate_step hs
    refine ⟨k, c'.dilate, hk, hd, c', ?_, rfl⟩
    rintro ⟨n, hn⟩
    exact hc ⟨n + 1, (haltsIn_succ hs).mpr hn⟩

end Config

theorem Program.not_halts_dilate {p : Program} (h : ¬ p.init.Halts) : ¬ p.dilate.init.Halts := by
  have := Config.not_halts_dilate h
  simpa [Config.dilate, Program.init, Tape.dilate_blank] using this

end Bf
