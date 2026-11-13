import Bf.Config

namespace Bf

def Program.mirror : Program → Program
  | .nil      => .nil
  | .left p   => .right p.mirror
  | .right p  => .left p.mirror
  | .flip p   => .flip p.mirror
  | .loop b p => .loop b.mirror p.mirror

def Tape.mirror (t : Tape) : Tape := ⟨fun (i : Int) => t.cells (-i)⟩

def Config.mirror (c : Config) : Config := ⟨c.tape.mirror, c.prog.mirror⟩

namespace Program

theorem mirror_append (p q : Program) : (p ++ q).mirror = p.mirror ++ q.mirror := by
  induction p with
  | nil => rfl
  | left _ ih | right _ ih | flip _ ih => simp [mirror, ih]
  | loop _ _ _ ih => simp [mirror, ih]

theorem size_mirror (p : Program) : p.mirror.size = p.size := by
  induction p with
  | nil => rfl
  | left _ ih | right _ ih | flip _ ih => simp [mirror, size, ih]
  | loop _ _ ihb ih => simp [mirror, size, ihb, ih]

theorem init_mirror (p : Program) : p.mirror.init = p.init.mirror := rfl

end Program

namespace Tape

theorem head_mirror (t : Tape) : t.mirror.head = t.head := rfl

theorem moveL_mirror (t : Tape) : t.mirror.moveL = t.moveR.mirror := by
  ext i
  show t.cells (-(i - 1)) = t.cells (-i + 1)
  congr 1; omega

theorem moveR_mirror (t : Tape) : t.mirror.moveR = t.moveL.mirror := by
  ext i
  show t.cells (-(i + 1)) = t.cells (-i - 1)
  congr 1; omega

theorem flip_mirror (t : Tape) : t.mirror.flip = t.flip.mirror := by
  ext i
  show (if i = 0 then !t.cells (-0) else t.cells (-i)) = (if -i = 0 then !t.cells 0 else t.cells (-i))
  by_cases h : i = 0
  · subst h; rfl
  · simp [h]

end Tape

namespace Config

theorem step_mirror (c : Config) : c.mirror.step = c.step.map mirror := by
  obtain ⟨t, p⟩ := c
  cases p with
  | nil => rfl
  | left p => simp [mirror, step, Program.mirror, Tape.moveR_mirror]
  | right p => simp [mirror, step, Program.mirror, Tape.moveL_mirror]
  | flip p => simp [mirror, step, Program.mirror, Tape.flip_mirror]
  | loop b p =>
    simp only [mirror, step, Program.mirror, Tape.head_mirror, Option.map_some]
    by_cases h : t.head = true <;> simp [h, Program.mirror, Program.mirror_append]

theorem steps_mirror (c : Config) (n : Nat) : c.mirror.steps n = (c.steps n).map mirror := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    simp only [steps, step_mirror]
    cases c.step <;> simp [ih]

theorem haltsIn_mirror (c : Config) (n : Nat) : c.mirror.HaltsIn n ↔ c.HaltsIn n := by
  simp only [HaltsIn, steps_mirror]
  constructor
  · rintro ⟨c', h, hs⟩
    obtain ⟨d, hd, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨d, hd, by rw [step_mirror] at hs; simpa using hs⟩
  · rintro ⟨d, hd, hs⟩
    exact ⟨d.mirror, by rw [hd]; rfl, by rw [step_mirror, hs]; rfl⟩

end Config

theorem Program.sameTime_mirror (p : Program) : p.mirror.SameTime p :=
  fun (k : Nat) => Config.haltsIn_mirror p.init k

end Bf
