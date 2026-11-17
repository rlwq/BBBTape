import Bf.Program

namespace Bf

@[ext] structure Config where
  tape : Tape
  prog : Program

def Program.init (p : Program) : Config := ⟨.blank, p⟩

namespace Config

def step : Config → Option Config
  | ⟨_, .nil⟩      => none
  | ⟨t, .left p⟩   => some ⟨t.moveL, p⟩
  | ⟨t, .right p⟩  => some ⟨t.moveR, p⟩
  | ⟨t, .flip p⟩   => some ⟨t.flip, p⟩
  | ⟨t, .loop b p⟩ => some ⟨t, if t.head then b ++ .loop b p else p⟩
  | ⟨_, .hole _ _⟩ => none

def steps (c : Config) : Nat → Option Config
  | 0     => some c
  | n + 1 => c.step.bind (·.steps n)

def HaltsIn (c : Config) (n : Nat) : Prop := ∃ c' : Config, c.steps n = some c' ∧ c'.step = none

def Halts (c : Config) : Prop := ∃ n : Nat, c.HaltsIn n

theorem steps_add (c : Config) (a b : Nat) : c.steps (a + b) = (c.steps a).bind (·.steps b) := by
  induction a generalizing c with
  | zero => simp [steps]
  | succ a ih =>
    rw [Nat.succ_add]
    simp only [steps]
    cases c.step <;> simp [ih]

theorem haltsIn_zero {c : Config} : c.HaltsIn 0 ↔ c.step = none := by
  simp [HaltsIn, steps]

theorem haltsIn_succ {c c' : Config} {n : Nat} (hs : c.step = some c') :
    c.HaltsIn (n + 1) ↔ c'.HaltsIn n := by
  simp [HaltsIn, steps, hs]

theorem not_haltsIn_succ {c : Config} {n : Nat} (hs : c.step = none) : ¬ c.HaltsIn (n + 1) := by
  simp [HaltsIn, steps, hs]

theorem haltsIn_add {c c' : Config} {k m : Nat} (hs : c.steps k = some c') :
    c.HaltsIn (k + m) ↔ c'.HaltsIn m := by
  simp [HaltsIn, steps_add, hs]

theorem steps_eq_none {c : Config} {n m : Nat} (h : c.HaltsIn n) (hm : n < m) :
    c.steps m = none := by
  obtain ⟨c', h₁, h₂⟩ := h
  obtain ⟨k, rfl⟩ : ∃ k : Nat, m = n + (k + 1) := ⟨m - n - 1, by omega⟩
  rw [steps_add, h₁]
  simp only [Option.bind_some, steps, h₂, Option.bind_none]

theorem not_haltsIn_of_lt {c c' : Config} {k n : Nat} (hs : c.steps k = some c') (hn : n < k) :
    ¬ c.HaltsIn n := by
  intro (h : c.HaltsIn n)
  rw [steps_eq_none h hn] at hs
  cases hs

theorem HaltsIn.unique {c : Config} {n m : Nat} (h : c.HaltsIn n) (h' : c.HaltsIn m) : n = m := by
  rcases Nat.lt_trichotomy n m with hlt | heq | hgt
  · exact absurd h (not_haltsIn_of_lt h'.choose_spec.1 hlt)
  · exact heq
  · exact absurd h' (not_haltsIn_of_lt h.choose_spec.1 hgt)

end Config

namespace Program

def SameTime (p q : Program) : Prop := ∀ k : Nat, p.init.HaltsIn k ↔ q.init.HaltsIn k

theorem SameTime.refl (p : Program) : p.SameTime p := fun (_ : Nat) => Iff.rfl

theorem SameTime.symm {p q : Program} (h : p.SameTime q) : q.SameTime p :=
  fun (k : Nat) => (h k).symm

theorem SameTime.trans {p q r : Program} (h₁ : p.SameTime q) (h₂ : q.SameTime r) :
    p.SameTime r :=
  fun (k : Nat) => (h₁ k).trans (h₂ k)

theorem haltsIn_size_of_loopFree {p : Program} (h : p.loopFree = true) (t : Tape) :
    (Config.mk t p).HaltsIn p.size := by
  induction p generalizing t with
  | nil => exact Config.haltsIn_zero.mpr rfl
  | loop => cases h
  | hole => cases h
  | left p ih | right p ih | flip p ih => exact (Config.haltsIn_succ rfl).mpr (ih h _)

end Program

end Bf
