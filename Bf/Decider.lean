import Bf.Statement

namespace Bf

open scoped Machine

/-- What a decider concluded about the program `q`. Every conclusion carries its own proof,
so a wrong verdict cannot even be constructed. -/
inductive Verdict (q : Program) where
  | halts    (steps : Nat) (h : q ⇓ steps)
  | diverges (h : q⇑)
  | stuck    (gap : Fin q.numGaps)
  | unknown

namespace Verdict

variable {q : Program}

def orElse : Verdict q → Verdict q → Verdict q
  | .unknown, v => v
  | v,        _ => v

instance : OrElse (Verdict q) where
  orElse v₁ v₂ := v₁.orElse (v₂ ())

@[simp] theorem unknown_orElse (v : Verdict q) : (.unknown <|> v) = v := rfl

@[simp] theorem orElse_unknown (v : Verdict q) : (v <|> .unknown) = v := by
  cases v <;> rfl

theorem orElse_assoc (a b c : Verdict q) : ((a <|> b) <|> c) = (a <|> (b <|> c)) := by
  cases a <;> rfl

/-- The number of steps, if the verdict is `halts`. -/
def steps? : Verdict q → Option Nat
  | .halts t _ => some t
  | _          => none

theorem haltsIn_of_steps? {v : Verdict q} {t : Nat} : v.steps? = some t → q ⇓ t := by
  cases v with
  | halts s h => intro hs; cases hs; exact h
  | diverges | stuck | unknown => intro hs; cases hs

end Verdict

/-- A decider is just a function: the proofs travel inside the verdicts. -/
def Decider := (q : Program) → Verdict q

namespace Decider

def unknown : Decider := fun _ => .unknown

def orElse (d₁ d₂ : Decider) : Decider := fun q => d₁ q <|> d₂ q

instance : OrElse Decider where
  orElse d₁ d₂ := d₁.orElse (d₂ ())

@[simp] theorem unknown_orElse (d : Decider) : (unknown <|> d) = d := rfl

@[simp] theorem orElse_unknown (d : Decider) : (d <|> unknown) = d :=
  funext fun q => Verdict.orElse_unknown (d q)

theorem orElse_assoc (a b c : Decider) : ((a <|> b) <|> c) = (a <|> (b <|> c)) :=
  funext fun q => Verdict.orElse_assoc (a q) (b q) (c q)

def any (ds : List Decider) : Decider :=
  ds.foldr (· <|> ·) unknown

end Decider

end Bf
