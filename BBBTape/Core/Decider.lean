import BBBTape.Core.Mirror

namespace BBBTape

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

/-- Lazy in the second verdict: a later decider runs only if the earlier one gave up. -/
instance : OrElse (Verdict q) where
  orElse v₁ v₂ := match v₁ with
    | .unknown => v₂ ()
    | v        => v

theorem orElse_eq (a b : Verdict q) : (a <|> b) = a.orElse b := by
  cases a <;> rfl

/-- `orElse` with `unknown` forms a monoid: the first verdict that is not `unknown` wins. -/
instance : Std.Associative (orElse (q := q)) where
  assoc a _ _ := by cases a <;> rfl

instance : Std.LawfulIdentity (orElse (q := q)) .unknown where
  left_id _  := rfl
  right_id v := by cases v <;> rfl

end Verdict

/-- A decider is just a function: the proofs travel inside the verdicts. -/
def Decider := (q : Program) → Verdict q

namespace Decider

def unknown : Decider := fun _ => .unknown

def orElse (d₁ d₂ : Decider) : Decider := fun q => d₁ q <|> d₂ q

instance : OrElse Decider where
  orElse d₁ d₂ := d₁.orElse (d₂ ())

theorem orElse_eq (a b : Decider) : (a <|> b) = a.orElse b := rfl

/-- The monoid on verdicts, lifted pointwise. -/
instance : Std.Associative orElse where
  assoc a b c := funext fun q => by
    simp only [orElse, Verdict.orElse_eq]
    exact Std.Associative.assoc (op := Verdict.orElse) (a q) (b q) (c q)

instance : Std.LawfulIdentity orElse unknown where
  left_id d  := funext fun q => by simp only [orElse, unknown, Verdict.orElse_eq]; rfl
  right_id d := funext fun q => by
    simp only [orElse, unknown, Verdict.orElse_eq]
    exact Std.LawfulRightIdentity.right_id (op := Verdict.orElse) (d q)

def any (ds : List Decider) : Decider :=
  ds.foldr (· <|> ·) unknown

/-- Run `d` on the mirror image; only divergence transfers back, since gap ids are not mirrored. -/
def mirror (d : Decider) : Decider := fun q =>
  match d q.mirror with
  | .diverges h => .diverges (Program.diverges_of_mirror h)
  | _           => .unknown

end Decider

end BBBTape
