import Bf.Core.Trace

namespace Bf

open scoped Machine

/-- What a decider concluded about the program `q`. Every conclusion carries its own proof,
so a wrong verdict cannot even be constructed. When a decider gives up (`unknown`), it hands
the accumulated execution trace to the next decider in the chain. -/
inductive Verdict (T : Type) [Tape T] (q : Program) where
  | halts    (steps : Nat) (h : q ⇓ steps)
  | diverges (h : q⇑)
  | stuck    (gap : Fin q.numGaps)
  | unknown  (tr : Trace T q)

/-- A decider extends or inspects the shared trace of `q` and returns a proved verdict. -/
def Decider (T : Type) [Tape T] := (q : Program) → Trace T q → Verdict T q

namespace Decider

variable {T : Type} [Tape T]

def unknown : Decider T := fun _ tr => .unknown tr

def orElse (d₁ d₂ : Decider T) : Decider T := fun q tr =>
  match d₁ q tr with
  | .unknown tr' => d₂ q tr'
  | v            => v

/-- Lazy in the second decider: it runs only if the first one gave up, reusing its trace. -/
instance : OrElse (Decider T) where
  orElse d₁ d₂ := fun q tr =>
    match d₁ q tr with
    | .unknown tr' => d₂ () q tr'
    | v            => v

theorem orElse_eq (a b : Decider T) : (a <|> b) = a.orElse b := rfl

/-- Deciders with `orElse` and `unknown` form a monoid: the first conclusive verdict wins,
while `unknown` threads the shared execution trace forward. -/
instance : Std.Associative (orElse (T := T)) where
  assoc a b c := funext fun q => funext fun tr => by
    dsimp only [orElse]
    cases a q tr <;> rfl

instance : Std.LawfulIdentity (orElse (T := T)) (unknown (T := T)) where
  left_id _  := rfl
  right_id d := funext fun q => funext fun tr => by
    dsimp only [orElse, unknown]
    cases d q tr <;> rfl

def any (ds : List (Decider T)) : Decider T :=
  ds.foldr (· <|> ·) unknown

/-- Run a decider on `q` starting from the initial empty trace. -/
@[inline] def run (d : Decider T) (q : Program) : Verdict T q :=
  d q (.init T q)

/-- Lift a divergence checker into a decider, preserving the shared trace on `unknown`. -/
@[inline] def ofDiverges (check : Program → Bool) (sound : ∀ {q}, check q = true → q⇑) :
    Decider T := fun q tr =>
  if h : check q then .diverges (sound h) else .unknown tr

/-- Run `d` on the mirror image; only divergence transfers back, since gap ids are not mirrored. -/
def mirror (d : Decider T) : Decider T := fun q tr =>
  match d.run q.mirror with
  | .diverges h => .diverges (Program.diverges_of_mirror h)
  | _           => .unknown tr

end Decider

end Bf
