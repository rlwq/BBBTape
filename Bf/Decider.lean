import Bf.Statement

namespace Bf

inductive Verdict where
  | halts    (steps : Nat)
  | diverges
  | stuck    (id : Nat)
  | unknown
  deriving DecidableEq, Repr

namespace Verdict

def orElse : Verdict → Verdict → Verdict
  | .unknown, v => v
  | v,        _ => v

instance : OrElse Verdict where
  orElse v₁ v₂ := v₁.orElse (v₂ ())

@[simp] theorem unknown_orElse (v : Verdict) : (.unknown <|> v) = v := rfl

@[simp] theorem orElse_unknown (v : Verdict) : (v <|> .unknown) = v := by
  cases v <;> rfl

theorem orElse_assoc (a b c : Verdict) : ((a <|> b) <|> c) = (a <|> (b <|> c)) := by
  cases a <;> rfl

end Verdict

open scoped Machine

@[ext] structure Decider where
  decide : Program → Verdict
  sound  : ∀ q : Program, match decide q with
    | .halts t  => q ⇓ t
    | .diverges => q⇑
    | _         => True

namespace Decider

def unknown : Decider where
  decide := fun (_ : Program) => .unknown
  sound  := fun (_ : Program) => trivial

def orElse (d₁ d₂ : Decider) : Decider where
  decide := fun (q : Program) => d₁.decide q <|> d₂.decide q
  sound  := fun (q : Program) => by
    have h₁ := d₁.sound q
    have h₂ := d₂.sound q
    cases h : d₁.decide q <;> simp [h] at h₁ ⊢ <;> first | exact h₁ | exact h₂

instance : OrElse Decider where
  orElse d₁ d₂ := d₁.orElse (d₂ ())

@[simp] theorem unknown_orElse (d : Decider) : (unknown <|> d) = d := rfl

@[simp] theorem orElse_unknown (d : Decider) : (d <|> unknown) = d := by
  ext q; exact Verdict.orElse_unknown (d.decide q)

theorem orElse_assoc (a b c : Decider) : ((a <|> b) <|> c) = (a <|> (b <|> c)) := by
  ext q; exact Verdict.orElse_assoc (a.decide q) (b.decide q) (c.decide q)

def any (ds : List Decider) : Decider :=
  ds.foldr (· <|> ·) unknown

end Decider

end Bf
