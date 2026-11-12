import Bf.Basic

inductive Verdict where
  | halts | nonhalts | unknown
  deriving DecidableEq, Repr

instance : ToString Verdict where
  toString
    | .halts    => "halts"
    | .nonhalts => "nonhalts"
    | .unknown  => "unknown"

@[ext] structure Decider where
  run      : Program → Verdict
  sound_h  : ∀ p, run p = .halts → p.toMachine.halts
  sound_nh : ∀ p, run p = .nonhalts → ¬ p.toMachine.halts

def Decider.orElse (d₁ d₂ : Decider) : Decider where
  run p := match d₁.run p with
    | .unknown => d₂.run p
    | v        => v
  sound_h p h := by
    cases h₁ : d₁.run p <;> simp only [h₁, reduceCtorEq] at h
    case halts   => exact d₁.sound_h p h₁
    case unknown => exact d₂.sound_h p h
  sound_nh p h := by
    cases h₁ : d₁.run p <;> simp only [h₁, reduceCtorEq] at h
    case nonhalts => exact d₁.sound_nh p h₁
    case unknown  => exact d₂.sound_nh p h

instance : OrElse Decider := ⟨fun d₁ d₂ => d₁.orElse (d₂ ())⟩

def Decider.unknown : Decider where
  run _ := .unknown
  sound_h _ h := nomatch h
  sound_nh _ h := nomatch h

theorem Decider.unknown_orElse (d : Decider) : Decider.unknown.orElse d = d := by
  ext p; rfl

theorem Decider.orElse_unknown (d : Decider) : d.orElse .unknown = d := by
  ext p; simp only [orElse, unknown]; split <;> simp_all

theorem Decider.orElse_assoc (a b c : Decider) :
    (a.orElse b).orElse c = a.orElse (b.orElse c) := by
  ext p; simp only [orElse]; cases a.run p <;> rfl

def Decider.any (ds : List Decider) : Decider :=
  ds.foldr Decider.orElse .unknown

def Decider.undecided (d : Decider) (ps : List Program) : List Program :=
  ps.filter fun p => d.run p = .unknown

def Decider.label (d : Decider) (ps : List Program) : List (Program × Verdict) :=
  ps.map fun p => (p, d.run p)
