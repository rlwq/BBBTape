import Bf.Decider

namespace Bf

namespace Machine

open scoped Program Machine

variable {T : Type} [Tape T]

def nextIds (m : Machine T) (ids : List Nat) : List Nat :=
  match m.prog with
  | .loop b _ => if Tape.cells m.tape 0 then ids.take b.numGaps ++ ids else ids.drop b.numGaps
  | _         => ids

def stop (m : Machine T) (ids : List Nat) : Verdict :=
  match m.prog with
  | ε        => .halts 0
  | .gap _ _ _ => .stuck (ids.headD 0)
  | _        => .unknown

def sim : Nat → Machine T → List Nat → Verdict
  | 0, m, ids =>
    match m⇒ with
    | none   => m.stop ids
    | some _ => .unknown
  | f + 1, m, ids =>
    match m⇒ with
    | none    => m.stop ids
    | some m' =>
      match m'.sim f (m.nextIds ids) with
      | .halts t => .halts (t + 1)
      | v        => v

theorem stop_halts {m : Machine T} {ids : List Nat} {k : Nat} :
    m⇒ = none → m.stop ids = .halts k → k = 0 ∧ m.prog = ε := by
  intro hs h
  obtain ⟨t, p⟩ := m
  cases p with
  | nil => simp only [stop, Verdict.halts.injEq] at h; exact ⟨h.symm, rfl⟩
  | gap => simp [stop] at h
  | left | right | flip | loop => cases hs

omit [Tape T] in
theorem stop_ne_diverges {m : Machine T} {ids : List Nat} :
    m.stop ids ≠ .diverges := by
  unfold stop
  cases m.prog <;> simp

theorem sim_halts {f : Nat} {m : Machine T} {ids : List Nat} {k : Nat} :
    m.sim f ids = .halts k → (m ⇓ k) := by
  induction f generalizing m ids k with
  | zero =>
    intro h
    unfold sim at h
    cases hs : m⇒ with
    | some _ => simp [hs] at h
    | none =>
      simp only [hs] at h
      obtain ⟨rfl, hp⟩ := stop_halts hs h
      exact haltsIn_zero.mpr hp
  | succ f ih =>
    intro h
    unfold sim at h
    cases hs : m⇒ with
    | none =>
      simp only [hs] at h
      obtain ⟨rfl, hp⟩ := stop_halts hs h
      exact haltsIn_zero.mpr hp
    | some m' =>
      simp only [hs] at h
      cases hr : m'.sim f (m.nextIds ids) with
      | halts j =>
        rw [hr] at h
        cases h
        exact (haltsIn_succ hs).mpr (ih hr)
      | diverges | stuck _ | unknown => rw [hr] at h; cases h

theorem sim_ne_diverges {f : Nat} {m : Machine T} {ids : List Nat} :
    m.sim f ids ≠ .diverges := by
  induction f generalizing m ids with
  | zero =>
    unfold sim
    cases m⇒ with
    | none   => exact stop_ne_diverges
    | some _ => simp
  | succ f ih =>
    unfold sim
    cases m⇒ with
    | none    => exact stop_ne_diverges
    | some m' =>
      simp only
      cases hr : m'.sim f (m.nextIds ids) with
      | halts _ | stuck _ | unknown => simp
      | diverges => exact absurd hr ih

@[specialize] def run : Nat → Machine T → Nat → Machine T × Nat
  | 0,     m, k => (m, k)
  | f + 1, m, k =>
    match m⇒ with
    | none    => (m, k)
    | some m' => run f m' (k + 1)

theorem run_steps {f k j : Nat} {m m' : Machine T} :
    run f m k = (m', j) → ∃ d : Nat, j = k + d ∧ m ⇒ d = some m' := by
  intro h
  induction f generalizing m k with
  | zero =>
    simp only [run, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨0, rfl, rfl⟩
  | succ f ih =>
    unfold run at h
    cases hs : m⇒ with
    | none =>
      simp only [hs, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨0, rfl, rfl⟩
    | some x =>
      simp only [hs] at h
      obtain ⟨d, rfl, hd⟩ := ih h
      exact ⟨d + 1, by omega, by simp [steps, hs, hd]⟩

@[inline] def verdict (limit : Nat) (q : Program) : Verdict :=
  match run limit (q.init T) 0 with
  | (m, k) =>
    match m.prog with
    | ε        => .halts k
    | .gap _ _ _ => (q.init T).sim limit (List.range q.numGaps)
    | _        => .unknown

theorem verdict_halts {limit t : Nat} {q : Program} :
    verdict (T := T) limit q = .halts t → (q.init T) ⇓ t := by
  intro h
  unfold verdict at h
  rcases hr : run limit (q.init T) 0 with ⟨⟨u, p⟩, k⟩
  rw [hr] at h
  cases p with
  | nil =>
    obtain ⟨d, hk, hd⟩ := run_steps hr
    simp only [Verdict.halts.injEq] at h
    have hdt : d = t := by omega
    subst hdt
    exact ⟨u, hd⟩
  | gap => exact sim_halts h
  | left | right | flip | loop => cases h

theorem verdict_ne_diverges {limit : Nat} {q : Program} :
    verdict (T := T) limit q ≠ .diverges := by
  intro h
  unfold verdict at h
  rcases hr : run limit (q.init T) 0 with ⟨⟨u, p⟩, k⟩
  rw [hr] at h
  cases p with
  | gap => exact sim_ne_diverges h
  | nil | left | right | flip | loop => cases h

end Machine

@[inline] def Decider.simulator (T : Type) [Tape T] (limit : Nat) : Decider where
  decide := fun (q : Program) => Machine.verdict (T := T) limit q
  sound  := fun (q : Program) => by
    cases h : Machine.verdict (T := T) limit q with
    | halts t           => exact Program.haltsIn_of (Machine.verdict_halts h)
    | diverges          => exact absurd h Machine.verdict_ne_diverges
    | stuck _ | unknown => trivial

end Bf
