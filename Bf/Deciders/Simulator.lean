import Bf.Core.Decider

namespace Bf

namespace Machine

open scoped Program Machine

variable {T : Type} [Tape T]

def nextIds (m : Machine T) (ids : List Nat) : List Nat :=
  match m.prog with
  | .loop b _ => if Tape.cells m.tape 0 then ids.take b.numGaps ++ ids else ids.drop b.numGaps
  | _         => ids

theorem haltsIn_of_reached {q : Program} {m : Machine T} {j : Nat}
    (hm : (q.init T) ⇒ j = some m) (hp : m.prog = ε) : (q.init T) ⇓ j :=
  ⟨m.tape, by rw [hm]; cases m; cases hp; rfl⟩

theorem reached_succ {q : Program} {m m' : Machine T} {j : Nat}
    (hm : (q.init T) ⇒ j = some m) (hs : m⇒ = some m') : (q.init T) ⇒ (j + 1) = some m' := by
  rw [steps_add, hm]; simp [steps, hs]

/-- `m` is `q` after `j` steps; `ids` tracks which gap of `q` each gap of `m` came from. -/
def stop (q : Program) (m : Machine T) (j : Nat) (hm : (q.init T) ⇒ j = some m)
    (ids : List Nat) : Verdict q :=
  match hp : m.prog with
  | ε          => .halts j (Program.haltsIn_of (haltsIn_of_reached hm hp))
  | .gap _ _ _ =>
    match ids with
    | i :: _ => if h : i < q.numGaps then .stuck ⟨i, h⟩ else .unknown
    | []     => .unknown
  | _          => .unknown

def sim (q : Program) :
    (f : Nat) → (m : Machine T) → (j : Nat) → (q.init T) ⇒ j = some m → List Nat → Verdict q
  | 0, m, j, hm, ids =>
    match m⇒ with
    | none   => stop q m j hm ids
    | some _ => .unknown
  | f + 1, m, j, hm, ids =>
    match hs : m⇒ with
    | none    => stop q m j hm ids
    | some m' => sim q f m' (j + 1) (reached_succ hm hs) (m.nextIds ids)

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

theorem reached_of_run {q : Program} {limit k : Nat} {m : Machine T} :
    run limit (q.init T) 0 = (m, k) → (q.init T) ⇒ k = some m := by
  intro h
  obtain ⟨d, hk, hd⟩ := run_steps h
  rw [hk, Nat.zero_add]; exact hd

/-- Run fast without bookkeeping; only if execution hits a gap, rerun tracking gap ids. -/
@[inline] def verdict (limit : Nat) (q : Program) : Verdict q :=
  match hr : run limit (q.init T) 0 with
  | (m, k) =>
    match hp : m.prog with
    | ε          => .halts k (Program.haltsIn_of (haltsIn_of_reached (reached_of_run hr) hp))
    | .gap _ _ _ => sim q limit (q.init T) 0 rfl (List.range q.numGaps)
    | _          => .unknown

end Machine

@[inline] def Decider.simulator (T : Type) [Tape T] (limit : Nat) : Decider :=
  fun q => Machine.verdict (T := T) limit q

end Bf
