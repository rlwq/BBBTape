import Bf.Config

namespace Bf

namespace Config

def Simulation (R : Config → Config → Prop) : Prop :=
  ∀ c d : Config, R c d →
    (c.step = none ∧ d.step = none) ∨
    ∃ (k : Nat) (c' d' : Config), 0 < k ∧ c.steps k = some c' ∧ d.steps k = some d' ∧ R c' d'

theorem Simulation.haltsIn_iff {R : Config → Config → Prop} (h : Simulation R)
    {c d : Config} (hcd : R c d) (n : Nat) : c.HaltsIn n ↔ d.HaltsIn n := by
  induction n using Nat.strongRecOn generalizing c d with
  | _ n ih =>
    rcases h c d hcd with ⟨h₁, h₂⟩ | ⟨k, c', d', hk, h₁, h₂, hr⟩
    · cases n with
      | zero => simp [haltsIn_zero, h₁, h₂]
      | succ n => exact iff_of_false (not_haltsIn_succ h₁) (not_haltsIn_succ h₂)
    · by_cases hn : n < k
      · exact iff_of_false (not_haltsIn_of_lt h₁ hn) (not_haltsIn_of_lt h₂ hn)
      · obtain ⟨m, rfl⟩ : ∃ m : Nat, n = k + m := ⟨n - k, by omega⟩
        rw [haltsIn_add h₁, haltsIn_add h₂]
        exact ih m (by omega) hr

theorem Simulation.sameTime {R : Config → Config → Prop} (h : Simulation R)
    {p q : Program} (hpq : R p.init q.init) : p.SameTime q :=
  fun (k : Nat) => h.haltsIn_iff hpq k

def Progress (S : Config → Prop) : Prop :=
  ∀ c : Config, S c → ∃ (k : Nat) (c' : Config), 0 < k ∧ c.steps k = some c' ∧ S c'

theorem Progress.not_halts {S : Config → Prop} (h : Progress S) {c : Config} (hc : S c) :
    ¬ c.Halts := by
  rintro ⟨m, hm⟩
  induction m using Nat.strongRecOn generalizing c with
  | _ m ih =>
    obtain ⟨k, c', hk, hs, hc'⟩ := h c hc
    by_cases hmk : m < k
    · exact not_haltsIn_of_lt hs hmk hm
    · obtain ⟨j, rfl⟩ : ∃ j : Nat, m = k + j := ⟨m - k, by omega⟩
      exact ih j (by omega) hc' ((haltsIn_add hs).mp hm)

theorem not_halts_of_steps {c c' : Config} {k : Nat} (hs : c.steps k = some c') (h : ¬ c'.Halts) :
    ¬ c.Halts := by
  rintro ⟨m, hm⟩
  by_cases hmk : m < k
  · exact not_haltsIn_of_lt hs hmk hm
  · obtain ⟨j, rfl⟩ : ∃ j : Nat, m = k + j := ⟨m - k, by omega⟩
    exact h ⟨j, (haltsIn_add hs).mp hm⟩

theorem step_append (t : Tape) (p r : Program) (hp : p ≠ .nil) :
    (Config.mk t (p ++ r)).step =
      (Config.mk t p).step.map fun (c : Config) => ⟨c.tape, c.prog ++ r⟩ := by
  cases p with
  | nil => exact absurd rfl hp
  | left p | right p | flip p => rfl
  | hole => rfl
  | loop b p =>
    simp only [step, Program.loop_append, Option.map_some]
    split <;> simp [Program.append_assoc]

theorem not_halts_append {t : Tape} {p : Program} (r : Program) (h : ¬ (Config.mk t p).Halts) :
    ¬ (Config.mk t (p ++ r)).Halts := by
  refine Progress.not_halts (S := fun (d : Config) =>
    ∃ c : Config, ¬ c.Halts ∧ d = ⟨c.tape, c.prog ++ r⟩) ?_ ⟨⟨t, p⟩, h, rfl⟩
  rintro _ ⟨⟨u, q⟩, hc, rfl⟩
  cases hs : (Config.mk u q).step with
  | none => exact absurd ⟨0, haltsIn_zero.mpr hs⟩ hc
  | some c' =>
    have hq : q ≠ .nil := by rintro rfl; cases hs
    have h₁ : (Config.mk u (q ++ r)).steps 1 = some ⟨c'.tape, c'.prog ++ r⟩ := by
      simp [steps, step_append u q r hq, hs]
    have h₂ : ¬ c'.Halts := by
      rintro ⟨k, hk⟩
      exact hc ⟨k + 1, (haltsIn_succ hs).mpr hk⟩
    exact ⟨1, _, by omega, h₁, c', h₂, rfl⟩

end Config

end Bf
