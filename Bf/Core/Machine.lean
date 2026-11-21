import Bf.Core.Tape
import Bf.Core.Program
import Bf.Core.Refines

namespace Bf

structure Machine (T : Type) where
  tape : T
  prog : Program

class Executable (α : Type) where
  HaltsIn  : α → Nat → Prop
  Diverges : α → Prop

def Executable.Halts {α : Type} [Executable α] (x : α) : Prop :=
  ∃ k : Nat, Executable.HaltsIn x k

def Program.init (T : Type) [Tape T] (p : Program) : Machine T := ⟨Tape.blank, p⟩

namespace Machine

open scoped Program

variable {T : Type} [Tape T]

@[inline] def step : Machine T → Option (Machine T)
  | ⟨_, ε⟩          => none
  | ⟨t, .left p⟩    => some ⟨Tape.moveL t, p⟩
  | ⟨t, .right p⟩   => some ⟨Tape.moveR t, p⟩
  | ⟨t, .flip p⟩    => some ⟨Tape.flip t, p⟩
  | ⟨t, .loop b p⟩  => some ⟨t, if Tape.cells t 0 then b ++ .loop b p else p⟩
  | ⟨_, .gap _ _ _⟩ => none

scoped postfix:max "⇒" => step

@[specialize] def steps (m : Machine T) : Nat → Option (Machine T)
  | 0     => some m
  | n + 1 => m⇒.bind (·.steps n)

scoped infix:60 " ⇒ " => steps

def HaltsIn (m : Machine T) (k : Nat) : Prop :=
  ∃ t : T, m ⇒ k = some ⟨t, ε⟩

def Diverges (m : Machine T) : Prop :=
  ∀ k : Nat, (m ⇒ k).isSome

instance : Executable (Machine T) where
  HaltsIn  := HaltsIn
  Diverges := Diverges

@[simp] theorem executable_haltsIn (m : Machine T) (k : Nat) :
    Executable.HaltsIn m k = m.HaltsIn k := rfl

@[simp] theorem executable_diverges (m : Machine T) :
    Executable.Diverges m = m.Diverges := rfl

scoped infix:50 " ⇓ " => Executable.HaltsIn
scoped postfix:max "⇓" => Executable.Halts
scoped postfix:max "⇑" => Executable.Diverges

def Refines (m n : Machine T) : Prop :=
  m.tape = n.tape ∧ m.prog ⊑ n.prog

scoped infix:50 " ⊑ " => Refines

theorem haltsIn_zero {m : Machine T} : (m ⇓ 0) ↔ m.prog = ε := by
  obtain ⟨t, p⟩ := m
  simp [HaltsIn, steps]

theorem haltsIn_succ {m m' : Machine T} {k : Nat} :
    m⇒ = some m' → ((m ⇓ (k + 1)) ↔ (m' ⇓ k)) := by
  intro hs
  simp [HaltsIn, steps, hs]

theorem not_haltsIn_succ {m : Machine T} {k : Nat} :
    m⇒ = none → ¬ (m ⇓ (k + 1)) := by
  intro hs
  simp [HaltsIn, steps, hs]

theorem HaltsIn.unique {m : Machine T} {k j : Nat} : (m ⇓ k) → (m ⇓ j) → k = j := by
  induction k generalizing m j with
  | zero =>
    intro hk hj
    rw [haltsIn_zero] at hk
    cases j with
    | zero => rfl
    | succ j =>
      have hnone : m⇒ = none := by obtain ⟨t, p⟩ := m; dsimp only at hk; subst hk; rfl
      exact absurd hj (not_haltsIn_succ hnone)
  | succ k ih =>
    intro hk hj
    cases hst : m⇒ with
    | none => exact absurd hk (not_haltsIn_succ hst)
    | some m' =>
      cases j with
      | zero =>
        rw [haltsIn_zero] at hj
        obtain ⟨t, p⟩ := m
        dsimp only at hj
        subst hj
        cases hst
      | succ j =>
        exact congrArg Nat.succ (ih ((haltsIn_succ hst).mp hk) ((haltsIn_succ hst).mp hj))

theorem not_halts_of_diverges {m : Machine T} : m⇑ → ¬ m⇓ := by
  rintro hd ⟨k, t, hs⟩
  have h := hd (k + 1)
  have hstep : m ⇒ (k + 1) = none := by
    clear hd h
    induction k generalizing m with
    | zero =>
      simp only [steps] at hs ⊢
      cases hs
      rfl
    | succ k ih =>
      rw [steps] at hs
      rw [steps]
      cases hst : m⇒ with
      | none => simp [hst] at hs
      | some m' =>
        simp only [hst, Option.bind_some] at hs ⊢
        exact ih hs
  rw [hstep] at h
  cases h

theorem steps_add (m : Machine T) (a b : Nat) :
    m ⇒ (a + b) = (m ⇒ a).bind (· ⇒ b) := by
  induction a generalizing m with
  | zero => simp [steps]
  | succ a ih =>
    rw [Nat.succ_add]
    simp only [steps]
    cases m⇒ <;> simp [ih]

theorem isSome_steps_of_le {m m' : Machine T} {j k : Nat} :
    m ⇒ k = some m' → j ≤ k → (m ⇒ j).isSome := by
  intro hs hj
  obtain ⟨d, rfl⟩ : ∃ d : Nat, k = j + d := ⟨k - j, by omega⟩
  rw [steps_add] at hs
  cases h : m ⇒ j with
  | none => rw [h] at hs; cases hs
  | some _ => rfl

theorem diverges_of_steps {m m' : Machine T} {k : Nat} :
    m ⇒ k = some m' → m'⇑ → m⇑ := by
  intro hs hd j
  by_cases hj : j ≤ k
  · exact isSome_steps_of_le hs hj
  · obtain ⟨d, rfl⟩ : ∃ d : Nat, j = k + d := ⟨j - k, by omega⟩
    rw [steps_add, hs, Option.bind_some]
    exact hd d

def Progress (S : Machine T → Prop) : Prop :=
  ∀ m : Machine T, S m → ∃ (k : Nat) (m' : Machine T), 0 < k ∧ m ⇒ k = some m' ∧ S m'

theorem Progress.diverges {S : Machine T → Prop} : Progress S → ∀ {m : Machine T}, S m → m⇑ := by
  intro h m hm j
  induction j using Nat.strongRecOn generalizing m with
  | _ j ih =>
    obtain ⟨k, m', hk, hs, hm'⟩ := h m hm
    by_cases hj : j ≤ k
    · exact isSome_steps_of_le hs hj
    · obtain ⟨d, rfl⟩ : ∃ d : Nat, j = k + d := ⟨j - k, by omega⟩
      rw [steps_add, hs, Option.bind_some]
      exact ih d (by omega) hm'

namespace Refines

theorem step {m n n' : Machine T} :
    m ⊑ n → n⇒ = some n' → ∃ m' : Machine T, m⇒ = some m' ∧ m' ⊑ n' := by
  rintro ⟨ht, hpq⟩ hs
  obtain ⟨t, p⟩ := m
  obtain ⟨_, q⟩ := n
  dsimp only at ht hpq
  subst ht
  cases hpq with
  | nil => cases hs
  | gap => cases hs
  | left h => cases hs; exact ⟨_, rfl, rfl, h⟩
  | right h => cases hs; exact ⟨_, rfl, rfl, h⟩
  | flip h => cases hs; exact ⟨_, rfl, rfl, h⟩
  | @loop b' b p q hb h =>
    cases hs
    refine ⟨⟨t, if Tape.cells t 0 then b' ++ .loop b' p else p⟩, rfl, rfl, ?_⟩
    show (if Tape.cells t 0 then b' ++ .loop b' p else p) ⊑ (if Tape.cells t 0 then b ++ .loop b q else q)
    split
    · exact hb.append (.loop hb h)
    · exact h

theorem steps {m n n' : Machine T} {k : Nat} :
    m ⊑ n → n ⇒ k = some n' → ∃ m' : Machine T, m ⇒ k = some m' ∧ m' ⊑ n' := by
  intro h hs
  induction k generalizing m n with
  | zero => cases hs; exact ⟨m, rfl, h⟩
  | succ k ih =>
    simp only [Machine.steps] at hs ⊢
    cases hst : n⇒ with
    | none => simp [hst] at hs
    | some n₁ =>
      rw [hst, Option.bind_some] at hs
      obtain ⟨m₁, hm₁, hr⟩ := h.step hst
      rw [hm₁, Option.bind_some]
      exact ih hr hs

theorem haltsIn {m n : Machine T} {k : Nat} : m ⊑ n → (n ⇓ k) → (m ⇓ k) := by
  rintro h ⟨t, hs⟩
  obtain ⟨⟨t', p'⟩, hm, ht, hp⟩ := h.steps hs
  dsimp only at ht hp
  subst ht
  cases hp
  exact ⟨t', hm⟩

theorem halts {m n : Machine T} : m ⊑ n → n⇓ → m⇓ := by
  rintro h ⟨k, hk⟩
  exact ⟨k, h.haltsIn hk⟩

theorem diverges {m n : Machine T} : m ⊑ n → n⇑ → m⇑ := by
  intro h hn k
  obtain ⟨n', hs⟩ := Option.isSome_iff_exists.mp (hn k)
  obtain ⟨m', hm, _⟩ := h.steps hs
  exact Option.isSome_iff_exists.mpr ⟨m', hm⟩

end Refines

section Equiv

variable {U : Type} [Tape U]

def Equiv (m : Machine T) (n : Machine U) : Prop :=
  m.prog = n.prog ∧ ∀ i : Int, Tape.cells m.tape i = Tape.cells n.tape i

scoped infix:50 " ≃ " => Equiv

theorem Equiv.init (p : Program) : (p.init T) ≃ (p.init U) :=
  ⟨rfl, fun (i : Int) => by simp [Program.init]⟩

theorem Equiv.step {m : Machine T} {n : Machine U} {m' : Machine T} :
    m ≃ n → m⇒ = some m' → ∃ n' : Machine U, n⇒ = some n' ∧ m' ≃ n' := by
  rintro ⟨hp, ht⟩ hs
  obtain ⟨t, p⟩ := m
  obtain ⟨u, q⟩ := n
  dsimp only at hp ht
  subst hp
  cases p with
  | nil | gap => cases hs
  | left p =>
    cases hs
    exact ⟨_, rfl, rfl, fun i => by simp [Tape.cells_moveL, ht (i - 1)]⟩
  | right p =>
    cases hs
    exact ⟨_, rfl, rfl, fun i => by simp [Tape.cells_moveR, ht (i + 1)]⟩
  | flip p =>
    cases hs
    exact ⟨_, rfl, rfl, fun i => by simp [Tape.cells_flip, ht 0, ht i]⟩
  | loop b p =>
    cases hs
    have hh : Tape.cells t 0 = Tape.cells u 0 := ht 0
    exact ⟨_, rfl, by simp [hh], ht⟩

theorem Equiv.steps {m : Machine T} {n : Machine U} {m' : Machine T} {k : Nat} :
    m ≃ n → m ⇒ k = some m' → ∃ n' : Machine U, n ⇒ k = some n' ∧ m' ≃ n' := by
  intro h hs
  induction k generalizing m n with
  | zero => cases hs; exact ⟨n, rfl, h⟩
  | succ k ih =>
    simp only [Machine.steps] at hs ⊢
    cases hst : m⇒ with
    | none => simp [hst] at hs
    | some m₁ =>
      rw [hst, Option.bind_some] at hs
      obtain ⟨n₁, hn₁, he⟩ := h.step hst
      rw [hn₁, Option.bind_some]
      exact ih he hs

theorem Equiv.haltsIn {m : Machine T} {n : Machine U} {k : Nat} :
    m ≃ n → (m ⇓ k) → (n ⇓ k) := by
  rintro h ⟨t, hs⟩
  obtain ⟨⟨u, q⟩, hn, hp, _⟩ := h.steps hs
  dsimp only at hp
  subst hp
  exact ⟨u, hn⟩

theorem Equiv.diverges {m : Machine T} {n : Machine U} :
    m ≃ n → m⇑ → n⇑ := by
  intro h hm k
  obtain ⟨m', hs⟩ := Option.isSome_iff_exists.mp (hm k)
  obtain ⟨n', hn, _⟩ := h.steps hs
  exact Option.isSome_iff_exists.mpr ⟨n', hn⟩

end Equiv

end Machine

open scoped Machine in
instance : Executable Program where
  HaltsIn p k := ∀ (T : Type) [Tape T], (p.init T) ⇓ k
  Diverges p  := ∀ (T : Type) [Tape T], (p.init T)⇑

open scoped Machine in
theorem Program.haltsIn_of {T : Type} [Tape T] {p : Program} {k : Nat}
    (h : (p.init T) ⇓ k) : p ⇓ k :=
  fun _ _ => (Machine.Equiv.init p).haltsIn h

open scoped Machine in
theorem Program.diverges_of {T : Type} [Tape T] {p : Program}
    (h : (p.init T)⇑) : p⇑ :=
  fun _ _ => (Machine.Equiv.init p).diverges h

namespace Program

open scoped Machine

def Equiv (p q : Program) : Prop :=
  ∀ k : Nat, (p ⇓ k) ↔ (q ⇓ k)

scoped infix:50 " ~ " => Equiv

theorem Equiv.refl (p : Program) : p ~ p := fun _ => Iff.rfl

end Program

namespace Program.Refines

open scoped Program Machine

theorem haltsIn {p q : Program} {k : Nat} : p ⊑ q → (q ⇓ k) → (p ⇓ k) :=
  fun h hq T _ => Machine.Refines.haltsIn (n := q.init T) ⟨rfl, h⟩ (hq T)

theorem halts {p q : Program} : p ⊑ q → q⇓ → p⇓ :=
  fun h ⟨k, hk⟩ => ⟨k, h.haltsIn hk⟩

theorem diverges {p q : Program} : p ⊑ q → q⇑ → p⇑ :=
  fun h hq T _ => Machine.Refines.diverges (n := q.init T) ⟨rfl, h⟩ (hq T)

end Program.Refines

end Bf
