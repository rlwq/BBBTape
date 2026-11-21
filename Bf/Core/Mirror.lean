import Bf.Core.Statement
import Bf.Tapes.Spec

namespace Bf

namespace Machine

open scoped Machine

def Mirrored (m n : Machine SpecTape) : Prop :=
  n.prog = m.prog.mirror ∧ ∀ i : Int, n.tape i = m.tape (-i)

theorem Mirrored.step {m n m' : Machine SpecTape} :
    Mirrored m n → m⇒ = some m' → ∃ n' : Machine SpecTape, n⇒ = some n' ∧ Mirrored m' n' := by
  rintro ⟨hp, ht⟩ hs
  obtain ⟨t, p⟩ := m
  obtain ⟨u, q⟩ := n
  dsimp only at hp ht
  subst hp
  cases p with
  | nil | gap => cases hs
  | left p =>
    cases hs
    refine ⟨⟨Tape.moveR u, p.mirror⟩, rfl, rfl, fun (i : Int) => ?_⟩
    show u (i + 1) = t (-i - 1)
    rw [ht, show -(i + 1) = -i - 1 by omega]
  | right p =>
    cases hs
    refine ⟨⟨Tape.moveL u, p.mirror⟩, rfl, rfl, fun (i : Int) => ?_⟩
    show u (i - 1) = t (-i + 1)
    rw [ht, show -(i - 1) = -i + 1 by omega]
  | flip p =>
    cases hs
    refine ⟨⟨Tape.flip u, p.mirror⟩, rfl, rfl, fun (i : Int) => ?_⟩
    show (if i = 0 then !u 0 else u i) = if -i = 0 then !t 0 else t (-i)
    by_cases hi : i = 0
    · subst hi
      simpa using ht 0
    · simp only [hi, ↓reduceIte, show ¬ -i = 0 by omega]
      exact ht i
  | loop b p =>
    cases hs
    have hh : Tape.cells u 0 = Tape.cells t 0 := by
      have h0 := ht 0
      rw [Int.neg_zero] at h0
      exact h0
    refine ⟨⟨u, if Tape.cells u 0 then b.mirror ++ .loop b.mirror p.mirror else p.mirror⟩,
      rfl, ?_, ht⟩
    rw [hh]
    show _ = (if Tape.cells t 0 then b ++ .loop b p else p).mirror
    split <;> simp [Program.mirror]

theorem Mirrored.diverges {m n : Machine SpecTape} : Mirrored m n → m⇑ → n⇑ := by
  intro h hm k
  induction k generalizing m n with
  | zero => rfl
  | succ k ih =>
    obtain ⟨m', hs⟩ := Option.isSome_iff_exists.mp (hm 1)
    have hs₁ : m⇒ = some m' := by
      simp only [steps] at hs
      cases hst : m⇒ with
      | none => simp [hst] at hs
      | some x => simpa [hst, steps] using hs
    obtain ⟨n', hn, hr⟩ := h.step hs₁
    simp only [steps, hn, Option.bind_some]
    refine ih hr fun (j : Nat) => ?_
    have := hm (j + 1)
    simpa only [steps, hs₁, Option.bind_some] using this

theorem Mirrored.steps {m n m' : Machine SpecTape} {k : Nat} :
    Mirrored m n → m ⇒ k = some m' → ∃ n' : Machine SpecTape, n ⇒ k = some n' ∧ Mirrored m' n' := by
  intro h hs
  induction k generalizing m n with
  | zero => cases hs; exact ⟨n, rfl, h⟩
  | succ k ih =>
    simp only [Machine.steps] at hs ⊢
    cases hst : m⇒ with
    | none => simp [hst] at hs
    | some m₁ =>
      rw [hst, Option.bind_some] at hs
      obtain ⟨n₁, hn₁, hm⟩ := h.step hst
      rw [hn₁, Option.bind_some]
      exact ih hm hs

theorem Mirrored.haltsIn {m n : Machine SpecTape} {k : Nat} :
    Mirrored m n → (m ⇓ k) → (n ⇓ k) := by
  rintro h ⟨t, hs⟩
  obtain ⟨⟨u, q⟩, hn, hp, _⟩ := h.steps hs
  dsimp only [Program.mirror] at hp
  subst hp
  exact ⟨u, hn⟩

end Machine

open scoped Program Machine in
theorem Program.Equiv.mirror (p : Program) : p ~ p.mirror := fun _ =>
  ⟨fun hk => Program.haltsIn_of (Machine.Mirrored.haltsIn (m := p.init SpecTape) ⟨rfl, fun _ => rfl⟩ (hk SpecTape)),
   fun hk => Program.haltsIn_of
     (Machine.Mirrored.haltsIn (m := p.mirror.init SpecTape) ⟨(mirror_mirror p).symm, fun _ => rfl⟩ (hk SpecTape))⟩

open scoped Machine in
theorem Program.diverges_of_mirror {q : Program} : q.mirror⇑ → q⇑ := fun h =>
  have hm : Machine.Mirrored (q.mirror.init SpecTape) (q.init SpecTape) :=
    ⟨(Program.mirror_mirror q).symm, fun (_ : Int) => rfl⟩
  Program.diverges_of (hm.diverges (h SpecTape))

end Bf
