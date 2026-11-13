import Bf.Solved
import Bf.Deciders.Translated

namespace Bf

namespace Program

def stripPrefix : Program → Program → Option Program
  | nil,      q         => some q
  | left p,   left q    => stripPrefix p q
  | right p,  right q   => stripPrefix p q
  | flip p,   flip q    => stripPrefix p q
  | loop b p, loop b' q => if b = b' then stripPrefix p q else none
  | _,        _         => none

theorem eq_append_of_stripPrefix {p q r : Program} (h : p.stripPrefix q = some r) :
    q = p ++ r := by
  induction p generalizing q with
  | nil => simp only [stripPrefix, Option.some.injEq] at h; simp [h]
  | left p ih => cases q <;> simp only [stripPrefix, reduceCtorEq] at h; rw [ih h]; rfl
  | right p ih => cases q <;> simp only [stripPrefix, reduceCtorEq] at h; rw [ih h]; rfl
  | flip p ih => cases q <;> simp only [stripPrefix, reduceCtorEq] at h; rw [ih h]; rfl
  | loop b p _ ih =>
    cases q with
    | loop b' q =>
      simp only [stripPrefix] at h
      split at h
      · next hb => subst hb; rw [ih h]; rfl
      · cases h
    | _ => simp [stripPrefix] at h

end Program

def Config.blankAt (j : Nat) (c : Config) : Bool :=
  (List.range (2 * j + 1)).all fun (k : Nat) => !c.tape.cells ((k : Int) - j)

theorem Config.tape_eq_blank {c : Config} {j : Nat} (hz : c.tape.ZeroBeyond j)
    (h : c.blankAt j = true) : c.tape = .blank := by
  apply Tape.ext
  funext i
  by_cases hi : -(j : Int) ≤ i ∧ i ≤ j
  · have hk := List.all_eq_true.mp h (i + j).toNat (List.mem_range.mpr (by omega))
    rw [Int.toNat_of_nonneg (by omega), Int.add_sub_cancel] at hk
    simpa [Tape.blank] using hk
  · exact hz i (by omega)

def Solved.extends (m : Solved) (q : Program) : Bool :=
  m.verdict == .nonhalts &&
    ((m.prog.stripPrefix q).isSome || (m.prog.stripPrefix q.mirror).isSome)

theorem Solved.not_halts_of_extends {m : Solved} {q : Program} (h : m.extends q = true) :
    ¬ q.init.Halts := by
  simp only [Solved.extends, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true,
    Option.isSome_iff_exists] at h
  obtain ⟨hv, ⟨r, hr⟩ | ⟨r, hr⟩⟩ := h
  · have hm := m.correct
    rw [hv] at hm
    rw [Program.eq_append_of_stripPrefix hr]
    exact Config.not_halts_append r hm
  · have hm := m.correct
    rw [hv] at hm
    have hq : ¬ q.mirror.init.Halts := by
      rw [Program.eq_append_of_stripPrefix hr]
      exact Config.not_halts_append r hm
    exact fun (hh : q.init.Halts) =>
      hq (hh.imp fun (k : Nat) => (q.sameTime_mirror k).mpr)

def Decider.reduceAt (known : List Solved) (p : Program) (j : Nat) : Bool :=
  match p.init.steps j with
  | none   => false
  | some c => c.blankAt j && known.any fun (m : Solved) => m.extends c.prog

theorem Decider.not_halts_of_reduceAt {known : List Solved} {p : Program} {j : Nat}
    (h : reduceAt known p j = true) : ¬ p.init.Halts := by
  unfold reduceAt at h
  split at h
  · cases h
  · next c hs =>
    simp only [Bool.and_eq_true, List.any_eq_true] at h
    obtain ⟨hb, m, -, hm⟩ := h
    have ht : c.tape = .blank :=
      Config.tape_eq_blank (by simpa using Config.zeroBeyond_steps hs Tape.zeroBeyond_blank) hb
    have hc : c = c.prog.init := by
      obtain ⟨t, q⟩ := c
      simp only at ht
      rw [ht]; rfl
    rw [hc] at hs
    exact Config.not_halts_of_steps hs (Solved.not_halts_of_extends hm)

def Decider.reduce (known : List Solved) (k : Nat) : Decider where
  run := fun (p : Program) =>
    if (List.range (k + 1)).any (reduceAt known p) then .nonhalts else .unknown
  sound := fun (p : Program) => by
    by_cases h : (List.range (k + 1)).any (reduceAt known p) = true
    · simp only [h, ↓reduceIte]
      obtain ⟨j, -, hj⟩ := List.any_eq_true.mp h
      exact not_halts_of_reduceAt hj
    · simp only [h]; trivial

end Bf
