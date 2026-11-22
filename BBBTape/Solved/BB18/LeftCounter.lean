import BBBTape.Solved.Known

namespace BBBTape

open scoped Program Machine

namespace LeftCounter

open Known

def walkBody : Program := .left (.flip (.left ε))

def clearBody : Program := .flip (.right (.right ε))

def outer : Program :=
  .loop (.loop walkBody (.flip (.right (.right (.loop clearBody (.left (.flip ε))))))) ε

def prog : Program := .flip outer

theorem walk (rest : Program) : ∀ (d : Nat) (f : Int → Bool) (p : Int), f (p - 2 * d) = false →
    ∃ (k j : Nat) (g : Int → Bool),
      (Machine.mk (tp f p) (.loop walkBody rest)) ⇒ (k + 1) = some ⟨tp g (p - 2 * j), rest⟩ ∧
      g (p - 2 * j) = false ∧ (∀ i, i < j → g (p - 2 * i) = true) ∧
      (∀ x, (p < x ∨ x ≤ p - 2 * j) → g x = f x) := by
  intro d
  induction d with
  | zero =>
    intro f p h
    have h0 : f p = false := by simpa using h
    exact ⟨0, 0, f, run (step_loop_false h0 _ _) (by simp; rfl), by simpa using h0,
      fun i hi => absurd hi (Nat.not_lt_zero i), fun _ _ => rfl⟩
  | succ d ih =>
    intro f p h
    cases hp : f p with
    | false =>
      exact ⟨0, 0, f, run (step_loop_false hp _ _) (by simp; rfl), by simpa using hp,
        fun i hi => absurd hi (Nat.not_lt_zero i), fun _ _ => rfl⟩
    | true =>
      obtain ⟨k, j, g, hs, hg0, hg1, hg2⟩ :=
        ih (flp f (p - 1)) (p - 2) (by rw [flp_ne (by omega), ← h]; congr 1; omega)
      refine ⟨k + 4, j + 1, g, ?_, ?_, ?_, ?_⟩
      · refine run (step_loop_true hp _ _) (run (step_left _ _ _) (run (step_flip _ _ _)
          (run (step_left _ _ _) ?_)))
        rw [show p - 1 - 1 = p - 2 by omega, show p - 2 * ↑(j + 1) = p - 2 - 2 * ↑j by omega]
        exact hs
      · rw [show p - 2 * ↑(j + 1) = p - 2 - 2 * ↑j by omega]; exact hg0
      · intro i hi
        cases i with
        | zero => rw [show p - 2 * ↑(0 : Nat) = p by omega, hg2 p (.inl (by omega)),
            flp_ne (by omega), hp]
        | succ i => rw [show p - 2 * ↑(i + 1) = p - 2 - 2 * ↑i by omega]; exact hg1 i (by omega)
      · intro x hx
        rw [hg2 x (by omega), flp_ne (by omega)]

theorem clear (rest : Program) : ∀ (c : Nat) (f : Int → Bool) (p : Int),
    (∀ i, i < c → f (p + 2 * i) = true) → f (p + 2 * c) = false →
    ∃ (k : Nat) (g : Int → Bool),
      (Machine.mk (tp f p) (.loop clearBody rest)) ⇒ (k + 1) = some ⟨tp g (p + 2 * c), rest⟩ ∧
      (∀ x, (x < p ∨ p + 2 * c ≤ x ∨ x % 2 ≠ p % 2) → g x = f x) := by
  intro c
  induction c with
  | zero =>
    intro f p _ h
    have h0 : f p = false := by simpa using h
    exact ⟨0, f, run (step_loop_false h0 _ _) (by simp; rfl), fun _ _ => rfl⟩
  | succ c ih =>
    intro f p h1 h
    have hp : f p = true := by simpa using h1 0 (by omega)
    obtain ⟨k, g, hs, hg⟩ := ih (flp f p) (p + 2)
      (fun i hi => by rw [flp_ne (by omega), ← h1 (i + 1) (by omega)]; congr 1; omega)
      (by rw [flp_ne (by omega), ← h]; congr 1; omega)
    refine ⟨k + 4, g, ?_, ?_⟩
    · refine run (step_loop_true hp _ _) (run (step_flip _ _ _) (run (step_right _ _ _)
        (run (step_right _ _ _) ?_)))
      rw [show p + 1 + 1 = p + 2 by omega, show p + 2 * ↑(c + 1) = p + 2 + 2 * ↑c by omega]
      exact hs
    · intro x hx
      rw [hg x (by omega), flp_ne (by omega)]

def Inv (f : Int → Bool) (p : Int) : Prop :=
  f p = true ∧ (∀ x, p < x → f x = false) ∧ ∃ N : Int, ∀ x, x < N → f x = false

theorem iter {f : Int → Bool} {p : Int} (hi : Inv f p) :
    ∃ (k : Nat) (f' : Int → Bool) (p' : Int),
      (Machine.mk (tp f p) outer) ⇒ (k + 1) = some ⟨tp f' p', outer⟩ ∧ Inv f' p' := by
  obtain ⟨hfp, hright, N, hN⟩ := hi
  have hpN : N ≤ p := by
    refine Int.not_lt.mp fun hlt => ?_
    rw [hN p hlt] at hfp; cases hfp
  obtain ⟨k₁, j, g, hs₁, hg0, hg1, hg2⟩ :=
    walk (.flip (.right (.right (.loop clearBody (.left (.flip outer))))))
      ((p - N).toNat + 1) f p (hN _ (by omega))
  have hj : 0 < j := by
    refine Nat.pos_of_ne_zero fun h0 => ?_
    subst h0
    have := hg2 p (.inr (by omega))
    rw [show p - 2 * ↑(0 : Nat) = p by omega] at hg0
    rw [hg0, hfp] at this; cases this
  obtain ⟨k₂, h, hs₂, hh⟩ :=
    clear (.left (.flip outer)) j (flp g (p - 2 * j)) (p - 2 * j + 2)
      (fun i hi => by
        rw [flp_ne (by omega), ← hg1 (j - 1 - i) (by omega)]; congr 1; omega)
      (by rw [flp_ne (by omega), hg2 _ (.inl (by omega))]; exact hright _ (by omega))
  refine ⟨k₁ + k₂ + 7, flp h (p + 2 - 1), p + 2 - 1, ?_, ?_, ?_, ?_⟩
  · refine run (step_loop_true hfp _ _) ?_
    rw [show k₁ + k₂ + 7 = (k₁ + 1) + (k₂ + 6) by omega, Machine.steps_add]
    refine (congrArg (·.bind (·⇒(k₂ + 6))) hs₁).trans ?_
    simp only [Option.bind_some]
    refine run (step_flip _ _ _) (run (step_right _ _ _) (run (step_right _ _ _) ?_))
    rw [show k₂ + 3 = (k₂ + 1) + 2 by omega, Machine.steps_add,
      show p - 2 * ↑j + 1 + 1 = p - 2 * ↑j + 2 by omega, hs₂, Option.bind_some,
      show p - 2 * ↑j + 2 + 2 * ↑j = p + 2 by omega]
    exact run (step_left _ _ _) (run (step_flip _ _ _) rfl)
  · rw [flp_eq, hh _ (.inr (.inr (by omega))), flp_ne (by omega), hg2 _ (.inl (by omega)),
      hright _ (by omega)]
    rfl
  · intro x hx
    rw [flp_ne (by omega), hh _ (.inr (.inl (by omega))), flp_ne (by omega),
      hg2 _ (.inl (by omega)), hright _ (by omega)]
  · refine ⟨min N (p - 2 * j), fun x hx => ?_⟩
    rw [flp_ne (by omega), hh _ (.inl (by omega)), flp_ne (by omega),
      hg2 _ (.inr (by omega)), hN _ (by omega)]

theorem outer_diverges {f : Int → Bool} {p : Int} (hi : Inv f p) :
    (Machine.mk (tp f p) outer)⇑ := by
  refine Machine.Progress.diverges (S := fun m => ∃ f p, m = ⟨tp f p, outer⟩ ∧ Inv f p) ?_
    ⟨f, p, rfl, hi⟩
  rintro m ⟨f, p, rfl, hi⟩
  obtain ⟨k, f', p', hs, hi'⟩ := iter hi
  exact ⟨k + 1, _, by omega, hs, f', p', rfl, hi'⟩

theorem diverges : prog⇑ :=
  diverges_of_tp (k := 1) (f := flp (fun _ => false) 0) (p := 0)
    (run (step_flip (fun _ => false) 0 outer) rfl)
    (outer_diverges ⟨by simp [flp], fun x hx => by simp [flp]; omega,
      0, fun x hx => by simp [flp]; omega⟩)

end LeftCounter

def Decider.leftCounter : Decider := Decider.known LeftCounter.prog LeftCounter.diverges

end BBBTape
