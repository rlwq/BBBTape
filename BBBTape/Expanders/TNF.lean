import BBBTape.Core.Expander
import BBBTape.Core.Mirror

namespace BBBTape

namespace Program

open scoped Program Machine

def shiftTape (t : SpecTape) (δ : Int) : SpecTape := fun i => t (i + δ)

theorem shiftTape_zero (t : SpecTape) : shiftTape t 0 = t := by
  funext i; simp [shiftTape]

theorem shiftTape_add (t : SpecTape) (δ₁ δ₂ : Int) :
    shiftTape (shiftTape t δ₁) δ₂ = shiftTape t (δ₁ + δ₂) := by
  funext i; show t (i + δ₂ + δ₁) = t (i + (δ₁ + δ₂)); congr 1; omega

theorem specTape_flip_flip (t : SpecTape) : Tape.flip (Tape.flip t) = t := by
  funext i
  show (if i = 0 then !(if (0 : Int) = 0 then !t 0 else t 0) else if i = 0 then !t 0 else t i) = t i
  by_cases h : i = 0 <;> simp [h]

theorem steps_rep_shift (f : Program → Program) (δ : Int)
    (hstep : ∀ t p, (Machine.mk t (f p))⇒ = some ⟨shiftTape t δ, p⟩) :
    ∀ (n : Nat) (t : SpecTape) (r : Program), (Machine.mk t (rep f n r)) ⇒ n = some ⟨shiftTape t (n * δ), r⟩
  | 0,     t, r => by simp [rep, Machine.steps, shiftTape_zero]
  | n + 1, t, r => by
    simp only [rep, Machine.steps, hstep, Option.bind_some, steps_rep_shift f δ hstep n, shiftTape_add]
    congr 2; funext i; show t (i + (δ + ↑n * δ)) = t (i + ↑(n + 1) * δ)
    rw [Int.natCast_succ, Int.add_mul, Int.one_mul, Int.add_comm δ]

theorem steps_rep_flip2 : ∀ (m : Nat) (t : SpecTape) (r : Program),
    (Machine.mk t (rep .flip (2 * m) r)) ⇒ (2 * m) = some ⟨t, r⟩
  | 0,     _, _ => rfl
  | m + 1, t, r => by
    rw [show 2 * (m + 1) = 2 * m + 2 by omega]
    simp only [rep, Machine.steps, Machine.step, Option.bind_some, specTape_flip_flip]
    exact steps_rep_flip2 m t r

def StepEquiv (s₁ s₂ : Program) : Prop :=
  ∃ d : Nat, 0 < d ∧ ∀ t : SpecTape, ∃ t' : SpecTape, ∀ r : Program,
    (Machine.mk t (s₁ ++ r)) ⇒ d = some ⟨t', r⟩ ∧
    (Machine.mk t (s₂ ++ r)) ⇒ d = some ⟨t', r⟩

def StepDom (s₁ s₂ : Program) : Prop :=
  ∀ t : SpecTape,
    (∀ r : Program, (Machine.mk t (s₁ ++ r))⇑) ∨
      ∃ (d₁ d₂ : Nat) (t' : SpecTape), 0 < d₁ ∧ d₁ ≤ d₂ ∧
        ∀ r : Program,
          (Machine.mk t (s₁ ++ r)) ⇒ d₁ = some ⟨t', r⟩ ∧
          (Machine.mk t (s₂ ++ r)) ⇒ d₂ = some ⟨t', r⟩

theorem StepEquiv.stepDom {s₁ s₂ : Program} (h : StepEquiv s₁ s₂) : StepDom s₁ s₂ := by
  obtain ⟨d, hd, hst⟩ := h
  intro t
  obtain ⟨t', hr⟩ := hst t
  exact .inr ⟨d, d, t', hd, Nat.le_refl d, hr⟩

theorem stepDom_emptyLoop : StepDom (.loop ε ε) (.flip (.flip ε)) := by
  intro t
  by_cases h0 : Tape.cells t 0 = true
  · left
    intro r
    simp only [loop_append, nil_append]
    refine Machine.Progress.diverges (S := fun m => m = ⟨t, .loop ε r⟩) ?_ rfl
    rintro m rfl
    exact ⟨1, ⟨t, .loop ε r⟩, by decide, by simp [Machine.steps, Machine.step, h0], rfl⟩
  · right
    have hf : Tape.cells t 0 = false := by cases h : Tape.cells t 0 <;> simp_all
    refine ⟨1, 2, t, by decide, by decide, fun r => ⟨?_, ?_⟩⟩
    · simp [loop_append, nil_append, Machine.steps, Machine.step, hf]
    · simp [flip_append, nil_append, Machine.steps, Machine.step, specTape_flip_flip]

inductive Congr (s₁ s₂ : Program) : Program → Program → Prop
  | nil   : Congr s₁ s₂ ε ε
  | left  {p q : Program} : Congr s₁ s₂ p q → Congr s₁ s₂ (.left p) (.left q)
  | right {p q : Program} : Congr s₁ s₂ p q → Congr s₁ s₂ (.right p) (.right q)
  | flip  {p q : Program} : Congr s₁ s₂ p q → Congr s₁ s₂ (.flip p) (.flip q)
  | loop  {b b' p q : Program} :
      Congr s₁ s₂ b b' → Congr s₁ s₂ p q → Congr s₁ s₂ (.loop b p) (.loop b' q)
  | swap  {p q : Program} : Congr s₁ s₂ p q → Congr s₁ s₂ (s₁ ++ p) (s₂ ++ q)

theorem Congr.refl {s₁ s₂ p : Program} : p° → Congr s₁ s₂ p p := by
  intro hp
  induction p with
  | nil => exact .nil
  | left _ ih => exact .left (ih hp)
  | right _ ih => exact .right (ih hp)
  | flip _ ih => exact .flip (ih hp)
  | loop _ _ ihb ihp => exact .loop (ihb hp.1) (ihp hp.2)
  | gap => exact absurd hp id

theorem Congr.symm {s₁ s₂ p q : Program} : Congr s₁ s₂ p q → Congr s₂ s₁ q p := by
  intro h
  induction h with
  | nil => exact .nil
  | left _ ih => exact .left ih
  | right _ ih => exact .right ih
  | flip _ ih => exact .flip ih
  | loop _ _ ihb ihp => exact .loop ihb ihp
  | swap _ ih => exact .swap ih

theorem Congr.append {s₁ s₂ a a' x x' : Program} :
    Congr s₁ s₂ a a' → Congr s₁ s₂ x x' → Congr s₁ s₂ (a ++ x) (a' ++ x') := by
  intro ha hx
  induction ha with
  | nil => exact hx
  | left _ ih => exact .left ih
  | right _ ih => exact .right ih
  | flip _ ih => exact .flip ih
  | loop hb _ _ ihp => exact .loop hb ihp
  | swap _ ih => rw [append_assoc, append_assoc]; exact .swap ih

theorem Congr.dominates_machine {s₁ s₂ p q : Program} {t : SpecTape} {k : Nat} :
    StepDom s₁ s₂ → Congr s₁ s₂ p q →
      ((Machine.mk t p) ⇓ k) → ∃ k' : Nat, k ≤ k' ∧ ((Machine.mk t q) ⇓ k') := by
  intro hsd
  induction k using Nat.strongRecOn generalizing p q t with
  | _ k ih =>
    intro hc hk
    cases hc with
    | nil => exact ⟨k, Nat.le_refl k, hk⟩
    | left h | right h | flip h =>
      cases k with
      | zero => rw [Machine.haltsIn_zero] at hk; cases hk
      | succ k =>
        obtain ⟨k', hle, hk'⟩ := ih k (by omega) h ((Machine.haltsIn_succ rfl).mp hk)
        exact ⟨k' + 1, by omega, (Machine.haltsIn_succ rfl).mpr hk'⟩
    | @loop b b' p q hb hp =>
      cases k with
      | zero => rw [Machine.haltsIn_zero] at hk; cases hk
      | succ k =>
        have hnext : Congr s₁ s₂ (if Tape.cells t 0 then b ++ .loop b p else p)
            (if Tape.cells t 0 then b' ++ .loop b' q else q) := by
          cases Tape.cells t 0
          · exact hp
          · exact hb.append (.loop hb hp)
        obtain ⟨k', hle, hk'⟩ := ih k (by omega) hnext ((Machine.haltsIn_succ rfl).mp hk)
        exact ⟨k' + 1, by omega, (Machine.haltsIn_succ rfl).mpr hk'⟩
    | @swap p q h =>
      rcases hsd t with hdiv | ⟨d₁, d₂, t', hd₁, hle_d, hst⟩
      · exact absurd ⟨k, hk⟩ (Machine.not_halts_of_diverges (hdiv p))
      · obtain ⟨u, hu⟩ := hk
        by_cases hdk : d₁ ≤ k
        · obtain ⟨j, rfl⟩ : ∃ j : Nat, k = d₁ + j := ⟨k - d₁, by omega⟩
          rw [Machine.steps_add, (hst p).1, Option.bind_some] at hu
          obtain ⟨j', hjj', u', hu'⟩ := ih j (by omega) h ⟨u, hu⟩
          refine ⟨d₂ + j', by omega, u', ?_⟩
          rw [Machine.steps_add, (hst q).2, Option.bind_some]
          exact hu'
        · have hnone : (Machine.mk t (s₁ ++ p)) ⇒ (k + 1) = none := by
            rw [Machine.steps_add, hu, Option.bind_some]; rfl
          have hsome := Machine.isSome_steps_of_le (hst p).1 (by omega : k + 1 ≤ d₁)
          rw [hnone] at hsome; cases hsome

theorem Congr.dominates {s₁ s₂ p q : Program} :
    StepDom s₁ s₂ → Congr s₁ s₂ p q → p ≼ q := by
  intro hsd hc k hk
  obtain ⟨k', hle, hk'⟩ := Congr.dominates_machine hsd hc (hk SpecTape)
  exact ⟨k', hle, Program.haltsIn_of hk'⟩

def NonShift : Program → Prop
  | .left _ | .right _ => False
  | _                  => True

def shiftPrefix : Program → Program
  | .left p  => .left (shiftPrefix p)
  | .right p => .right (shiftPrefix p)
  | _        => ε

def shiftTail : Program → Program
  | .left p | .right p => shiftTail p
  | p                  => p

def countL : Program → Nat
  | .left p  => countL p + 1
  | .right p => countL p
  | _        => 0

def countR : Program → Nat
  | .left p  => countR p
  | .right p => countR p + 1
  | _        => 0

theorem shiftPrefix_append_tail (s : Program) : shiftPrefix s ++ shiftTail s = s := by
  induction s <;> simp [shiftPrefix, shiftTail, *]

theorem nonShift_shiftTail (s : Program) : NonShift (shiftTail s) := by
  induction s with
  | left _ ih | right _ ih => exact ih
  | _ => trivial

theorem closed_shiftTail {s : Program} : s° → (shiftTail s)° := by
  induction s with
  | left _ ih | right _ ih => exact ih
  | _ => exact id

theorem size_shiftPrefix (s : Program) : ‖shiftPrefix s‖ = countL s + countR s := by
  induction s <;> simp [shiftPrefix, countL, countR, size, *] <;> omega

theorem shiftPrefix_eq_left {s : Program} : countR s = 0 → shiftPrefix s = rep .left (countL s) ε := by
  induction s with
  | left _ ih => intro hr; simp [shiftPrefix, countL, rep, ih hr]
  | right _ _ => intro hr; simp [countR] at hr
  | _ => intro _; rfl

theorem shiftPrefix_eq_right {s : Program} : countL s = 0 → shiftPrefix s = rep .right (countR s) ε := by
  induction s with
  | right _ ih => intro hl; simp [shiftPrefix, countR, rep, ih hl]
  | left _ _ => intro hl; simp [countL] at hl
  | _ => intro _; rfl

theorem steps_shiftPrefix (s : Program) (t : SpecTape) (r : Program) :
    (Machine.mk t (shiftPrefix s ++ r)) ⇒ (countL s + countR s) =
      some ⟨shiftTape t ((countR s : Int) - (countL s : Int)), r⟩ := by
  induction s generalizing t with
  | left p ih =>
    rw [show countL (.left p) + countR (.left p) = (countL p + countR p) + 1 by simp [countL, countR]; omega]
    simp only [shiftPrefix, left_append, Machine.steps, Machine.step, Option.bind_some]
    change (Machine.mk (shiftTape t (-1)) (shiftPrefix p ++ r)) ⇒ _ = _
    rw [ih, shiftTape_add]
    congr 2; funext i; show t (i + (-1 + ((countR p : Int) - (countL p : Int)))) = _
    simp only [countL, countR, shiftTape]; congr 1; omega
  | right p ih =>
    rw [show countL (.right p) + countR (.right p) = (countL p + countR p) + 1 by simp [countL, countR]; omega]
    simp only [shiftPrefix, right_append, Machine.steps, Machine.step, Option.bind_some]
    change (Machine.mk (shiftTape t 1) (shiftPrefix p ++ r)) ⇒ _ = _
    rw [ih, shiftTape_add]
    congr 2; funext i; show t (i + (1 + ((countR p : Int) - (countL p : Int)))) = _
    simp only [countL, countR, shiftTape]; congr 1; omega
  | _ => simp [shiftPrefix, countL, countR, Machine.steps, shiftTape_zero]

def normShifts (a b : Nat) : Program :=
  rep .flip (2 * min a b) (if b ≤ a then rep .left (a - b) ε else rep .right (b - a) ε)

theorem size_normShifts (a b : Nat) : ‖normShifts a b‖ = a + b := by
  unfold normShifts
  rw [size_rep .flip (fun _ => rfl)]
  split
  · rw [size_rep .left (fun _ => rfl)]; simp [size]; omega
  · rw [size_rep .right (fun _ => rfl)]; simp [size]; omega

theorem closed_normShifts (a b : Nat) : (normShifts a b)° := by
  unfold normShifts
  apply closed_rep .flip (fun _ h => h)
  split
  · exact closed_rep .left (fun _ h => h) trivial
  · exact closed_rep .right (fun _ h => h) trivial

theorem steps_normShifts (a b : Nat) (t : SpecTape) (r : Program) :
    (Machine.mk t (normShifts a b ++ r)) ⇒ (a + b) =
      some ⟨shiftTape t ((b : Int) - (a : Int)), r⟩ := by
  unfold normShifts
  split
  · next hba =>
    rw [show a + b = 2 * min a b + (a - b) by omega, Machine.steps_add,
      rep_append .flip flip_append, steps_rep_flip2, Option.bind_some,
      rep_append .left left_append, nil_append,
      steps_rep_shift .left (-1) (fun _ _ => rfl)]
    congr 2; funext i; show t (i + ↑(a - b) * (-1)) = t (i + (↑b - ↑a)); congr 1; omega
  · next hba =>
    rw [show a + b = 2 * min a b + (b - a) by omega, Machine.steps_add,
      rep_append .flip flip_append, steps_rep_flip2, Option.bind_some,
      rep_append .right right_append, nil_append,
      steps_rep_shift .right 1 (fun _ _ => rfl)]
    congr 2; funext i; show t (i + ↑(b - a) * 1) = t (i + (↑b - ↑a)); congr 1; omega

theorem normShifts_eq_flip {a b : Nat} (ha : 0 < a) (hb : 0 < b) :
    ∃ u : Program, u° ∧ ‖u‖ = a + b - 1 ∧ normShifts a b = .flip u := by
  obtain ⟨k, hk⟩ : ∃ k : Nat, 2 * min a b = k + 1 := ⟨2 * min a b - 1, by omega⟩
  refine ⟨rep .flip k (if b ≤ a then rep .left (a - b) ε else rep .right (b - a) ε), ?_, ?_, ?_⟩
  · apply closed_rep .flip (fun _ h => h)
    split
    · exact closed_rep .left (fun _ h => h) trivial
    · exact closed_rep .right (fun _ h => h) trivial
  · rw [size_rep .flip (fun _ => rfl)]
    split
    · rw [size_rep .left (fun _ => rfl)]; simp [size]; omega
    · rw [size_rep .right (fun _ => rfl)]; simp [size]; omega
  · unfold normShifts; rw [hk]; rfl

def nonShiftShapes (r : Nat) : List Program :=
  if r = 0 then [ε]
  else
    [.flip (gap? (r - 1))] ++
      (List.range (r - 2)).map fun (a : Nat) => .loop (gap? (a + 1)) (gap? (r - 3 - a))

theorem nonShiftShapes_cover {r : Program} :
    r° → NonShift r →
      (∃ c ∈ nonShiftShapes ‖r‖, r ⊑ c) ∨
      (∃ s₁ s₂ r' : Program, StepDom s₁ s₂ ∧ r'° ∧ ‖r'‖ = ‖r‖ ∧
        (∃ c ∈ nonShiftShapes ‖r‖, r' ⊑ c) ∧ Congr s₁ s₂ r r') := by
  intro hr hns
  cases r with
  | nil => exact .inl ⟨ε, by simp [nonShiftShapes, size], .nil⟩
  | left _ | right _ => exact absurd hns id
  | gap => exact absurd hr id
  | flip p =>
    exact .inl ⟨.flip (gap? ‖p‖), by simp [nonShiftShapes, size], .flip (refines_gap? hr rfl)⟩
  | loop b p =>
    by_cases hb0 : ‖b‖ = 0
    · have hbe : b = ε := size_eq_zero_of_closed hr.1 hb0
      subst hbe
      refine .inr ⟨.loop ε ε, .flip (.flip ε), .flip (.flip p), stepDom_emptyLoop,
        hr.2, by simp [size], ?_, ?_⟩
      · refine ⟨.flip (gap? (‖p‖ + 1)), by simp [nonShiftShapes, size],
          .flip (refines_gap? (by exact hr.2) (by simp [size]))⟩
      · exact Congr.swap (s₁ := .loop ε ε) (s₂ := .flip (.flip ε)) (Congr.refl hr.2)
    · refine .inl ⟨.loop (gap? ‖b‖) (gap? ‖p‖), ?_,
        .loop (refines_gap? hr.1 rfl) (refines_gap? hr.2 rfl)⟩
      simp only [nonShiftShapes, size, show ¬ (‖b‖ + ‖p‖ + 2 = 0) by omega, ↓reduceIte,
        List.mem_append]
      refine .inr (List.mem_map.mpr ⟨‖b‖ - 1, List.mem_range.mpr (by omega), ?_⟩)
      congr 2 <;> omega

def shapes (noShift : Bool) (k : Nat) : List Program :=
  if k = 0 then [ε]
  else
    let ls := (List.range k).flatMap fun (i : Nat) =>
      (nonShiftShapes (k - 1 - i)).map (rep .left (i + 1))
    let rs := if noShift then [] else (List.range k).flatMap fun (i : Nat) =>
      (nonShiftShapes (k - 1 - i)).map (rep .right (i + 1))
    ls ++ rs ++ nonShiftShapes k

theorem mem_flatMap_rep {f : Program → Program} {k m r : Nat} {c : Program}
    (hm : 0 < m) (hsz : k = m + r) (hc : c ∈ nonShiftShapes r) :
    rep f m c ∈ (List.range k).flatMap fun (i : Nat) => (nonShiftShapes (k - 1 - i)).map (rep f (i + 1)) := by
  simp only [List.mem_flatMap, List.mem_range, List.mem_map]
  exact ⟨m - 1, by omega, c, by rwa [show k - 1 - (m - 1) = r by omega], by rw [show m - 1 + 1 = m by omega]⟩

theorem Congr.rep (f : Program → Program)
    (hf : ∀ {p q s₁ s₂}, Congr s₁ s₂ p q → Congr s₁ s₂ (f p) (f q)) :
    ∀ {n p q s₁ s₂}, Congr s₁ s₂ p q → Congr s₁ s₂ (Program.rep f n p) (Program.rep f n q)
  | 0,     _, _, _, _, h => h
  | _ + 1, _, _, _, _, h => hf (Congr.rep f hf h)

theorem shapes_cover (noShift : Bool) {s : Program} :
    s° →
      ∃ c ∈ shapes noShift ‖s‖,
        s ⊑ c ∨
        (noShift = true ∧ s.mirror ⊑ c) ∨
        (∃ s₁ s₂ s' : Program,
          StepDom s₁ s₂ ∧ s'° ∧ ‖s'‖ = ‖s‖ ∧ s' ⊑ c ∧
          (Congr s₁ s₂ s s' ∨ (noShift = true ∧ Congr s₁ s₂ s.mirror s'))) := by
  intro hs
  by_cases h0 : ‖s‖ = 0
  · rw [size_eq_zero_of_closed hs h0]; exact ⟨ε, by simp [shapes, size], .inl .nil⟩
  · have hsp := shiftPrefix_append_tail s
    have hsz : ‖s‖ = countL s + countR s + ‖shiftTail s‖ := by
      have := congrArg size hsp; rw [size_append, size_shiftPrefix] at this; exact this.symm
    have ht_cl := closed_shiftTail hs
    have ht_ns := nonShift_shiftTail s
    by_cases ha : countL s = 0
    · by_cases hb : countR s = 0
      · have hst : shiftTail s = s := by
          simpa [shiftPrefix_eq_left hb, ha, rep] using hsp
        rcases nonShiftShapes_cover ht_cl ht_ns with
          ⟨c, hc, hrc⟩ | ⟨s₁, s₂, r', hsd, hr'_cl, hr'_sz, ⟨c, hc, hrc⟩, hcr⟩
        · rw [hst] at hc hrc
          exact ⟨c, by simp only [shapes, h0, ↓reduceIte, List.mem_append]; exact .inr hc, .inl hrc⟩
        · rw [hst] at hc hr'_sz hcr
          exact ⟨c, by simp only [shapes, h0, ↓reduceIte, List.mem_append]; exact .inr hc,
            .inr (.inr ⟨s₁, s₂, r', hsd, hr'_cl, hr'_sz, hrc, .inl hcr⟩)⟩
      · have hseq : s = rep .right (countR s) (shiftTail s) := by
          simpa [shiftPrefix_eq_right ha, rep_append .right right_append] using hsp.symm
        cases noShift with
        | false =>
          rcases nonShiftShapes_cover ht_cl ht_ns with
            ⟨c, hc, hrc⟩ | ⟨s₁, s₂, r', hsd, hr'_cl, hr'_sz, ⟨c, hc, hrc⟩, hcr⟩
          · refine ⟨rep .right (countR s) c, ?_, .inl ?_⟩
            · simp only [shapes, h0, ↓reduceIte, Bool.false_eq_true, List.mem_append]
              exact .inl (.inr (mem_flatMap_rep (by omega) (by omega) hc))
            · have hr := refines_rep .right (fun h => .right h) (n := countR s) hrc
              rwa [← hseq] at hr
          · refine ⟨rep .right (countR s) c, ?_,
              .inr (.inr ⟨s₁, s₂, rep .right (countR s) r', hsd,
                closed_rep .right (fun _ h => h) hr'_cl,
                by rw [size_rep .right (fun _ => rfl), hr'_sz]; omega,
                refines_rep .right (fun h => .right h) hrc,
                .inl (by
                  have hcr' := Congr.rep .right Congr.right (n := countR s) hcr
                  rwa [← hseq] at hcr')⟩)⟩
            simp only [shapes, h0, ↓reduceIte, Bool.false_eq_true, List.mem_append]
            exact .inl (.inr (mem_flatMap_rep (by omega) (by omega) hc))
        | true =>
          have htm_ns : NonShift (shiftTail s).mirror := by
            cases h : shiftTail s with
            | left _ | right _ => rw [h] at ht_ns; exact absurd ht_ns id
            | _ => simp [mirror, NonShift]
          have hsm : s.mirror = rep .left (countR s) (shiftTail s).mirror := by
            rw [← mirror_rep_right, ← hseq]
          rcases nonShiftShapes_cover (closed_mirror ht_cl) htm_ns with
            ⟨c, hc, hrc⟩ | ⟨s₁, s₂, r', hsd, hr'_cl, hr'_sz, ⟨c, hc, hrc⟩, hcr⟩
          · refine ⟨rep .left (countR s) c, ?_, .inr (.inl ⟨rfl, ?_⟩)⟩
            · simp only [shapes, h0, ↓reduceIte, List.mem_append]
              exact .inl (.inl (mem_flatMap_rep (by omega) (by rw [size_mirror]; omega) hc))
            · have hr := refines_rep .left (fun h => .left h) (n := countR s) hrc
              rwa [← hsm] at hr
          · rw [size_mirror] at hr'_sz hc
            refine ⟨rep .left (countR s) c, ?_,
              .inr (.inr ⟨s₁, s₂, rep .left (countR s) r', hsd,
                closed_rep .left (fun _ h => h) hr'_cl,
                by rw [size_rep .left (fun _ => rfl), hr'_sz]; omega,
                refines_rep .left (fun h => .left h) hrc,
                .inr ⟨rfl, by
                  have hcr' := Congr.rep .left Congr.left (n := countR s) hcr
                  rwa [← hsm] at hcr'⟩⟩)⟩
            simp only [shapes, h0, ↓reduceIte, List.mem_append]
            exact .inl (.inl (mem_flatMap_rep (by omega) (by omega) hc))
    · by_cases hb : countR s = 0
      · have hseq : s = rep .left (countL s) (shiftTail s) := by
          simpa [shiftPrefix_eq_left hb, rep_append .left left_append] using hsp.symm
        rcases nonShiftShapes_cover ht_cl ht_ns with
          ⟨c, hc, hrc⟩ | ⟨s₁, s₂, r', hsd, hr'_cl, hr'_sz, ⟨c, hc, hrc⟩, hcr⟩
        · refine ⟨rep .left (countL s) c, ?_, .inl ?_⟩
          · simp only [shapes, h0, ↓reduceIte, List.mem_append]
            exact .inl (.inl (mem_flatMap_rep (by omega) (by omega) hc))
          · have hr := refines_rep .left (fun h => .left h) (n := countL s) hrc
            rwa [← hseq] at hr
        · refine ⟨rep .left (countL s) c, ?_,
            .inr (.inr ⟨s₁, s₂, rep .left (countL s) r', hsd,
              closed_rep .left (fun _ h => h) hr'_cl,
              by rw [size_rep .left (fun _ => rfl), hr'_sz]; omega,
              refines_rep .left (fun h => .left h) hrc,
              .inl (by
                have hcr' := Congr.rep .left Congr.left (n := countL s) hcr
                rwa [← hseq] at hcr')⟩)⟩
          simp only [shapes, h0, ↓reduceIte, List.mem_append]
          exact .inl (.inl (mem_flatMap_rep (by omega) (by omega) hc))
      · obtain ⟨u, hu_cl, hu_sz, hnorm⟩ :=
          normShifts_eq_flip (Nat.pos_of_ne_zero ha) (Nat.pos_of_ne_zero hb)
        have hse : StepEquiv (shiftPrefix s) (normShifts (countL s) (countR s)) :=
          ⟨countL s + countR s, by omega, fun t =>
            ⟨shiftTape t ((countR s : Int) - (countL s : Int)), fun r =>
              ⟨steps_shiftPrefix s t r, steps_normShifts (countL s) (countR s) t r⟩⟩⟩
        refine ⟨.flip (gap? (‖s‖ - 1)), ?_, .inr (.inr ⟨shiftPrefix s, normShifts (countL s) (countR s),
          normShifts (countL s) (countR s) ++ shiftTail s, hse.stepDom,
          closed_append (closed_normShifts _ _) ht_cl,
          by rw [size_append, size_normShifts]; omega, ?_, .inl ?_⟩)⟩
        · simp only [shapes, h0, ↓reduceIte, List.mem_append, nonShiftShapes, List.mem_singleton]
          exact .inr (.inl trivial)
        · rw [hnorm, flip_append]
          exact .flip (refines_gap? (closed_append hu_cl ht_cl) (by rw [size_append, hu_sz]; omega))
        · have hsw := Congr.swap (s₁ := shiftPrefix s) (s₂ := normShifts (countL s) (countR s))
            (Congr.refl ht_cl)
          rwa [hsp] at hsw

theorem subst_cover {i k : Nat} {p q : Program} :
    gapSize? i q = some k → p° → p ⊑ q →
      ∃ s : Program, s° ∧ ‖s‖ = k ∧
        (∀ c : Program, s ⊑ c → p ⊑ q[i ↦ c]) ∧
        (∀ c : Program, s.mirror ⊑ c → p.mirror ⊑ q.mirror[i ↦ c]) ∧
        (∀ s₁ s₂ s' c : Program, s'° → s' ⊑ c → Congr s₁ s₂ s s' →
          ∃ p' : Program, p'° ∧ p' ⊑ q[i ↦ c] ∧ Congr s₁ s₂ p p') ∧
        (∀ s₁ s₂ s' c : Program, s'° → s' ⊑ c → Congr s₁ s₂ s.mirror s' →
          ∃ p' : Program, p'° ∧ p' ⊑ q.mirror[i ↦ c] ∧ Congr s₁ s₂ p.mirror p') := by
  intro hg hp hpq
  induction hpq generalizing i with
  | nil => cases hg
  | left _ ih =>
    obtain ⟨s, hs, hk, hc, hcm, hcg, hcgm⟩ := ih hg hp
    exact ⟨s, hs, hk, fun c h => .left (hc c h), fun c h => .right (hcm c h),
      fun s₁ s₂ s' c hs' hsc hcs =>
        let ⟨p', hp', hp'c, hcp⟩ := hcg s₁ s₂ s' c hs' hsc hcs; ⟨.left p', hp', .left hp'c, .left hcp⟩,
      fun s₁ s₂ s' c hs' hsc hcs =>
        let ⟨p', hp', hp'c, hcp⟩ := hcgm s₁ s₂ s' c hs' hsc hcs; ⟨.right p', hp', .right hp'c, .right hcp⟩⟩
  | right _ ih =>
    obtain ⟨s, hs, hk, hc, hcm, hcg, hcgm⟩ := ih hg hp
    exact ⟨s, hs, hk, fun c h => .right (hc c h), fun c h => .left (hcm c h),
      fun s₁ s₂ s' c hs' hsc hcs =>
        let ⟨p', hp', hp'c, hcp⟩ := hcg s₁ s₂ s' c hs' hsc hcs; ⟨.right p', hp', .right hp'c, .right hcp⟩,
      fun s₁ s₂ s' c hs' hsc hcs =>
        let ⟨p', hp', hp'c, hcp⟩ := hcgm s₁ s₂ s' c hs' hsc hcs; ⟨.left p', hp', .left hp'c, .left hcp⟩⟩
  | flip _ ih =>
    obtain ⟨s, hs, hk, hc, hcm, hcg, hcgm⟩ := ih hg hp
    exact ⟨s, hs, hk, fun c h => .flip (hc c h), fun c h => .flip (hcm c h),
      fun s₁ s₂ s' c hs' hsc hcs =>
        let ⟨p', hp', hp'c, hcp⟩ := hcg s₁ s₂ s' c hs' hsc hcs; ⟨.flip p', hp', .flip hp'c, .flip hcp⟩,
      fun s₁ s₂ s' c hs' hsc hcs =>
        let ⟨p', hp', hp'c, hcp⟩ := hcgm s₁ s₂ s' c hs' hsc hcs; ⟨.flip p', hp', .flip hp'c, .flip hcp⟩⟩
  | @loop b' b p q hb hp_ref ihb ihp =>
    simp only [gapSize?] at hg
    split at hg
    · next hi =>
      obtain ⟨s, hs, hk, hc, hcm, hcg, hcgm⟩ := ihb hg hp.1
      refine ⟨s, hs, hk,
        fun c h => by simp only [subst, hi, ↓reduceIte]; exact .loop (hc c h) hp_ref,
        fun c h => by simp only [mirror, subst, numGaps_mirror, hi, ↓reduceIte]; exact .loop (hcm c h) hp_ref.mirror,
        fun s₁ s₂ s' c hs' hsc hcs => ?_,
        fun s₁ s₂ s' c hs' hsc hcs => ?_⟩
      · obtain ⟨b'', hb'', hb''c, hcb⟩ := hcg s₁ s₂ s' c hs' hsc hcs
        exact ⟨.loop b'' p, ⟨hb'', hp.2⟩,
          by simp only [subst, hi, ↓reduceIte]; exact .loop hb''c hp_ref, .loop hcb (Congr.refl hp.2)⟩
      · obtain ⟨b'', hb'', hb''c, hcb⟩ := hcgm s₁ s₂ s' c hs' hsc hcs
        exact ⟨.loop b'' p.mirror, ⟨hb'', closed_mirror hp.2⟩,
          by simp only [mirror, subst, numGaps_mirror, hi, ↓reduceIte]; exact .loop hb''c hp_ref.mirror,
          .loop hcb (Congr.refl (closed_mirror hp.2))⟩
    · next hi =>
      obtain ⟨s, hs, hk, hc, hcm, hcg, hcgm⟩ := ihp hg hp.2
      refine ⟨s, hs, hk,
        fun c h => by simp only [subst, hi, ↓reduceIte]; exact .loop hb (hc c h),
        fun c h => by simp only [mirror, subst, numGaps_mirror, hi, ↓reduceIte]; exact .loop hb.mirror (hcm c h),
        fun s₁ s₂ s' c hs' hsc hcs => ?_,
        fun s₁ s₂ s' c hs' hsc hcs => ?_⟩
      · obtain ⟨p'', hp'', hp''c, hcp⟩ := hcg s₁ s₂ s' c hs' hsc hcs
        exact ⟨.loop b' p'', ⟨hp.1, hp''⟩,
          by simp only [subst, hi, ↓reduceIte]; exact .loop hb hp''c, .loop (Congr.refl hp.1) hcp⟩
      · obtain ⟨p'', hp'', hp''c, hcp⟩ := hcgm s₁ s₂ s' c hs' hsc hcs
        exact ⟨.loop b'.mirror p'', ⟨closed_mirror hp.1, hp''⟩,
          by simp only [mirror, subst, numGaps_mirror, hi, ↓reduceIte]; exact .loop hb.mirror hp''c,
          .loop (Congr.refl (closed_mirror hp.1)) hcp⟩
  | @gap m _ s₀ p' q' hm hp_ref ihp =>
    obtain ⟨hs₀, hp'⟩ := closed_of_append hp
    cases i with
    | zero =>
      simp only [gapSize?, Option.some.injEq] at hg; subst hg
      exact ⟨s₀, hs₀, hm,
        fun c h => h.append hp_ref,
        fun c h => by rw [mirror_append]; exact h.append hp_ref.mirror,
        fun _ _ s' c hs' hsc hcs =>
          ⟨s' ++ p', closed_append hs' hp', hsc.append hp_ref, hcs.append (Congr.refl hp')⟩,
        fun _ _ s' c hs' hsc hcs =>
          ⟨s' ++ p'.mirror, closed_append hs' (closed_mirror hp'),
            by rw [mirror]; exact hsc.append hp_ref.mirror,
            by rw [mirror_append]; exact hcs.append (Congr.refl (closed_mirror hp'))⟩⟩
    | succ j =>
      obtain ⟨s, hs, hk, hc, hcm, hcg, hcgm⟩ := ihp hg hp'
      exact ⟨s, hs, hk,
        fun c h => Refines.gap hm (hc c h),
        fun c h => by rw [mirror_append]; exact Refines.gap (by rw [size_mirror, hm]) (hcm c h),
        fun s₁ s₂ s' c hs' hsc hcs =>
          let ⟨p'', hp'', hp''c, hcp⟩ := hcg s₁ s₂ s' c hs' hsc hcs
          ⟨s₀ ++ p'', closed_append hs₀ hp'', Refines.gap hm hp''c, (Congr.refl hs₀).append hcp⟩,
        fun s₁ s₂ s' c hs' hsc hcs =>
          let ⟨p'', hp'', hp''c, hcp⟩ := hcgm s₁ s₂ s' c hs' hsc hcs
          ⟨s₀.mirror ++ p'', closed_append (closed_mirror hs₀) hp'',
            by rw [mirror]; exact Refines.gap (by rw [size_mirror, hm]) hp''c,
            by rw [mirror_append]; exact (Congr.refl (closed_mirror hs₀)).append hcp⟩⟩

def gapSize : (q : Program) → Fin q.numGaps → Nat
  | ε,         i          => absurd i.isLt (Nat.not_lt_zero _)
  | .left p,   i          => gapSize p i
  | .right p,  i          => gapSize p i
  | .flip p,   i          => gapSize p i
  | .loop b p, i          =>
    if h : i.val < b.numGaps then gapSize b ⟨i.val, h⟩
    else gapSize p ⟨i.val - b.numGaps, by have := i.isLt; simp [numGaps] at this; omega⟩
  | .gap k _ _, ⟨0, _⟩     => k
  | .gap _ _ p, ⟨j + 1, h⟩ => gapSize p ⟨j, by simp [numGaps] at h; omega⟩

theorem gapSize?_eq_some :
    ∀ (q : Program) (i : Fin q.numGaps), gapSize? i.val q = some (gapSize q i)
  | ε,         i          => absurd i.isLt (Nat.not_lt_zero _)
  | .left p,   i          => gapSize?_eq_some p i
  | .right p,  i          => gapSize?_eq_some p i
  | .flip p,   i          => gapSize?_eq_some p i
  | .loop b p, i          => by
    simp only [gapSize?, gapSize]
    split
    · exact gapSize?_eq_some b ⟨i.val, ‹_›⟩
    · exact gapSize?_eq_some p ⟨i.val - b.numGaps, by have := i.isLt; simp [numGaps] at this; omega⟩
  | .gap _ _ _, ⟨0, _⟩     => rfl
  | .gap _ _ p, ⟨j + 1, h⟩ => gapSize?_eq_some p ⟨j, by simp [numGaps] at h; omega⟩

def isBlankGap : Program → Bool
  | .gap _ _ ε => true
  | _          => false

theorem eq_gap_of_isBlankGap {q : Program} (h : q.isBlankGap = true) :
    ∃ (k : Nat) (hk : 0 < k), q = .gap k hk ε := by
  cases q with
  | gap k hk r =>
    cases r with
    | nil => exact ⟨k, hk, rfl⟩
    | _ => cases h
  | _ => cases h

def rootShapes (k : Nat) : List Program :=
  if k = 0 then [ε]
  else
    [rep .left k ε] ++
      ((List.range (k - 4)).map fun (a : Nat) =>
        .flip (.loop (gap? (a + 2)) (gap? (k - 5 - a)))) ++
      ((List.range (k - 2)).map fun (i : Nat) =>
        .flip (rep .left (i + 1) (.flip (gap? (k - 3 - i)))))

theorem steps_append_tail : ∀ (m : Nat) (t t' : SpecTape) (q s : Program),
    (Machine.mk t q) ⇒ m = some ⟨t', ε⟩ →
    (Machine.mk t (q ++ s)) ⇒ m = some ⟨t', s⟩
  | 0, t, t', q, s, h0 => by
    simp only [Machine.steps, Option.some.injEq, Machine.mk.injEq] at h0
    rcases h0 with ⟨rfl, rfl⟩
    rfl
  | m + 1, t, t', q, s, hm => by
    simp only [Machine.steps] at hm ⊢
    cases q with
    | nil | gap => simp only [Machine.step] at hm; cases hm
    | left r | right r | flip r =>
      simp only [left_append, right_append, flip_append, Machine.step, Option.bind_some] at hm ⊢
      exact steps_append_tail m _ _ _ s hm
    | loop b r =>
      simp only [loop_append, Machine.step, Option.bind_some] at hm ⊢
      cases hcell : Tape.cells t 0
      · simp only [hcell, Bool.false_eq_true, ↓reduceIte] at hm ⊢
        exact steps_append_tail m _ _ _ s hm
      · simp only [hcell, ↓reduceIte] at hm ⊢
        rw [← loop_append, ← append_assoc]
        exact steps_append_tail m _ _ _ s hm

theorem Dominates.trans {p q r : Program} (h₁ : p ≼ q) (h₂ : q ≼ r) : p ≼ r := by
  intro k hk
  obtain ⟨k₁, hle₁, hk₁⟩ := h₁ k hk
  obtain ⟨k₂, hle₂, hk₂⟩ := h₂ k₁ hk₁
  exact ⟨k₂, Nat.le_trans hle₁ hle₂, hk₂⟩

theorem rep_left_add : ∀ (a b : Nat), rep .left a ε ++ rep .left b ε = rep .left (a + b) ε
  | 0, _ => by simp [rep]
  | a + 1, b => by rw [Nat.succ_add]; simp [rep, rep_left_add a b]

theorem rep_left_snoc : ∀ (n : Nat) (p : Program), rep .left n (.left p) = rep .left (n + 1) p
  | 0, _ => rfl
  | n + 1, p => by simp [rep, rep_left_snoc n p]

def PadDom (d : Nat) (p q : Program) : Prop :=
  ∀ k : Nat, (p ⇓ k) → ∃ k₀ : Nat, k ≤ k₀ + d ∧ (q ⇓ k₀)

theorem PadDom.to_dominates {d : Nat} {p q q' : Program} (h : PadDom d p q) (hdom : q ≼ q') :
    p ≼ (q' ++ rep .left d ε) := by
  intro k hk
  obtain ⟨k₀, hle₀, hk₀⟩ := h k hk
  obtain ⟨k', hle', hk'⟩ := hdom k₀ hk₀
  obtain ⟨u, hu⟩ := hk' SpecTape
  refine ⟨k' + d, by omega, Program.haltsIn_of ⟨shiftTape u ((d : Nat) * (-1 : Int)), ?_⟩⟩
  show (Machine.mk (Tape.blank : SpecTape) (q' ++ rep .left d ε)) ⇒ (k' + d) = _
  rw [Machine.steps_add, steps_append_tail k' _ _ q' _ hu, Option.bind_some,
    steps_rep_shift .left (-1) (fun _ _ => rfl)]

inductive IsRootCanonical : Program → Prop
  | shifts (k : Nat) : IsRootCanonical (rep .left k ε)
  | loop   (b u : Program) : b° → u° → 2 ≤ ‖b‖ → IsRootCanonical (.flip (.loop b u))
  | flip   (i : Nat) (u : Program) : u° → IsRootCanonical (.flip (rep .left (i + 1) (.flip u)))

theorem IsRootCanonical.closed {p : Program} : IsRootCanonical p → p°
  | .shifts _ => closed_rep .left (fun _ h => h) trivial
  | .loop _ _ hb hu _ => ⟨hb, hu⟩
  | .flip _ _ hu => closed_rep .left (fun _ h => h) hu

theorem IsRootCanonical.append_rep_left {p : Program} (d : Nat) :
    IsRootCanonical p → IsRootCanonical (p ++ rep .left d ε)
  | .shifts k => by rw [rep_left_add]; exact .shifts (k + d)
  | .loop b u hb hu h2 =>
    .loop b (u ++ rep .left d ε) hb (closed_append hu (closed_rep .left (fun _ h => h) trivial)) h2
  | .flip i u hu => by
    simp only [flip_append, rep_append .left left_append]
    exact .flip i (u ++ rep .left d ε) (closed_append hu (closed_rep .left (fun _ h => h) trivial))

theorem IsRootCanonical.to_rootShapes {p : Program} (h : IsRootCanonical p) :
    ∃ c ∈ rootShapes ‖p‖, p ⊑ c := by
  cases h with
  | shifts k =>
    have hsz : ‖rep .left k ε‖ = k := by rw [size_rep .left (fun _ => rfl)]; simp [size]
    rw [hsz]
    by_cases hk : k = 0
    · subst hk; exact ⟨ε, by simp [rootShapes], .nil⟩
    · exact ⟨rep .left k ε, by simp [rootShapes, hk], Program.Refines.refl _⟩
  | loop b u hb hu h2 =>
    have hsz : ‖Program.flip (.loop b u)‖ = ‖b‖ + ‖u‖ + 3 := by simp [size]
    refine ⟨.flip (.loop (gap? ‖b‖) (gap? ‖u‖)), ?_,
      .flip (.loop (refines_gap? hb rfl) (refines_gap? hu rfl))⟩
    rw [hsz]
    simp only [rootShapes, show ¬ (‖b‖ + ‖u‖ + 3 = 0) by omega, ↓reduceIte,
      List.mem_append, List.mem_map, List.mem_range]
    refine .inl (.inr ⟨‖b‖ - 2, by omega, ?_⟩)
    rw [show ‖b‖ - 2 + 2 = ‖b‖ by omega, show ‖b‖ + ‖u‖ + 3 - 5 - (‖b‖ - 2) = ‖u‖ by omega]
  | flip i u hu =>
    have hsz : ‖Program.flip (rep .left (i + 1) (.flip u))‖ = i + ‖u‖ + 3 := by
      simp only [size, size_rep .left (fun _ => rfl)]; omega
    refine ⟨.flip (rep .left (i + 1) (.flip (gap? ‖u‖))), ?_,
      .flip (refines_rep .left (fun h => .left h) (.flip (refines_gap? hu rfl)))⟩
    rw [hsz]
    simp only [rootShapes, show ¬ (i + ‖u‖ + 3 = 0) by omega, ↓reduceIte,
      List.mem_append, List.mem_map, List.mem_range]
    refine .inr ⟨i, by omega, ?_⟩
    rw [show i + ‖u‖ + 3 - 3 - i = ‖u‖ by omega]

theorem padDom_of_steps₂ {d d₁ d₂ : Nat} {p q r : Program} {t : SpecTape}
    (h1 : (Machine.mk (Tape.blank : SpecTape) p) ⇒ d₁ = some ⟨t, r⟩)
    (h2 : (Machine.mk (Tape.blank : SpecTape) q) ⇒ d₂ = some ⟨t, r⟩)
    (hd : d₁ ≤ d₂ + d) : PadDom d p q := by
  intro k hk
  obtain ⟨u, hu⟩ := hk SpecTape
  change (Machine.mk (Tape.blank : SpecTape) p) ⇒ k = some ⟨u, ε⟩ at hu
  by_cases hle : d₁ ≤ k
  · obtain ⟨k₀, rfl⟩ : ∃ k₀, k = d₁ + k₀ := ⟨k - d₁, by omega⟩
    rw [Machine.steps_add, h1, Option.bind_some] at hu
    refine ⟨d₂ + k₀, by omega, Program.haltsIn_of ⟨u, ?_⟩⟩
    show (Machine.mk (Tape.blank : SpecTape) q) ⇒ (d₂ + k₀) = some ⟨u, ε⟩
    rw [Machine.steps_add, h2, Option.bind_some]
    exact hu
  · have hnone : (Machine.mk (Tape.blank : SpecTape) p) ⇒ (k + 1) = none := by
      rw [Machine.steps_add, hu, Option.bind_some]; rfl
    have hsome := Machine.isSome_steps_of_le h1 (by omega : k + 1 ≤ d₁)
    rw [hnone] at hsome; cases hsome

theorem padDom_left (p : Program) : PadDom 1 (.left p) p :=
  padDom_of_steps₂ (d₁ := 1) (d₂ := 0) (t := Tape.blank) rfl rfl (by omega)

theorem padDom_right (p : Program) : PadDom 1 (.right p) p :=
  padDom_of_steps₂ (d₁ := 1) (d₂ := 0) (t := Tape.blank) rfl rfl (by omega)

theorem padDom_loop (b p : Program) : PadDom (‖b‖ + 2) (.loop b p) p :=
  padDom_of_steps₂ (d₁ := 1) (d₂ := 0) (t := Tape.blank) rfl rfl (by omega)

theorem padDom_flip_flip (p : Program) : PadDom 2 (.flip (.flip p)) p :=
  padDom_of_steps₂ (d₁ := 2) (d₂ := 0) (t := Tape.blank)
    (by simp [Machine.steps, Machine.step, specTape_flip_flip]) rfl (by omega)

theorem padDom_flip_loop_nil (p : Program) (hp : p°) :
    PadDom 2 (.flip (.loop ε p)) (.flip p) := by
  have hcg : Congr (.loop ε ε) (.flip (.flip ε)) (.flip (.loop ε p)) (.flip (.flip (.flip p))) :=
    .flip (Congr.swap (s₁ := .loop ε ε) (s₂ := .flip (.flip ε)) (Congr.refl hp))
  have hdom := Congr.dominates stepDom_emptyLoop hcg
  intro k hk
  obtain ⟨k', hle, hk'⟩ := hdom k hk
  obtain ⟨k₀, hle₀, hk₀⟩ := padDom_flip_flip (.flip p) k' hk'
  exact ⟨k₀, by omega, hk₀⟩

theorem padDom_flip_loop_flip (p : Program) :
    PadDom 4 (.flip (.loop (.flip ε) p)) p := by
  have hc1 : Tape.cells (Tape.flip (Tape.blank : SpecTape)) 0 = true := rfl
  have hc0 : Tape.cells (Tape.blank : SpecTape) 0 = false := rfl
  refine padDom_of_steps₂ (d₁ := 4) (d₂ := 0) (t := Tape.blank) ?_ rfl (by omega)
  simp only [Machine.steps, Machine.step, Option.bind_some, hc1, ↓reduceIte, flip_append,
    nil_append, specTape_flip_flip, hc0, Bool.false_eq_true]

theorem padDom_flip_loop_left (p : Program) :
    PadDom 2 (.flip (.loop (.left ε) p)) (.flip (.left p)) := by
  have hc1 : Tape.cells (Tape.flip (Tape.blank : SpecTape)) 0 = true := rfl
  have hc0 : Tape.cells (Tape.moveL (Tape.flip (Tape.blank : SpecTape))) 0 = false := rfl
  refine padDom_of_steps₂ (d₁ := 4) (d₂ := 2) (t := Tape.moveL (Tape.flip Tape.blank)) ?_ rfl (by omega)
  simp only [Machine.steps, Machine.step, Option.bind_some, hc1, ↓reduceIte, left_append,
    nil_append, hc0, Bool.false_eq_true]

theorem padDom_flip_left_right (i : Nat) (p : Program) :
    PadDom 2 (.flip (rep .left (i + 1) (.right p))) (.flip (rep .left i p)) := by
  have hrep : rep .left (i + 1) (.right p) = rep .left i (.left (.right p)) := by
    rw [← rep_left_snoc]
  refine padDom_of_steps₂ (d₁ := 1 + (i + 2)) (d₂ := 1 + i) (r := p)
    (t := shiftTape (Tape.flip Tape.blank) ((i : Nat) * (-1 : Int))) ?_ ?_ (by omega)
  · rw [hrep, Machine.steps_add]
    have hfl : (Machine.mk (Tape.blank : SpecTape) (.flip (rep .left i (.left (.right p))))) ⇒ 1 =
        some ⟨Tape.flip Tape.blank, rep .left i (.left (.right p))⟩ := rfl
    rw [hfl, Option.bind_some, Machine.steps_add,
      steps_rep_shift .left (-1) (fun _ _ => rfl), Option.bind_some]
    simp only [Machine.steps, Machine.step, Option.bind_some, Option.some.injEq, Machine.mk.injEq, and_true]
    funext x
    show (Tape.flip (Tape.blank : SpecTape)) (x + 1 - 1 + ↑i * -1) =
      (Tape.flip (Tape.blank : SpecTape)) (x + ↑i * -1)
    rw [Int.add_sub_cancel]
  · rw [Machine.steps_add]
    have hfl : (Machine.mk (Tape.blank : SpecTape) (.flip (rep .left i p))) ⇒ 1 =
        some ⟨Tape.flip Tape.blank, rep .left i p⟩ := rfl
    rw [hfl, Option.bind_some, steps_rep_shift .left (-1) (fun _ _ => rfl)]

theorem padDom_flip_left_loop (i : Nat) (b p : Program) :
    PadDom (‖b‖ + 2) (.flip (rep .left (i + 1) (.loop b p))) (.flip (rep .left (i + 1) p)) := by
  have hcell : Tape.cells (shiftTape (Tape.flip (Tape.blank : SpecTape)) ((i + 1 : Nat) * (-1 : Int))) 0 = false := by
    change (if (0 : Int) + ↑(i + 1) * -1 = 0 then !(Tape.blank : SpecTape) 0 else (Tape.blank : SpecTape) (0 + ↑(i + 1) * -1)) = false
    rw [ite_eq_right_iff.mpr (fun h => absurd h (by omega))]; rfl
  refine padDom_of_steps₂ (d₁ := 1 + (i + 1) + 1) (d₂ := 1 + (i + 1)) (r := p)
    (t := shiftTape (Tape.flip Tape.blank) ((i + 1 : Nat) * (-1 : Int))) ?_ ?_ (by omega)
  · rw [Machine.steps_add, Machine.steps_add]
    have hfl : (Machine.mk (Tape.blank : SpecTape) (.flip (rep .left (i + 1) (.loop b p)))) ⇒ 1 =
        some ⟨Tape.flip Tape.blank, rep .left (i + 1) (.loop b p)⟩ := rfl
    rw [hfl, Option.bind_some, steps_rep_shift .left (-1) (fun _ _ => rfl), Option.bind_some]
    show (Machine.mk (shiftTape (Tape.flip Tape.blank) ((i + 1 : Nat) * (-1 : Int))) (.loop b p)) ⇒ 1 = _
    simp only [Machine.steps, Machine.step, Option.bind_some, hcell, Bool.false_eq_true, ↓reduceIte]
  · rw [Machine.steps_add]
    have hfl : (Machine.mk (Tape.blank : SpecTape) (.flip (rep .left (i + 1) p))) ⇒ 1 =
        some ⟨Tape.flip Tape.blank, rep .left (i + 1) p⟩ := rfl
    rw [hfl, Option.bind_some, steps_rep_shift .left (-1) (fun _ _ => rfl)]

theorem blank_dominates_flip_rep_left (i : Nat) :
    (.flip (rep .left i ε)) ≼ rep .left (i + 1) ε := by
  intro k hk
  have h1 : (Machine.mk (Tape.blank : SpecTape) (.flip (rep .left i ε))) ⇒ (1 + i) =
      some ⟨shiftTape (Tape.flip Tape.blank) ((i : Nat) * (-1 : Int)), ε⟩ := by
    rw [Machine.steps_add]
    have hfl : (Machine.mk (Tape.blank : SpecTape) (.flip (rep .left i ε))) ⇒ 1 =
        some ⟨Tape.flip Tape.blank, rep .left i ε⟩ := rfl
    rw [hfl, Option.bind_some, steps_rep_shift .left (-1) (fun _ _ => rfl)]
  have hkeq : k = 1 + i := Machine.HaltsIn.unique (hk SpecTape) ⟨_, h1⟩
  refine ⟨i + 1, by omega, Program.haltsIn_of ⟨shiftTape Tape.blank ((i + 1 : Nat) * (-1 : Int)), ?_⟩⟩
  exact steps_rep_shift .left (-1) (fun _ _ => rfl) (i + 1) Tape.blank ε

def leftCount : Program → Nat
  | .left p => leftCount p + 1
  | _       => 0

def leftTail : Program → Program
  | .left p => leftTail p
  | p       => p

theorem rep_leftCount_leftTail : ∀ (p : Program), rep .left (leftCount p) (leftTail p) = p
  | .left p => by simp [leftCount, leftTail, rep, rep_leftCount_leftTail p]
  | .right _ | .flip _ | .loop _ _ | .gap _ _ _ | ε => rfl

theorem size_leftCount_leftTail : ∀ (p : Program), ‖p‖ = leftCount p + ‖leftTail p‖
  | .left p => by simp [leftCount, leftTail, size, size_leftCount_leftTail p]; omega
  | .right _ | .flip _ | .loop _ _ | .gap _ _ _ | ε => by simp [leftCount, leftTail]

theorem closed_leftTail : ∀ (p : Program), p° → (leftTail p)°
  | .left p, hp => closed_leftTail p hp
  | .right _, hp | .flip _, hp | .loop _ _, hp | .gap _ _ _, hp | ε, hp => hp

theorem closed_size_one_cases {b : Program} (hb : b°) (hsz : ‖b‖ = 1) :
    b = .left ε ∨ b = .right ε ∨ b = .flip ε := by
  cases b with
  | nil => simp [size] at hsz
  | gap => exact absurd hb id
  | loop => simp [size] at hsz
  | left r =>
    have hr0 : ‖r‖ = 0 := by simp [size] at hsz; omega
    exact .inl (congrArg Program.left (size_eq_zero_of_closed hb hr0))
  | right r =>
    have hr0 : ‖r‖ = 0 := by simp [size] at hsz; omega
    exact .inr (.inl (congrArg Program.right (size_eq_zero_of_closed hb hr0)))
  | flip r =>
    have hr0 : ‖r‖ = 0 := by simp [size] at hsz; omega
    exact .inr (.inr (congrArg Program.flip (size_eq_zero_of_closed hb hr0)))

theorem not_left_leftTail : ∀ (p r : Program), leftTail p ≠ .left r
  | .left p, r => not_left_leftTail p r
  | .right _, _ | .flip _, _ | .loop _ _, _ | .gap _ _ _, _ | ε, _ => by simp [leftTail]

theorem flip_left_cover_aux (n : Nat)
    (ih : ∀ m < n, ∀ q : Program, q° → ‖q‖ = m → ∃ p', IsRootCanonical p' ∧ ‖p'‖ = m ∧ q ≼ p')
    (i : Nat) (t : Program) (ht : t°) (ht_not_left : ∀ r, t ≠ .left r)
    (hi_right : i = 0 → ∀ r, t ≠ .right r)
    (hsz : 1 + i + ‖t‖ = n) :
    ∃ p', IsRootCanonical p' ∧ ‖p'‖ = n ∧ (.flip (rep .left i t)) ≼ p' := by
  have hpad : ∀ (d : Nat) (q : Program), q° → 0 < d → ‖q‖ + d = n →
      PadDom d (.flip (rep .left i t)) q →
      ∃ p', IsRootCanonical p' ∧ ‖p'‖ = n ∧ (.flip (rep .left i t)) ≼ p' := by
    intro d q hq hd hqsz hpd
    obtain ⟨q', hrc, hq'sz, hdom⟩ := ih ‖q‖ (by omega) q hq rfl
    refine ⟨q' ++ rep .left d ε, hrc.append_rep_left d, ?_, hpd.to_dominates hdom⟩
    rw [size_append, size_rep .left (fun _ => rfl), hq'sz]; simp [size]; omega
  cases t with
  | gap => exact absurd ht id
  | left r => exact absurd rfl (ht_not_left r)
  | nil =>
    simp only [size, Nat.add_zero] at hsz
    refine ⟨rep .left (i + 1) ε, .shifts (i + 1), ?_, blank_dominates_flip_rep_left i⟩
    rw [size_rep .left (fun _ => rfl)]; simp [size]; omega
  | right r =>
    cases i with
    | zero => exact absurd rfl (hi_right rfl r)
    | succ i' =>
      exact hpad 2 (.flip (rep .left i' r)) (closed_rep .left (fun _ h => h) ht) (by omega)
        (by simp [size, size_rep .left (fun _ => rfl)] at hsz ⊢; omega)
        (padDom_flip_left_right i' r)
  | flip r =>
    cases i with
    | zero =>
      exact hpad 2 r ht (by omega) (by simp [size] at hsz; omega) (padDom_flip_flip r)
    | succ i' =>
      refine ⟨.flip (rep .left (i' + 1) (.flip r)), .flip i' r ht, ?_, Dominates.refl _⟩
      simp [size, size_rep .left (fun _ => rfl)] at hsz ⊢; omega
  | loop b r =>
    cases i with
    | succ i' =>
      exact hpad (‖b‖ + 2) (.flip (rep .left (i' + 1) r)) (closed_rep .left (fun _ h => h) ht.2) (by omega)
        (by simp [size, size_rep .left (fun _ => rfl)] at hsz ⊢; omega)
        (padDom_flip_left_loop i' b r)
    | zero =>
      simp only [rep]
      by_cases hb0 : ‖b‖ = 0
      · have hbe := size_eq_zero_of_closed ht.1 hb0
        subst hbe
        exact hpad 2 (.flip r) ht.2 (by omega) (by simp [size] at hsz ⊢; omega)
          (padDom_flip_loop_nil r ht.2)
      · by_cases hb1 : ‖b‖ = 1
        · rcases closed_size_one_cases ht.1 hb1 with rfl | rfl | rfl
          · exact hpad 2 (.flip (.left r)) ht.2 (by omega) (by simp [size] at hsz ⊢; omega)
              (padDom_flip_loop_left r)
          · have hmir : (.flip (.loop (.right ε) r)) ≼ (.flip (.loop (.left ε) r.mirror)) :=
              (Equiv.mirror (.flip (.loop (.right ε) r))).dominates
            obtain ⟨q', hrc, hq'sz, hdom⟩ :=
              ih (‖r‖ + 2) (by simp [size] at hsz; omega) (.flip (.left r.mirror))
                (closed_mirror ht.2) (by simp [size, size_mirror])
            refine ⟨q' ++ rep .left 2 ε, hrc.append_rep_left 2, ?_,
              Dominates.trans hmir ((padDom_flip_loop_left r.mirror).to_dominates hdom)⟩
            rw [size_append, size_rep .left (fun _ => rfl), hq'sz]
            simp [size] at hsz ⊢; omega
          · exact hpad 4 r ht.2 (by omega) (by simp [size] at hsz ⊢; omega)
              (padDom_flip_loop_flip r)
        · refine ⟨.flip (.loop b r), .loop b r ht.1 ht.2 (by omega), ?_, Dominates.refl _⟩
          simp [size] at hsz ⊢; omega

theorem rootShapes_cover_canonical (n : Nat) :
    ∀ (p : Program), p° → ‖p‖ = n →
      ∃ p', IsRootCanonical p' ∧ ‖p'‖ = n ∧ p ≼ p' := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro p hp hsz
    have hpad : ∀ (d : Nat) (q : Program), q° → 0 < d → ‖q‖ + d = n →
        PadDom d p q →
        ∃ p', IsRootCanonical p' ∧ ‖p'‖ = n ∧ p ≼ p' := by
      intro d q hq hd hqsz hpd
      obtain ⟨q', hrc, hq'sz, hdom⟩ := ih ‖q‖ (by omega) q hq rfl
      refine ⟨q' ++ rep .left d ε, hrc.append_rep_left d, ?_, hpd.to_dominates hdom⟩
      rw [size_append, size_rep .left (fun _ => rfl), hq'sz]; simp [size]; omega
    cases p with
    | gap => exact absurd hp id
    | nil =>
      simp only [size] at hsz; subst hsz
      exact ⟨rep .left 0 ε, .shifts 0, rfl, Dominates.refl ε⟩
    | left q =>
      exact hpad 1 q hp (by omega) (by simp [size] at hsz; omega) (padDom_left q)
    | right q =>
      exact hpad 1 q hp (by omega) (by simp [size] at hsz; omega) (padDom_right q)
    | loop b q =>
      exact hpad (‖b‖ + 2) q hp.2 (by omega) (by simp [size] at hsz; omega) (padDom_loop b q)
    | flip q =>
      by_cases hqr : ∃ r, q = .right r
      · obtain ⟨r, rfl⟩ := hqr
        have hmir : (.flip (.right r)) ≼ (.flip (.left r.mirror)) :=
          (Equiv.mirror (.flip (.right r))).dominates
        have hrep := rep_leftCount_leftTail (.left r.mirror)
        have hsz_lt := size_leftCount_leftTail (.left r.mirror)
        obtain ⟨p', hrc, hp'sz, hdom⟩ :=
          flip_left_cover_aux n ih (leftCount (.left r.mirror)) (leftTail (.left r.mirror))
            (closed_leftTail (.left r.mirror) (closed_mirror hp)) (not_left_leftTail (.left r.mirror))
            (fun h0 => by simp [leftCount] at h0)
            (by simp [size, size_mirror] at hsz hsz_lt; omega)
        rw [hrep] at hdom
        exact ⟨p', hrc, hp'sz, Dominates.trans hmir hdom⟩
      · have hrep := rep_leftCount_leftTail q
        have hsz_lt := size_leftCount_leftTail q
        obtain ⟨p', hrc, hp'sz, hdom⟩ :=
          flip_left_cover_aux n ih (leftCount q) (leftTail q)
            (closed_leftTail q hp) (not_left_leftTail q)
            (fun h0 r hr => hqr ⟨r, by
              have hlt : leftTail q = q := by
                cases q with
                | left _ => simp [leftCount] at h0
                | _ => rfl
              rwa [hlt] at hr⟩)
            (by simp [size] at hsz; omega)
        rw [hrep] at hdom
        exact ⟨p', hrc, hp'sz, hdom⟩

theorem rootShapes_cover {s : Program} (hs : s°) :
    ∃ c ∈ rootShapes ‖s‖, ∃ p', p'° ∧ p' ⊑ c ∧ s ≼ p' := by
  obtain ⟨p', hrc, hp'sz, hdom⟩ := rootShapes_cover_canonical ‖s‖ s hs rfl
  obtain ⟨c, hc, hp'c⟩ := hrc.to_rootShapes
  rw [hp'sz] at hc
  exact ⟨c, hc, p', hrc.closed, hp'c, hdom⟩

def isTopTailGap : Program → Bool
  | .gap _ _ ε => true
  | .left p | .right p | .flip p => isTopTailGap p
  | .loop b p => (b.numGaps == 0) && isTopTailGap p
  | _ => false

def isTopAfterLoop : Program → Bool
  | .loop b (.gap _ _ ε) => b.numGaps == 0
  | .left p | .right p | .flip p => isTopAfterLoop p
  | .loop b p => (b.numGaps == 0) && isTopAfterLoop p
  | _ => false

def topNonShiftShapes (afterLoop : Bool) (r : Nat) : List Program :=
  if r = 0 then []
  else
    (if 4 ≤ r then [.flip (gap? (r - 1))] else []) ++
      (if afterLoop then []
       else (List.range (r - 2)).map fun (a : Nat) => .loop (gap? (a + 1)) (gap? (r - 3 - a)))

def topShapes (noShift afterLoop : Bool) (k : Nat) : List Program :=
  if k = 0 then [ε]
  else
    let ls := (List.range k).flatMap fun (i : Nat) =>
      (topNonShiftShapes false (k - 1 - i)).map (rep .left (i + 1))
    let rs := if noShift then [] else (List.range k).flatMap fun (i : Nat) =>
      (topNonShiftShapes false (k - 1 - i)).map (rep .right (i + 1))
    [rep .left k ε] ++ ls ++ rs ++ topNonShiftShapes afterLoop k

theorem sub_nonShiftShapes_of_topNonShiftShapes {afterLoop : Bool} {r : Nat} {c : Program} :
    c ∈ topNonShiftShapes afterLoop r → c ∈ nonShiftShapes r := by
  intro hc
  unfold topNonShiftShapes at hc
  split at hc
  · cases hc
  · next hr0 =>
    simp only [nonShiftShapes, hr0, ↓reduceIte, List.mem_append] at hc ⊢
    rcases hc with hfl | hlp
    · split at hfl
      · exact .inl hfl
      · cases hfl
    · split at hlp
      · cases hlp
      · exact .inr hlp

theorem closed_of_numGaps_eq_zero : ∀ (p : Program), p.numGaps = 0 → p°
  | ε, _ => trivial
  | .left p, h | .right p, h | .flip p, h => closed_of_numGaps_eq_zero p h
  | .loop b p, h =>
    ⟨closed_of_numGaps_eq_zero b (by simp [numGaps] at h; omega),
     closed_of_numGaps_eq_zero p (by simp [numGaps] at h; omega)⟩
  | .gap _ _ _, h => by simp [numGaps] at h

theorem numGaps_eq_zero_of_closed : ∀ (p : Program), p° → p.numGaps = 0
  | ε, _ => rfl
  | .left p, h | .right p, h | .flip p, h => numGaps_eq_zero_of_closed p h
  | .loop b p, h => by
    simp [numGaps, numGaps_eq_zero_of_closed b h.1, numGaps_eq_zero_of_closed p h.2]
  | .gap _ _ _, h => absurd h id

theorem eq_append_gap_of_isTopTailGap : ∀ (q : Program), q.isTopTailGap = true →
    ∃ (pre : Program) (k : Nat) (hk : 0 < k),
      pre° ∧ q = pre ++ .gap k hk ε ∧
      (q.isTopAfterLoop = true → ∃ pre₀ b : Program, pre₀° ∧ b° ∧ pre = pre₀ ++ .loop b ε)
  | .gap k hk ε, _ => ⟨ε, k, hk, trivial, rfl, fun h => by simp [isTopAfterLoop] at h⟩
  | .gap _ _ (.left _), h | .gap _ _ (.right _), h | .gap _ _ (.flip _), h
  | .gap _ _ (.loop _ _), h | .gap _ _ (.gap _ _ _), h | ε, h => by simp [isTopTailGap] at h
  | .left p, h => by
    obtain ⟨pre, k, hk, hpre, rfl, hafter⟩ := eq_append_gap_of_isTopTailGap p h
    refine ⟨.left pre, k, hk, hpre, rfl, fun hal => ?_⟩
    obtain ⟨pre₀, b, hpre₀, hb, rfl⟩ := hafter hal
    exact ⟨.left pre₀, b, hpre₀, hb, rfl⟩
  | .right p, h => by
    obtain ⟨pre, k, hk, hpre, rfl, hafter⟩ := eq_append_gap_of_isTopTailGap p h
    refine ⟨.right pre, k, hk, hpre, rfl, fun hal => ?_⟩
    obtain ⟨pre₀, b, hpre₀, hb, rfl⟩ := hafter hal
    exact ⟨.right pre₀, b, hpre₀, hb, rfl⟩
  | .flip p, h => by
    obtain ⟨pre, k, hk, hpre, rfl, hafter⟩ := eq_append_gap_of_isTopTailGap p h
    refine ⟨.flip pre, k, hk, hpre, rfl, fun hal => ?_⟩
    obtain ⟨pre₀, b, hpre₀, hb, rfl⟩ := hafter hal
    exact ⟨.flip pre₀, b, hpre₀, hb, rfl⟩
  | .loop b p, h => by
    simp only [isTopTailGap, Bool.and_eq_true, beq_iff_eq] at h
    have hb := closed_of_numGaps_eq_zero b h.1
    obtain ⟨pre, k, hk, hpre, hp_eq, hafter⟩ := eq_append_gap_of_isTopTailGap p h.2
    refine ⟨.loop b pre, k, hk, ⟨hb, hpre⟩, by rw [hp_eq, loop_append], fun hal => ?_⟩
    cases p with
    | gap k' hk' r =>
      cases r with
      | nil =>
        have hpre_nil : pre = ε := by
          cases pre with
          | nil => rfl
          | left _ | right _ | flip _ | loop _ _ => cases hp_eq
          | gap _ _ _ => exact absurd hpre id
        subst hpre_nil
        exact ⟨ε, b, trivial, hb, rfl⟩
      | _ => simp [isTopTailGap] at h
    | left _ | right _ | flip _ | loop _ _ =>
      simp only [isTopAfterLoop, Bool.and_eq_true, beq_iff_eq] at hal
      obtain ⟨pre₀, b', hpre₀, hb', rfl⟩ := hafter hal.2
      exact ⟨.loop b pre₀, b', ⟨hb, hpre₀⟩, hb', rfl⟩
    | nil => simp [isTopTailGap] at h

theorem subst_zero_append_closed (pre : Program) (hpre : pre°) (r c : Program) :
    (pre ++ r)[0 ↦ c] = pre ++ r[0 ↦ c] := by
  induction pre with
  | nil => rfl
  | left _ ih => exact congrArg Program.left (ih hpre)
  | right _ ih => exact congrArg Program.right (ih hpre)
  | flip _ ih => exact congrArg Program.flip (ih hpre)
  | loop b _ _ ihp =>
    have hb0 : b.numGaps = 0 := numGaps_eq_zero_of_closed b hpre.1
    simp [subst, hb0, ihp hpre.2]
  | gap => exact absurd hpre id

theorem gapSize?_zero_append_closed (pre : Program) (hpre : pre°) (k : Nat) (hk : 0 < k) :
    gapSize? 0 (pre ++ .gap k hk ε) = some k := by
  induction pre with
  | nil => rfl
  | left _ ih | right _ ih | flip _ ih => exact ih hpre
  | loop b _ _ ihp =>
    have hb0 : b.numGaps = 0 := numGaps_eq_zero_of_closed b hpre.1
    simp [gapSize?, hb0, ihp hpre.2]
  | gap => exact absurd hpre id

theorem numGaps_append_closed (pre : Program) (hpre : pre°) (r : Program) :
    (pre ++ r).numGaps = r.numGaps := by
  induction pre with
  | nil => rfl
  | left _ ih | right _ ih | flip _ ih => exact ih hpre
  | loop b _ _ ihp =>
    simp [numGaps, numGaps_eq_zero_of_closed b hpre.1, ihp hpre.2]
  | gap => exact absurd hpre id

theorem noShift_of_append (pre r : Program) (h : (pre ++ r).noShift = true) :
    pre.noShift = true := by
  induction pre with
  | nil => rfl
  | left _ _ | right _ _ => simp [noShift] at h
  | flip _ ih | gap _ _ _ ih => exact ih h
  | loop _ _ _ ihp =>
    simp only [loop_append, noShift, Bool.and_eq_true] at h ⊢
    exact ⟨h.1, ihp h.2⟩

theorem refines_eq_of_closed (q p : Program) (hq : q°) (h : p ⊑ q) : p = q := by
  induction h with
  | nil => rfl
  | left _ ih => exact congrArg Program.left (ih hq)
  | right _ ih => exact congrArg Program.right (ih hq)
  | flip _ ih => exact congrArg Program.flip (ih hq)
  | loop _ _ ihb ihp => rw [ihb hq.1, ihp hq.2]
  | gap => exact absurd hq id

theorem refines_append_closed_cancel (pre : Program) (hpre : pre°) {p r : Program}
    (h : p ⊑ (pre ++ r)) : ∃ s, p = pre ++ s ∧ s ⊑ r := by
  induction pre generalizing p with
  | nil => exact ⟨p, rfl, h⟩
  | left pre₁ ih =>
    cases h with
    | left h₁ =>
      obtain ⟨s, rfl, hs⟩ := ih hpre h₁
      exact ⟨s, rfl, hs⟩
  | right pre₁ ih =>
    cases h with
    | right h₁ =>
      obtain ⟨s, rfl, hs⟩ := ih hpre h₁
      exact ⟨s, rfl, hs⟩
  | flip pre₁ ih =>
    cases h with
    | flip h₁ =>
      obtain ⟨s, rfl, hs⟩ := ih hpre h₁
      exact ⟨s, rfl, hs⟩
  | loop b pre₁ _ ihp =>
    cases h with
    | loop hb h₁ =>
      have hbe := refines_eq_of_closed b _ hpre.1 hb
      subst hbe
      obtain ⟨s, rfl, hs⟩ := ihp hpre.2 h₁
      exact ⟨s, rfl, hs⟩
  | gap => exact absurd hpre id

theorem refines_append_closed_left (pre : Program) (hpre : pre°) {s c : Program}
    (h : s ⊑ c) : (pre ++ s) ⊑ (pre ++ c) := by
  induction pre with
  | nil => exact h
  | left _ ih => exact .left (ih hpre)
  | right _ ih => exact .right (ih hpre)
  | flip _ ih => exact .flip (ih hpre)
  | loop _ _ _ ihp => exact .loop (Program.Refines.refl _) (ihp hpre.2)
  | gap => exact absurd hpre id

theorem haltsIn_le_size_of_le_one {s : Program} (hs : s°) (hsz : ‖s‖ ≤ 1)
    {t : SpecTape} {k : Nat} (hk : (Machine.mk t s) ⇓ k) : k ≤ ‖s‖ := by
  cases s with
  | nil =>
    have : k = 0 := Machine.HaltsIn.unique hk ⟨t, rfl⟩
    omega
  | gap => exact absurd hs id
  | loop => simp [size] at hsz
  | left r =>
    have hr0 : ‖r‖ = 0 := by simp [size] at hsz; omega
    have hre := size_eq_zero_of_closed (p := r) hs hr0
    subst hre
    have : k = 1 := Machine.HaltsIn.unique hk ⟨_, rfl⟩
    simp [size, this]
  | right r =>
    have hr0 : ‖r‖ = 0 := by simp [size] at hsz; omega
    have hre := size_eq_zero_of_closed (p := r) hs hr0
    subst hre
    have : k = 1 := Machine.HaltsIn.unique hk ⟨_, rfl⟩
    simp [size, this]
  | flip r =>
    have hr0 : ‖r‖ = 0 := by simp [size] at hsz; omega
    have hre := size_eq_zero_of_closed (p := r) hs hr0
    subst hre
    have : k = 1 := Machine.HaltsIn.unique hk ⟨_, rfl⟩
    simp [size, this]

theorem haltsIn_le_size_of_le_two {s : Program} (hs : s°) (hsz : ‖s‖ ≤ 2)
    {t : SpecTape} {k : Nat} (hk : (Machine.mk t s) ⇓ k) : k ≤ ‖s‖ := by
  cases s with
  | nil =>
    have : k = 0 := Machine.HaltsIn.unique hk ⟨t, rfl⟩
    omega
  | gap => exact absurd hs id
  | left r =>
    cases k with
    | zero => rw [Machine.haltsIn_zero] at hk; cases hk
    | succ k =>
      have hst : (Machine.mk t (.left r))⇒ = some ⟨Tape.moveL t, r⟩ := rfl
      have := haltsIn_le_size_of_le_one (s := r) hs (by simp [size] at hsz; omega)
        ((Machine.haltsIn_succ hst).mp hk)
      simp [size]; omega
  | right r =>
    cases k with
    | zero => rw [Machine.haltsIn_zero] at hk; cases hk
    | succ k =>
      have hst : (Machine.mk t (.right r))⇒ = some ⟨Tape.moveR t, r⟩ := rfl
      have := haltsIn_le_size_of_le_one (s := r) hs (by simp [size] at hsz; omega)
        ((Machine.haltsIn_succ hst).mp hk)
      simp [size]; omega
  | flip r =>
    cases k with
    | zero => rw [Machine.haltsIn_zero] at hk; cases hk
    | succ k =>
      have hst : (Machine.mk t (.flip r))⇒ = some ⟨Tape.flip t, r⟩ := rfl
      have := haltsIn_le_size_of_le_one (s := r) hs (by simp [size] at hsz; omega)
        ((Machine.haltsIn_succ hst).mp hk)
      simp [size]; omega
  | loop b r =>
    have hb0 : ‖b‖ = 0 := by simp [size] at hsz; omega
    have hr0 : ‖r‖ = 0 := by simp [size] at hsz; omega
    have hbe := size_eq_zero_of_closed hs.1 hb0
    have hre := size_eq_zero_of_closed hs.2 hr0
    subst hbe; subst hre
    rcases stepDom_emptyLoop t with hdiv | ⟨d₁, d₂, t', hd₁, hle_d, hst⟩
    · exact absurd ⟨k, hk⟩ (Machine.not_halts_of_diverges (by simpa using hdiv ε))
    · have h1 := (hst ε).1
      have : k = d₁ := Machine.HaltsIn.unique hk ⟨t', h1⟩
      have hd2 : d₂ = 2 := by
        have h2 := (hst ε).2
        exact Machine.HaltsIn.unique ⟨t', h2⟩ ⟨Tape.flip (Tape.flip t), rfl⟩
      simp [size]; omega

theorem haltsIn_le_size_of_flip_le_two {u : Program} (hu : u°) (hsz : ‖u‖ ≤ 2)
    {t : SpecTape} {k : Nat} (hk : (Machine.mk t (.flip u)) ⇓ k) : k ≤ ‖Program.flip u‖ := by
  cases k with
  | zero => rw [Machine.haltsIn_zero] at hk; cases hk
  | succ k =>
    have hst : (Machine.mk t (.flip u))⇒ = some ⟨Tape.flip t, u⟩ := rfl
    have := haltsIn_le_size_of_le_two hu hsz ((Machine.haltsIn_succ hst).mp hk)
    simp [size]; omega

theorem haltsIn_le_size_of_loop_nil_le_one {u : Program} (hu : u°) (hsz : ‖u‖ ≤ 1)
    {t : SpecTape} {k : Nat} (hk : (Machine.mk t (.loop ε u)) ⇓ k) : k ≤ ‖Program.loop ε u‖ := by
  have hcg : Congr (.loop ε ε) (.flip (.flip ε)) (.loop ε u) (.flip (.flip u)) :=
    Congr.swap (s₁ := .loop ε ε) (s₂ := .flip (.flip ε)) (Congr.refl hu)
  obtain ⟨k', hle, hk'⟩ := Congr.dominates_machine stepDom_emptyLoop hcg hk
  have := haltsIn_le_size_of_flip_le_two (u := .flip u) hu (by simp [size]; omega) hk'
  simp [size] at this ⊢; omega

theorem haltsIn_shiftPrefix_le {s : Program} {t : SpecTape} {k : Nat}
    (htail : ∀ (t₁ : SpecTape) (d : Nat), (Machine.mk t₁ (shiftTail s)) ⇓ d → d ≤ ‖shiftTail s‖)
    (hk : (Machine.mk t s) ⇓ k) : k ≤ ‖s‖ := by
  have hsz : ‖s‖ = countL s + countR s + ‖shiftTail s‖ := by
    have := congrArg size (shiftPrefix_append_tail s)
    rw [size_append, size_shiftPrefix] at this; exact this.symm
  by_cases hle : countL s + countR s ≤ k
  · obtain ⟨d, rfl⟩ : ∃ d, k = (countL s + countR s) + d := ⟨k - (countL s + countR s), by omega⟩
    obtain ⟨u, hu⟩ := hk
    rw [Machine.steps_add] at hu
    conv at hu => lhs; arg 1; rw [show (Machine.mk t s) = Machine.mk t (shiftPrefix s ++ shiftTail s) by
      rw [shiftPrefix_append_tail]]
    rw [steps_shiftPrefix s t (shiftTail s), Option.bind_some] at hu
    have hd := htail _ d ⟨u, hu⟩
    omega
  · omega

theorem closed_steps_dichotomy :
    ∀ (n : Nat) (t : SpecTape) (a : Program), a° →
      (∃ t' a', a'° ∧ ∀ r : Program, (Machine.mk t (a ++ r)) ⇒ n = some ⟨t', a' ++ r⟩) ∨
      (∃ d t', d ≤ n ∧ ∀ r : Program, (Machine.mk t (a ++ r)) ⇒ d = some ⟨t', r⟩)
  | 0, t, a, ha => .inl ⟨t, a, ha, fun _ => rfl⟩
  | n + 1, t, ε, _ => .inr ⟨0, t, by omega, fun _ => rfl⟩
  | n + 1, _, .gap _ _ _, ha => absurd ha id
  | n + 1, t, .left a, ha => by
    rcases closed_steps_dichotomy n (Tape.moveL t) a ha with
      ⟨t', a', ha', hr⟩ | ⟨d, t', hdn, hr⟩
    · exact .inl ⟨t', a', ha', fun r => hr r⟩
    · exact .inr ⟨d + 1, t', by omega, fun r => hr r⟩
  | n + 1, t, .right a, ha => by
    rcases closed_steps_dichotomy n (Tape.moveR t) a ha with
      ⟨t', a', ha', hr⟩ | ⟨d, t', hdn, hr⟩
    · exact .inl ⟨t', a', ha', fun r => hr r⟩
    · exact .inr ⟨d + 1, t', by omega, fun r => hr r⟩
  | n + 1, t, .flip a, ha => by
    rcases closed_steps_dichotomy n (Tape.flip t) a ha with
      ⟨t', a', ha', hr⟩ | ⟨d, t', hdn, hr⟩
    · exact .inl ⟨t', a', ha', fun r => hr r⟩
    · exact .inr ⟨d + 1, t', by omega, fun r => hr r⟩
  | n + 1, t, .loop b a, ha => by
    have hnext : (if Tape.cells t 0 then b ++ .loop b a else a)° := by
      split; exact closed_append ha.1 ha; exact ha.2
    rcases closed_steps_dichotomy n t (if Tape.cells t 0 then b ++ .loop b a else a) hnext with
      ⟨t', a', ha', hr⟩ | ⟨d, t', hdn, hr⟩
    · refine .inl ⟨t', a', ha', fun r => ?_⟩
      simp only [loop_append, Machine.steps, Machine.step, Option.bind_some]
      have hite : (if Tape.cells t 0 then b ++ .loop b (a ++ r) else a ++ r) =
          (if Tape.cells t 0 then b ++ .loop b a else a) ++ r := by
        split <;> simp [append_assoc]
      rw [hite]; exact hr r
    · refine .inr ⟨d + 1, t', by omega, fun r => ?_⟩
      simp only [loop_append, Machine.steps, Machine.step, Option.bind_some]
      have hite : (if Tape.cells t 0 then b ++ .loop b (a ++ r) else a ++ r) =
          (if Tape.cells t 0 then b ++ .loop b a else a) ++ r := by
        split <;> simp [append_assoc]
      rw [hite]; exact hr r

theorem steps_append_split {a s : Program} {t u : SpecTape} {k : Nat}
    (ha : a°) (hk : (Machine.mk t (a ++ s)) ⇒ k = some ⟨u, ε⟩) :
    ∃ (d k₂ : Nat) (t₀ : SpecTape),
      k = d + k₂ ∧
      (∀ r : Program, (Machine.mk t (a ++ r)) ⇒ d = some ⟨t₀, r⟩) ∧
      (Machine.mk t₀ s) ⇓ k₂ := by
  rcases closed_steps_dichotomy (k + 1) t a ha with
    ⟨t', a', _, hr⟩ | ⟨d, t₀, hdk, hr⟩
  · have hnone : (Machine.mk t (a ++ s)) ⇒ (k + 1) = none := by
      rw [Machine.steps_add, hk, Option.bind_some]; rfl
    rw [hr s] at hnone; cases hnone
  · by_cases hle : d ≤ k
    · obtain ⟨k₂, rfl⟩ : ∃ k₂, k = d + k₂ := ⟨k - d, by omega⟩
      rw [Machine.steps_add, hr s, Option.bind_some] at hk
      exact ⟨d, k₂, t₀, rfl, hr, u, hk⟩
    · have hd : d = k + 1 := by omega
      subst hd
      have hnone : (Machine.mk t (a ++ s)) ⇒ (k + 1) = none := by
        rw [Machine.steps_add, hk, Option.bind_some]; rfl
      rw [hr s] at hnone; cases hnone

theorem loop_exit_cell_false :
    ∀ (d : Nat) (t t₀ : SpecTape) (p b : Program), p° → b° →
      (Machine.mk t (p ++ .loop b ε)) ⇒ d = some ⟨t₀, ε⟩ →
      Tape.cells t₀ 0 = false
  | 0, _, _, p, b, _, _, h => by
    simp only [Machine.steps, Option.some.injEq, Machine.mk.injEq] at h
    cases p <;> cases h.2
  | _ + 1, _, _, .gap _ _ _, _, hp, _, _ => absurd hp id
  | d + 1, t, t₀, .left p, b, hp, hb, h =>
    loop_exit_cell_false d (Tape.moveL t) t₀ p b hp hb h
  | d + 1, t, t₀, .right p, b, hp, hb, h =>
    loop_exit_cell_false d (Tape.moveR t) t₀ p b hp hb h
  | d + 1, t, t₀, .flip p, b, hp, hb, h =>
    loop_exit_cell_false d (Tape.flip t) t₀ p b hp hb h
  | d + 1, t, t₀, .loop b₁ p, b, hp, hb, h => by
    simp only [loop_append, Machine.steps, Machine.step, Option.bind_some] at h
    have hite : (if Tape.cells t 0 then b₁ ++ .loop b₁ (p ++ .loop b ε) else p ++ .loop b ε) =
        (if Tape.cells t 0 then b₁ ++ .loop b₁ p else p) ++ .loop b ε := by
      split <;> simp [append_assoc]
    rw [hite] at h
    have hcl : (if Tape.cells t 0 then b₁ ++ .loop b₁ p else p)° := by
      split; exact closed_append hp.1 hp; exact hp.2
    exact loop_exit_cell_false d t t₀ _ b hcl hb h
  | d + 1, t, t₀, ε, b, _, hb, h => by
    simp only [nil_append, Machine.steps, Machine.step, Option.bind_some] at h
    cases hcell : Tape.cells t 0
    · simp only [hcell, Bool.false_eq_true, ↓reduceIte] at h
      cases d with
      | zero =>
        simp only [Machine.steps, Option.some.injEq, Machine.mk.injEq] at h
        rw [← h.1, hcell]
      | succ d' =>
        simp only [Machine.steps, Machine.step] at h; cases h
    · simp only [hcell, ↓reduceIte] at h
      exact loop_exit_cell_false d t t₀ b b hb hb h

def peelLoops : Program → Program
  | .loop b u => peelLoops u ++ rep .left (‖b‖ + 2) ε
  | s         => s

theorem size_peelLoops : ∀ (s : Program), ‖peelLoops s‖ = ‖s‖
  | .loop b u => by
    simp only [peelLoops, size_append, size_rep .left (fun _ => rfl), size_peelLoops u, size]
    omega
  | .left _ | .right _ | .flip _ | .gap _ _ _ | ε => rfl

theorem closed_peelLoops : ∀ {s : Program}, s° → (peelLoops s)°
  | .loop _ _, hs =>
    closed_append (closed_peelLoops hs.2) (closed_rep .left (fun _ h => h) trivial)
  | .left _, hs | .right _, hs | .flip _, hs | .gap _ _ _, hs | ε, hs => hs

theorem not_loop_append_rep_left : ∀ (p : Program) (m : Nat), 0 < m →
    (∀ b u, p ≠ .loop b u) → ∀ b u, p ++ rep .left m ε ≠ .loop b u
  | ε, m + 1, _, _ => by simp [rep]
  | .left _, _, _, _ | .right _, _, _, _ | .flip _, _, _, _ | .gap _ _ _, _, _, _ => by simp
  | .loop b u, _, _, h => absurd rfl (h b u)

theorem not_loop_peelLoops : ∀ (s b u : Program), peelLoops s ≠ .loop b u
  | .loop b₀ u₀, b, u =>
    not_loop_append_rep_left (peelLoops u₀) (‖b₀‖ + 2) (by omega)
      (not_loop_peelLoops u₀) b u
  | .left _, _, _ | .right _, _, _ | .flip _, _, _ | .gap _ _ _, _, _ | ε, _, _ => by simp [peelLoops]

theorem peelLoops_dominates_of_cell_false {t₀ : SpecTape} (hcell : Tape.cells t₀ 0 = false) :
    ∀ (s : Program) (k : Nat), ((Machine.mk t₀ s) ⇓ k) →
      ∃ k' : Nat, k ≤ k' ∧ ((Machine.mk t₀ (peelLoops s)) ⇓ k')
  | .loop b u, k, hk => by
    cases k with
    | zero => rw [Machine.haltsIn_zero] at hk; cases hk
    | succ k =>
      have hst : (Machine.mk t₀ (.loop b u))⇒ = some ⟨t₀, u⟩ := by
        simp [Machine.step, hcell]
      obtain ⟨k', hle, u_tape, hu'⟩ :=
        peelLoops_dominates_of_cell_false hcell u k ((Machine.haltsIn_succ hst).mp hk)
      refine ⟨k' + (‖b‖ + 2), by omega,
        shiftTape u_tape ((‖b‖ + 2 : Nat) * (-1 : Int)), ?_⟩
      show (Machine.mk t₀ (peelLoops u ++ rep .left (‖b‖ + 2) ε)) ⇒ (k' + (‖b‖ + 2)) = _
      rw [Machine.steps_add, steps_append_tail k' _ _ (peelLoops u) _ hu', Option.bind_some,
        steps_rep_shift .left (-1) (fun _ _ => rfl)]
  | .left _, k, hk | .right _, k, hk | .flip _, k, hk | .gap _ _ _, k, hk | ε, k, hk =>
    ⟨k, Nat.le_refl k, hk⟩

theorem sub_shapes_of_topShapes {noShift afterLoop : Bool} {k : Nat} {c : Program} :
    c ∈ topShapes noShift afterLoop k → c ∈ shapes noShift k := by
  intro hc
  unfold topShapes at hc
  split at hc
  · next hk0 => simp [shapes, hk0, hc]
  · next hk0 =>
    simp only [shapes, hk0, ↓reduceIte, List.mem_append, List.mem_singleton] at hc ⊢
    rcases hc with ((rfl | hls) | hrs) | hns
    · refine .inl (.inl (mem_flatMap_rep (m := k) (r := 0) (by omega) (by omega) ?_))
      simp [nonShiftShapes]
    · simp only [List.mem_flatMap, List.mem_range, List.mem_map] at hls ⊢
      obtain ⟨i, hi, d, hd, rfl⟩ := hls
      exact .inl (.inl ⟨i, hi, d, sub_nonShiftShapes_of_topNonShiftShapes hd, rfl⟩)
    · cases noShift with
      | true => simp at hrs
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, List.mem_flatMap, List.mem_range, List.mem_map] at hrs ⊢
        obtain ⟨i, hi, d, hd, rfl⟩ := hrs
        exact .inl (.inr ⟨i, hi, d, sub_nonShiftShapes_of_topNonShiftShapes hd, rfl⟩)
    · exact .inr (sub_nonShiftShapes_of_topNonShiftShapes hns)

theorem dominates_append_pre_of_cell_false {pre pre₀ b s : Program}
    (hpre : pre°) (hpre₀ : pre₀°) (hb : b°) (heq : pre = pre₀ ++ .loop b ε) :
    (pre ++ s) ≼ (pre ++ peelLoops s) := by
  intro k hk
  obtain ⟨u, hu⟩ := hk SpecTape
  change (Machine.mk (Tape.blank : SpecTape) (pre ++ s)) ⇒ k = some ⟨u, ε⟩ at hu
  obtain ⟨d, k₂, t₀, rfl, hpre_steps, hk₂⟩ := steps_append_split hpre hu
  have hpre_end : (Machine.mk (Tape.blank : SpecTape) (pre₀ ++ .loop b ε)) ⇒ d = some ⟨t₀, ε⟩ := by
    rw [← heq]; simpa using hpre_steps ε
  obtain ⟨d₀, d₁, t₁, rfl, hpre₀_steps, _⟩ := steps_append_split hpre₀ hpre_end
  rw [Machine.steps_add, hpre₀_steps (.loop b ε), Option.bind_some] at hpre_end
  have hcell : Tape.cells t₀ 0 = false :=
    loop_exit_cell_false d₁ t₁ t₀ ε b trivial hb (by simpa [nil_append] using hpre_end)
  obtain ⟨k₂', hle₂, u', hu'⟩ := peelLoops_dominates_of_cell_false hcell s k₂ hk₂
  refine ⟨d₀ + d₁ + k₂', by omega, Program.haltsIn_of ⟨u', ?_⟩⟩
  show (Machine.mk (Tape.blank : SpecTape) (pre ++ peelLoops s)) ⇒ (d₀ + d₁ + k₂') = some ⟨u', ε⟩
  rw [Machine.steps_add, hpre_steps (peelLoops s), Option.bind_some]
  exact hu'

theorem dominates_append_rep_left_of_le {pre s : Program} (hpre : pre°)
    (hle : ∀ (t₀ : SpecTape) (k₂ : Nat), (Machine.mk t₀ s) ⇓ k₂ → k₂ ≤ ‖s‖) :
    (pre ++ s) ≼ (pre ++ rep .left ‖s‖ ε) := by
  intro k hk
  obtain ⟨u, hu⟩ := hk SpecTape
  change (Machine.mk (Tape.blank : SpecTape) (pre ++ s)) ⇒ k = some ⟨u, ε⟩ at hu
  obtain ⟨d, k₂, t₀, rfl, hpre_steps, hk₂⟩ := steps_append_split hpre hu
  have hk₂_le := hle t₀ k₂ hk₂
  refine ⟨d + ‖s‖, by omega,
    Program.haltsIn_of ⟨shiftTape t₀ ((‖s‖ : Nat) * (-1 : Int)), ?_⟩⟩
  show (Machine.mk (Tape.blank : SpecTape) (pre ++ rep .left ‖s‖ ε)) ⇒ (d + ‖s‖) = _
  rw [Machine.steps_add, hpre_steps (rep .left ‖s‖ ε), Option.bind_some,
    steps_rep_shift .left (-1) (fun _ _ => rfl)]

theorem topNonShiftShapes_cover (afterLoop : Bool) {r : Program}
    (hr : r°) (hns : NonShift r)
    (hafter : afterLoop = true → ∀ b u, r ≠ .loop b u)
    (ht3 : 3 ≤ ‖r‖)
    (hfl : ∀ u, r = .flip u → 3 ≤ ‖u‖)
    (hlp : ∀ u, r = .loop ε u → 2 ≤ ‖u‖) :
    (∃ c ∈ topNonShiftShapes afterLoop ‖r‖, r ⊑ c) ∨
    (∃ s₁ s₂ r' : Program, StepDom s₁ s₂ ∧ r'° ∧ ‖r'‖ = ‖r‖ ∧
      (∃ c ∈ topNonShiftShapes afterLoop ‖r‖, r' ⊑ c) ∧ Congr s₁ s₂ r r') := by
  cases r with
  | nil => simp [size] at ht3
  | left _ | right _ => exact absurd hns id
  | gap => exact absurd hr id
  | flip u =>
    have hu3 := hfl u rfl
    refine .inl ⟨.flip (gap? ‖u‖), ?_, .flip (refines_gap? hr rfl)⟩
    simp only [topNonShiftShapes, size, show ¬ (‖u‖ + 1 = 0) by omega,
      show 4 ≤ ‖u‖ + 1 by omega, ↓reduceIte, List.mem_append, List.mem_singleton]
    exact .inl (by simp)
  | loop b u =>
    by_cases hb0 : ‖b‖ = 0
    · have hbe : b = ε := size_eq_zero_of_closed hr.1 hb0
      subst hbe
      have hu2 := hlp u rfl
      refine .inr ⟨.loop ε ε, .flip (.flip ε), .flip (.flip u), stepDom_emptyLoop,
        hr.2, by simp [size], ?_,
        Congr.swap (s₁ := .loop ε ε) (s₂ := .flip (.flip ε)) (Congr.refl hr.2)⟩
      refine ⟨.flip (gap? (‖u‖ + 1)), ?_,
        .flip (refines_gap? hr.2 (by simp [size]))⟩
      simp only [size, Nat.zero_add]
      simp only [topNonShiftShapes, show ¬ (‖u‖ + 2 = 0) by omega,
        show 4 ≤ ‖u‖ + 2 by omega, ↓reduceIte, List.mem_append, List.mem_singleton]
      exact .inl (by simp)
    · cases hal : afterLoop with
      | true => exact absurd rfl (hafter hal b u)
      | false =>
        refine .inl ⟨.loop (gap? ‖b‖) (gap? ‖u‖), ?_,
          .loop (refines_gap? hr.1 rfl) (refines_gap? hr.2 rfl)⟩
        simp only [topNonShiftShapes, size, show ¬ (‖b‖ + ‖u‖ + 2 = 0) by omega,
          Bool.false_eq_true, ↓reduceIte, List.mem_append]
        refine .inr (List.mem_map.mpr ⟨‖b‖ - 1, List.mem_range.mpr (by omega), ?_⟩)
        congr 2 <;> omega

theorem mem_flatMap_topRep {f : Program → Program} {k m r : Nat} {c : Program}
    (hm : 0 < m) (hsz : k = m + r) (hc : c ∈ topNonShiftShapes false r) :
    rep f m c ∈ (List.range k).flatMap fun (i : Nat) =>
      (topNonShiftShapes false (k - 1 - i)).map (rep f (i + 1)) := by
  simp only [List.mem_flatMap, List.mem_range, List.mem_map]
  exact ⟨m - 1, by omega, c, by rwa [show k - 1 - (m - 1) = r by omega],
    by rw [show m - 1 + 1 = m by omega]⟩

theorem mem_topShapes_of_not_short (noShift afterLoop : Bool) {s : Program}
    (hs : s°) (h0 : ‖s‖ ≠ 0)
    (hafter : afterLoop = true → ∀ b u, s ≠ .loop b u)
    (ht3 : 3 ≤ ‖shiftTail s‖)
    (hfl : ∀ u, shiftTail s = .flip u → 3 ≤ ‖u‖)
    (hlp : ∀ u, shiftTail s = .loop ε u → 2 ≤ ‖u‖) :
    ∃ c ∈ topShapes noShift afterLoop ‖s‖,
      s ⊑ c ∨
      (noShift = true ∧ s.mirror ⊑ c) ∨
      (∃ s₁ s₂ s' : Program,
        StepDom s₁ s₂ ∧ s'° ∧ ‖s'‖ = ‖s‖ ∧ s' ⊑ c ∧
        (Congr s₁ s₂ s s' ∨ (noShift = true ∧ Congr s₁ s₂ s.mirror s'))) := by
  have hsp := shiftPrefix_append_tail s
  have hsz : ‖s‖ = countL s + countR s + ‖shiftTail s‖ := by
    have := congrArg size hsp; rw [size_append, size_shiftPrefix] at this; exact this.symm
  have ht_cl := closed_shiftTail hs
  have ht_ns := nonShift_shiftTail s
  by_cases ha : countL s = 0
  · by_cases hb : countR s = 0
    · have hst : shiftTail s = s := by
        simpa [shiftPrefix_eq_left hb, ha, rep] using hsp
      rcases topNonShiftShapes_cover afterLoop ht_cl ht_ns
          (fun hal b u hbu => hafter hal b u (by rwa [← hst]))
          ht3 hfl hlp with
        ⟨c, hc, hrc⟩ | ⟨s₁, s₂, r', hsd, hr'_cl, hr'_sz, ⟨c, hc, hrc⟩, hcr⟩
      · rw [hst] at hc hrc
        exact ⟨c, by simp only [topShapes, h0, ↓reduceIte, List.mem_append]; exact .inr hc, .inl hrc⟩
      · rw [hst] at hc hr'_sz hcr
        exact ⟨c, by simp only [topShapes, h0, ↓reduceIte, List.mem_append]; exact .inr hc,
          .inr (.inr ⟨s₁, s₂, r', hsd, hr'_cl, hr'_sz, hrc, .inl hcr⟩)⟩
    · have hseq : s = rep .right (countR s) (shiftTail s) := by
        simpa [shiftPrefix_eq_right ha, rep_append .right right_append] using hsp.symm
      cases noShift with
      | false =>
        rcases topNonShiftShapes_cover false ht_cl ht_ns (by intro h; cases h) ht3 hfl hlp with
          ⟨c, hc, hrc⟩ | ⟨s₁, s₂, r', hsd, hr'_cl, hr'_sz, ⟨c, hc, hrc⟩, hcr⟩
        · refine ⟨rep .right (countR s) c, ?_, .inl ?_⟩
          · simp only [topShapes, h0, ↓reduceIte, Bool.false_eq_true, List.mem_append]
            exact .inl (.inr (mem_flatMap_topRep (by omega) (by omega) hc))
          · have hr := refines_rep .right (fun h => .right h) (n := countR s) hrc
            rwa [← hseq] at hr
        · refine ⟨rep .right (countR s) c, ?_,
            .inr (.inr ⟨s₁, s₂, rep .right (countR s) r', hsd,
              closed_rep .right (fun _ h => h) hr'_cl,
              by rw [size_rep .right (fun _ => rfl), hr'_sz]; omega,
              refines_rep .right (fun h => .right h) hrc,
              .inl (by
                have hcr' := Congr.rep .right Congr.right (n := countR s) hcr
                rwa [← hseq] at hcr')⟩)⟩
          simp only [topShapes, h0, ↓reduceIte, Bool.false_eq_true, List.mem_append]
          exact .inl (.inr (mem_flatMap_topRep (by omega) (by omega) hc))
      | true =>
        have htm_ns : NonShift (shiftTail s).mirror := by
          cases h : shiftTail s with
          | left _ | right _ => rw [h] at ht_ns; exact absurd ht_ns id
          | _ => simp [mirror, NonShift]
        have hsm : s.mirror = rep .left (countR s) (shiftTail s).mirror := by
          rw [← mirror_rep_right, ← hseq]
        have ht3_m : 3 ≤ ‖(shiftTail s).mirror‖ := by rw [size_mirror]; exact ht3
        have hfl_m : ∀ u, (shiftTail s).mirror = .flip u → 3 ≤ ‖u‖ := by
          intro u hu
          cases hst_cases : shiftTail s with
          | flip u₀ =>
            rw [hst_cases, mirror, Program.flip.injEq] at hu
            subst hu; rw [size_mirror]
            exact hfl u₀ hst_cases
          | left _ | right _ | loop _ _ | gap _ _ _ | nil =>
            rw [hst_cases] at hu; cases hu
        have hlp_m : ∀ u, (shiftTail s).mirror = .loop ε u → 2 ≤ ‖u‖ := by
          intro u hu
          cases hst_cases : shiftTail s with
          | loop b₀ u₀ =>
            rw [hst_cases, mirror, Program.loop.injEq] at hu
            have hb₀ : b₀ = ε := by cases b₀ <;> cases hu.1; rfl
            subst hb₀; rcases hu with ⟨_, rfl⟩
            rw [size_mirror]
            exact hlp u₀ hst_cases
          | left _ | right _ | flip _ | gap _ _ _ | nil =>
            rw [hst_cases] at hu; cases hu
        rcases topNonShiftShapes_cover false (closed_mirror ht_cl) htm_ns
            (by intro h; cases h) ht3_m hfl_m hlp_m with
          ⟨c, hc, hrc⟩ | ⟨s₁, s₂, r', hsd, hr'_cl, hr'_sz, ⟨c, hc, hrc⟩, hcr⟩
        · refine ⟨rep .left (countR s) c, ?_, .inr (.inl ⟨rfl, ?_⟩)⟩
          · simp only [topShapes, h0, ↓reduceIte, List.mem_append]
            exact .inl (.inl (.inr (mem_flatMap_topRep (by omega) (by rw [size_mirror]; omega) hc)))
          · have hr := refines_rep .left (fun h => .left h) (n := countR s) hrc
            rwa [← hsm] at hr
        · rw [size_mirror] at hr'_sz hc
          refine ⟨rep .left (countR s) c, ?_,
            .inr (.inr ⟨s₁, s₂, rep .left (countR s) r', hsd,
              closed_rep .left (fun _ h => h) hr'_cl,
              by rw [size_rep .left (fun _ => rfl), hr'_sz]; omega,
              refines_rep .left (fun h => .left h) hrc,
              .inr ⟨rfl, by
                have hcr' := Congr.rep .left Congr.left (n := countR s) hcr
                rwa [← hsm] at hcr'⟩⟩)⟩
          simp only [topShapes, h0, ↓reduceIte, List.mem_append]
          exact .inl (.inl (.inr (mem_flatMap_topRep (by omega) (by omega) hc)))
  · by_cases hb : countR s = 0
    · have hseq : s = rep .left (countL s) (shiftTail s) := by
        simpa [shiftPrefix_eq_left hb, rep_append .left left_append] using hsp.symm
      rcases topNonShiftShapes_cover false ht_cl ht_ns (by intro h; cases h) ht3 hfl hlp with
        ⟨c, hc, hrc⟩ | ⟨s₁, s₂, r', hsd, hr'_cl, hr'_sz, ⟨c, hc, hrc⟩, hcr⟩
      · refine ⟨rep .left (countL s) c, ?_, .inl ?_⟩
        · simp only [topShapes, h0, ↓reduceIte, List.mem_append]
          exact .inl (.inl (.inr (mem_flatMap_topRep (by omega) (by omega) hc)))
        · have hr := refines_rep .left (fun h => .left h) (n := countL s) hrc
          rwa [← hseq] at hr
      · refine ⟨rep .left (countL s) c, ?_,
          .inr (.inr ⟨s₁, s₂, rep .left (countL s) r', hsd,
            closed_rep .left (fun _ h => h) hr'_cl,
            by rw [size_rep .left (fun _ => rfl), hr'_sz]; omega,
            refines_rep .left (fun h => .left h) hrc,
            .inl (by
              have hcr' := Congr.rep .left Congr.left (n := countL s) hcr
              rwa [← hseq] at hcr')⟩)⟩
        simp only [topShapes, h0, ↓reduceIte, List.mem_append]
        exact .inl (.inl (.inr (mem_flatMap_topRep (by omega) (by omega) hc)))
    · obtain ⟨u, hu_cl, hu_sz, hnorm⟩ :=
        normShifts_eq_flip (Nat.pos_of_ne_zero ha) (Nat.pos_of_ne_zero hb)
      have hse : StepEquiv (shiftPrefix s) (normShifts (countL s) (countR s)) :=
        ⟨countL s + countR s, by omega, fun t =>
          ⟨shiftTape t ((countR s : Int) - (countL s : Int)), fun r =>
            ⟨steps_shiftPrefix s t r, steps_normShifts (countL s) (countR s) t r⟩⟩⟩
      refine ⟨.flip (gap? (‖s‖ - 1)), ?_, .inr (.inr ⟨shiftPrefix s, normShifts (countL s) (countR s),
        normShifts (countL s) (countR s) ++ shiftTail s, hse.stepDom,
        closed_append (closed_normShifts _ _) ht_cl,
        by rw [size_append, size_normShifts]; omega, ?_, .inl ?_⟩)⟩
      · simp only [topShapes, h0, ↓reduceIte, List.mem_append, topNonShiftShapes,
          show 4 ≤ ‖s‖ by omega, List.mem_singleton, true_or]
        exact .inr trivial
      · rw [hnorm, flip_append]
        exact .flip (refines_gap? (closed_append hu_cl ht_cl) (by rw [size_append, hu_sz]; omega))
      · have hsw := Congr.swap (s₁ := shiftPrefix s) (s₂ := normShifts (countL s) (countR s))
          (Congr.refl ht_cl)
        rwa [hsp] at hsw

theorem topTail_cover {pre s : Program} (noShift afterLoop : Bool)
    (hpre : pre°) (hs : s°) (hs_pos : 0 < ‖s‖)
    (hns_pre : noShift = true → pre.noShift = true)
    (hafter : afterLoop = true → ∃ pre₀ b : Program, pre₀° ∧ b° ∧ pre = pre₀ ++ .loop b ε) :
    ∃ c ∈ topShapes noShift afterLoop ‖s‖, ∃ p', p'° ∧ p' ⊑ (pre ++ c) ∧ (pre ++ s) ≼ p' := by
  let s₁ := if afterLoop then peelLoops s else s
  have hs₁ : s₁° := by
    dsimp [s₁]; split; exact closed_peelLoops hs; exact hs
  have hsz₁ : ‖s₁‖ = ‖s‖ := by
    dsimp [s₁]; split; exact size_peelLoops s; rfl
  have hdom₁ : (pre ++ s) ≼ (pre ++ s₁) := by
    dsimp [s₁]; split
    · next hal =>
      obtain ⟨pre₀, b, hpre₀, hb, heq⟩ := hafter hal
      exact dominates_append_pre_of_cell_false hpre hpre₀ hb heq
    · exact Dominates.refl _
  have hafter₁ : afterLoop = true → ∀ b u, s₁ ≠ .loop b u := by
    intro hal
    simp only [s₁, hal, ↓reduceIte]
    exact not_loop_peelLoops s
  have hleaf : (∀ (t₀ : SpecTape) (k₂ : Nat), (Machine.mk t₀ s₁) ⇓ k₂ → k₂ ≤ ‖s₁‖) →
      ∃ c ∈ topShapes noShift afterLoop ‖s‖, ∃ p', p'° ∧ p' ⊑ (pre ++ c) ∧ (pre ++ s) ≼ p' := by
    intro hle
    have h0 : ‖s‖ ≠ 0 := by omega
    refine ⟨rep .left ‖s‖ ε, ?_, pre ++ rep .left ‖s‖ ε,
      closed_append hpre (closed_rep .left (fun _ h => h) trivial),
      refines_append_closed_left pre hpre (Program.Refines.refl _),
      Dominates.trans hdom₁ ?_⟩
    · simp [topShapes, h0]
    · rw [← hsz₁]
      exact dominates_append_rep_left_of_le hpre hle
  by_cases ht2 : ‖shiftTail s₁‖ ≤ 2
  · exact hleaf (fun t₀ k₂ hk₂ =>
      haltsIn_shiftPrefix_le (fun _ _ hd => haltsIn_le_size_of_le_two (closed_shiftTail hs₁) ht2 hd) hk₂)
  · by_cases hfl2 : ∃ u, shiftTail s₁ = .flip u ∧ ‖u‖ ≤ 2
    · obtain ⟨u, hu_eq, hu2⟩ := hfl2
      exact hleaf (fun t₀ k₂ hk₂ =>
        haltsIn_shiftPrefix_le (fun _ _ hd => by
          rw [hu_eq] at hd ⊢
          have hu_cl : u° := by have := closed_shiftTail hs₁; rwa [hu_eq] at this
          exact haltsIn_le_size_of_flip_le_two hu_cl hu2 hd) hk₂)
    · by_cases hlp1 : ∃ u, shiftTail s₁ = .loop ε u ∧ ‖u‖ ≤ 1
      · obtain ⟨u, hu_eq, hu1⟩ := hlp1
        exact hleaf (fun t₀ k₂ hk₂ =>
          haltsIn_shiftPrefix_le (fun _ _ hd => by
            rw [hu_eq] at hd ⊢
            have hu_cl : u° := by have := closed_shiftTail hs₁; rw [hu_eq] at this; exact this.2
            exact haltsIn_le_size_of_loop_nil_le_one hu_cl hu1 hd) hk₂)
      · obtain ⟨c, hc, hsc | ⟨hns, hsc⟩ | ⟨x₁, x₂, s', hsd, hs', _, hs'c, hcs | ⟨hns, hcs⟩⟩⟩ :=
          mem_topShapes_of_not_short noShift afterLoop hs₁ (by omega) hafter₁ (by omega)
            (fun u hu => by have : ¬ ‖u‖ ≤ 2 := fun h => hfl2 ⟨u, hu, h⟩; omega)
            (fun u hu => by have : ¬ ‖u‖ ≤ 1 := fun h => hlp1 ⟨u, hu, h⟩; omega)
        · rw [hsz₁] at hc
          exact ⟨c, hc, pre ++ s₁, closed_append hpre hs₁,
            refines_append_closed_left pre hpre hsc, hdom₁⟩
        · rw [hsz₁] at hc
          have hpre_m : pre.mirror = pre := mirror_eq_self (hns_pre hns)
          have hmir : (pre ++ s₁) ≼ (pre ++ s₁.mirror) := by
            have h := (Equiv.mirror (pre ++ s₁)).dominates
            rwa [mirror_append, hpre_m] at h
          exact ⟨c, hc, pre ++ s₁.mirror, closed_append hpre (closed_mirror hs₁),
            refines_append_closed_left pre hpre hsc, Dominates.trans hdom₁ hmir⟩
        · rw [hsz₁] at hc
          have hdom₂ : (pre ++ s₁) ≼ (pre ++ s') :=
            Congr.dominates hsd ((Congr.refl hpre).append hcs)
          exact ⟨c, hc, pre ++ s', closed_append hpre hs',
            refines_append_closed_left pre hpre hs'c, Dominates.trans hdom₁ hdom₂⟩
        · rw [hsz₁] at hc
          have hpre_m : pre.mirror = pre := mirror_eq_self (hns_pre hns)
          have hmir : (pre ++ s₁) ≼ (pre ++ s₁.mirror) := by
            have h := (Equiv.mirror (pre ++ s₁)).dominates
            rwa [mirror_append, hpre_m] at h
          have hdom₂ : (pre ++ s₁.mirror) ≼ (pre ++ s') :=
            Congr.dominates hsd ((Congr.refl hpre).append hcs)
          exact ⟨c, hc, pre ++ s', closed_append hpre hs',
            refines_append_closed_left pre hpre hs'c,
            Dominates.trans hdom₁ (Dominates.trans hmir hdom₂)⟩

def runExpand (q : Program) (i : Fin q.numGaps) : List Program :=
  if q.isBlankGap then
    rootShapes (gapSize q i)
  else if q.isTopTailGap then
    (topShapes q.noShift q.isTopAfterLoop (gapSize q i)).map (q[i.val ↦ ·])
  else
    (shapes q.noShift (gapSize q i)).map (q[i.val ↦ ·])

theorem runExpand_cover {p q : Program} (i : Fin q.numGaps) :
    p° → p ⊑ q → ∃ c ∈ runExpand q i, ∃ p', p'° ∧ p' ⊑ c ∧ p ≼ p' := by
  intro hp hpq
  unfold runExpand
  split
  · next hblank =>
    obtain ⟨k, hk, rfl⟩ := eq_gap_of_isBlankGap hblank
    have hi0 : i = ⟨0, by simp [numGaps]⟩ := by
      ext; have := i.isLt; simp [numGaps] at this; omega
    subst hi0
    have hsz : ‖p‖ = k := by
      have := hpq.size
      simpa [size] using this
    simpa [gapSize, hsz] using rootShapes_cover hp
  · split
    · next htop =>
      obtain ⟨pre, k, hk, hpre, hq_eq, hafter⟩ := eq_append_gap_of_isTopTailGap q htop
      have hn : q.numGaps = 1 := by
        rw [hq_eq, numGaps_append_closed pre hpre]; simp [numGaps]
      have hi0 : i.val = 0 := by have := i.isLt; omega
      have hgs : gapSize q i = k := by
        have h1 := gapSize?_eq_some q i
        have h2 : gapSize? 0 q = some k := by
          rw [hq_eq]; exact gapSize?_zero_append_closed pre hpre k hk
        rw [hi0, h2] at h1
        exact (Option.some.inj h1).symm
      rw [hq_eq] at hpq
      obtain ⟨s, rfl, hsg⟩ := refines_append_closed_cancel pre hpre hpq
      have hs : s° := (closed_of_append hp).2
      have hsz_s : ‖s‖ = k := by
        have := hsg.size; simpa [size] using this
      obtain ⟨c, hc, p', hp', hp'c, hdom⟩ :=
        topTail_cover q.noShift q.isTopAfterLoop hpre hs (by omega)
          (fun hns => by rw [hq_eq] at hns; exact noShift_of_append pre _ hns) hafter
      rw [hsz_s, ← hgs] at hc
      refine ⟨q[i.val ↦ c], List.mem_map.mpr ⟨c, hc, rfl⟩, p', hp', ?_, hdom⟩
      rw [hi0, hq_eq, subst_zero_append_closed pre hpre]
      simpa [subst] using hp'c
    · obtain ⟨s, hs, hsz, hsub, hsubm, hsubc, hsubcm⟩ := subst_cover (gapSize?_eq_some q i) hp hpq
      obtain ⟨c, hc, hsc | ⟨hns, hsc⟩ | ⟨s₁, s₂, s', hsd, hs', _, hs'c, hcs | ⟨hns, hcs⟩⟩⟩ :=
        shapes_cover q.noShift hs
      · rw [hsz] at hc
        exact ⟨q[i.val ↦ c], List.mem_map.mpr ⟨c, hc, rfl⟩, p, hp, hsub c hsc, Dominates.refl p⟩
      · rw [hsz] at hc
        have hm := hsubm c hsc; rw [mirror_eq_self hns] at hm
        exact ⟨q[i.val ↦ c], List.mem_map.mpr ⟨c, hc, rfl⟩, p.mirror, closed_mirror hp, hm,
          (Equiv.mirror p).dominates⟩
      · rw [hsz] at hc
        obtain ⟨p', hp', hp'c, hcp⟩ := hsubc s₁ s₂ s' c hs' hs'c hcs
        exact ⟨q[i.val ↦ c], List.mem_map.mpr ⟨c, hc, rfl⟩, p', hp', hp'c, Congr.dominates hsd hcp⟩
      · rw [hsz] at hc
        obtain ⟨p', hp', hp'c, hcp⟩ := hsubcm s₁ s₂ s' c hs' hs'c hcs
        rw [mirror_eq_self hns] at hp'c
        refine ⟨q[i.val ↦ c], List.mem_map.mpr ⟨c, hc, rfl⟩, p', hp', hp'c, ?_⟩
        intro k hk
        exact Congr.dominates hsd hcp k ((Equiv.mirror p k).mp hk)

theorem gapSum_rep_left : ∀ (m : Nat) (c : Program), ‖rep .left m c‖° = ‖c‖°
  | 0,     _ => rfl
  | m + 1, c => by simp [rep, gapSum, gapSum_rep_left m c]

theorem gapSum_rep_right : ∀ (m : Nat) (c : Program), ‖rep .right m c‖° = ‖c‖°
  | 0,     _ => rfl
  | m + 1, c => by simp [rep, gapSum, gapSum_rep_right m c]

theorem gapSum_nonShiftShapes {r : Nat} {c : Program} :
    c ∈ nonShiftShapes r → ‖c‖° ≤ r - 1 := by
  intro hc
  unfold nonShiftShapes at hc
  split at hc
  · simp only [List.mem_singleton] at hc; subst hc; simp [gapSum]
  · simp only [List.mem_append, List.mem_singleton, List.mem_map, List.mem_range] at hc
    rcases hc with rfl | ⟨a, ha, rfl⟩
    · simp [gapSum]
    · simp only [gapSum, gapSum_gap?]; omega

/-- Every shape fixes at least one command, so its gaps are strictly smaller than the gap it fills. -/
theorem gapSum_shapes {noShift : Bool} {k : Nat} {c : Program} :
    0 < k → c ∈ shapes noShift k → ‖c‖° < k := by
  intro hk hc
  unfold shapes at hc
  split at hc
  · omega
  · simp only [List.mem_append] at hc
    rcases hc with (hls | hrs) | hns
    · simp only [List.mem_flatMap, List.mem_range, List.mem_map] at hls
      obtain ⟨i, hi, d, hd, rfl⟩ := hls
      have := gapSum_nonShiftShapes hd; rw [gapSum_rep_left]; omega
    · cases noShift
      · simp only [Bool.false_eq_true, ↓reduceIte, List.mem_flatMap, List.mem_range,
          List.mem_map] at hrs
        obtain ⟨i, hi, d, hd, rfl⟩ := hrs
        have := gapSum_nonShiftShapes hd; rw [gapSum_rep_right]; omega
      · simp at hrs
    · have := gapSum_nonShiftShapes hns; omega

theorem gapSum_rootShapes {k : Nat} {c : Program} :
    0 < k → c ∈ rootShapes k → ‖c‖° < k := by
  intro hk hc
  unfold rootShapes at hc
  split at hc
  · omega
  · simp only [List.mem_append, List.mem_singleton, List.mem_map, List.mem_range] at hc
    rcases hc with (rfl | ⟨a, ha, rfl⟩) | ⟨i, hi, rfl⟩
    · rw [gapSum_rep_left]; simp [gapSum]; omega
    · simp only [gapSum, gapSum_gap?]; omega
    · simp only [gapSum, gapSum_rep_left, gapSum_gap?]; omega

theorem runExpand_decreasing {q c : Program} {i : Fin q.numGaps} :
    c ∈ runExpand q i → ‖c‖° < ‖q‖° := by
  intro hc
  unfold runExpand at hc
  split at hc
  · next hblank =>
    obtain ⟨k, hk, rfl⟩ := eq_gap_of_isBlankGap hblank
    have hi0 : i = ⟨0, by simp [numGaps]⟩ := by
      ext; have := i.isLt; simp [numGaps] at this; omega
    subst hi0
    have := gapSum_rootShapes hk hc
    simpa [gapSize, gapSum] using this
  · split at hc
    · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hc
      have h₀ := gapSize?_pos (gapSize?_eq_some q i)
      have h₁ := gapSum_subst s (gapSize?_eq_some q i)
      have h₂ := gapSum_shapes h₀ (sub_shapes_of_topShapes hs)
      omega
    · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hc
      have h₀ := gapSize?_pos (gapSize?_eq_some q i)
      have h₁ := gapSum_subst s (gapSize?_eq_some q i)
      have h₂ := gapSum_shapes h₀ hs
      omega

theorem size_nonShiftShapes {r : Nat} {c : Program} :
    c ∈ nonShiftShapes r → ‖c‖ = r := by
  intro hc
  unfold nonShiftShapes at hc
  split at hc
  · simp only [List.mem_singleton] at hc; subst hc; simp [size]; omega
  · simp only [List.mem_append, List.mem_singleton, List.mem_map, List.mem_range] at hc
    rcases hc with rfl | ⟨a, ha, rfl⟩
    · simp [size]; omega
    · simp [size]; omega

theorem size_shapes {noShift : Bool} {k : Nat} {c : Program} :
    c ∈ shapes noShift k → ‖c‖ = k := by
  intro hc
  unfold shapes at hc
  split at hc
  · simp only [List.mem_singleton] at hc; subst hc; simp [size]; omega
  · simp only [List.mem_append] at hc
    rcases hc with (hls | hrs) | hns
    · simp only [List.mem_flatMap, List.mem_range, List.mem_map] at hls
      obtain ⟨i, hi, d, hd, rfl⟩ := hls
      rw [size_rep .left (fun _ => rfl), size_nonShiftShapes hd]; omega
    · cases noShift
      · simp only [Bool.false_eq_true, ↓reduceIte, List.mem_flatMap, List.mem_range,
          List.mem_map] at hrs
        obtain ⟨i, hi, d, hd, rfl⟩ := hrs
        rw [size_rep .right (fun _ => rfl), size_nonShiftShapes hd]; omega
      · simp at hrs
    · exact size_nonShiftShapes hns

theorem size_rootShapes {k : Nat} {c : Program} :
    c ∈ rootShapes k → ‖c‖ = k := by
  intro hc
  unfold rootShapes at hc
  split at hc
  · simp only [List.mem_singleton] at hc; subst hc; simp [size]; omega
  · simp only [List.mem_append, List.mem_singleton, List.mem_map, List.mem_range] at hc
    rcases hc with (rfl | ⟨a, ha, rfl⟩) | ⟨i, hi, rfl⟩
    · rw [size_rep .left (fun _ => rfl)]; simp [size]
    · simp [size]; omega
    · simp [size, size_rep .left (fun _ => rfl)]; omega

theorem runExpand_size {q c : Program} {i : Fin q.numGaps} :
    c ∈ runExpand q i → ‖c‖ = ‖q‖ := by
  intro hc
  unfold runExpand at hc
  split at hc
  · next hblank =>
    obtain ⟨k, hk, rfl⟩ := eq_gap_of_isBlankGap hblank
    have hi0 : i = ⟨0, by simp [numGaps]⟩ := by
      ext; have := i.isLt; simp [numGaps] at this; omega
    subst hi0
    have := size_rootShapes hc
    simpa [gapSize, size] using this
  · split at hc
    · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hc
      have := size_subst s (gapSize?_eq_some q i)
      have := size_shapes (sub_shapes_of_topShapes hs)
      omega
    · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hc
      have := size_subst s (gapSize?_eq_some q i)
      have := size_shapes hs
      omega

end Program

namespace Expander

def tnf : Expander where
  expand     := Program.runExpand
  cover      := Program.runExpand_cover
  decreasing := Program.runExpand_decreasing
  size       := Program.runExpand_size

end Expander

abbrev Φ₁ : Expander := .tnf

end BBBTape
