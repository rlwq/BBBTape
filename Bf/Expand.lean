import Bf.Mirror

namespace Bf

namespace Program

open scoped Program Machine

theorem closed_append {p q : Program} : p° → q° → (p ++ q)° := by
  intro hp hq
  induction p with
  | nil => exact hq
  | left _ ih | right _ ih | flip _ ih => exact ih hp
  | loop _ _ _ ihp => exact ⟨hp.1, ihp hp.2⟩
  | gap => exact absurd hp id

theorem closed_of_append {p q : Program} : (p ++ q)° → p° ∧ q° := by
  induction p with
  | nil => exact fun h => ⟨trivial, h⟩
  | left _ ih | right _ ih | flip _ ih => exact ih
  | loop _ _ _ ihp => exact fun ⟨hb, hq⟩ => ⟨⟨hb, (ihp hq).1⟩, (ihp hq).2⟩
  | gap => exact fun h => absurd h id

theorem size_eq_zero_of_closed {p : Program} : p° → ‖p‖ = 0 → p = ε := by
  intro hp hs
  cases p with
  | nil => rfl
  | gap => exact absurd hp id
  | _ => simp [size] at hs

theorem refines_gap? {s : Program} {k : Nat} : s° → ‖s‖ = k → s ⊑ gap? k := by
  intro hs hk
  cases k with
  | zero => rw [size_eq_zero_of_closed hs hk]; exact .nil
  | succ k => simpa [gap?] using Refines.gap (h := Nat.succ_pos k) hk .nil

def rep (f : Program → Program) : Nat → Program → Program
  | 0,     r => r
  | n + 1, r => f (rep f n r)

theorem rep_append (f : Program → Program) (hf : ∀ p q, f p ++ q = f (p ++ q)) :
    ∀ n p q, rep f n p ++ q = rep f n (p ++ q)
  | 0,     _, _ => rfl
  | n + 1, p, q => by simp [rep, hf, rep_append f hf n]

theorem size_rep (f : Program → Program) (hf : ∀ p, ‖f p‖ = ‖p‖ + 1) :
    ∀ n r, ‖rep f n r‖ = n + ‖r‖
  | 0,     _ => by simp [rep]
  | n + 1, r => by simp [rep, hf, size_rep f hf n]; omega

theorem closed_rep (f : Program → Program) (hf : ∀ p, p° → (f p)°) :
    ∀ {n r}, r° → (rep f n r)°
  | 0,     _, hr => hr
  | _ + 1, _, hr => hf _ (closed_rep f hf hr)

theorem refines_rep (f : Program → Program) (hf : ∀ {p q : Program}, p ⊑ q → f p ⊑ f q) :
    ∀ {n : Nat} {p q : Program}, p ⊑ q → rep f n p ⊑ rep f n q
  | 0,     _, _, h => h
  | _ + 1, _, _, h => hf (refines_rep f hf h)

theorem mirror_rep_right : ∀ n r, (rep .right n r).mirror = rep .left n r.mirror
  | 0,     _ => rfl
  | n + 1, r => by simp [rep, mirror, mirror_rep_right n]

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

theorem StepEquiv.symm {s₁ s₂ : Program} : StepEquiv s₁ s₂ → StepEquiv s₂ s₁ :=
  fun ⟨d, hd, h⟩ => ⟨d, hd, fun t => let ⟨t', hr⟩ := h t; ⟨t', fun r => (hr r).symm⟩⟩

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

theorem Congr.haltsIn {s₁ s₂ p q : Program} {t : SpecTape} {k : Nat} :
    StepEquiv s₁ s₂ → Congr s₁ s₂ p q →
      ((Machine.mk t p) ⇓ k) → ((Machine.mk t q) ⇓ k) := by
  intro hse
  induction k using Nat.strongRecOn generalizing p q t with
  | _ k ih =>
    intro hc hk
    cases hc with
    | nil => exact hk
    | left h | right h | flip h =>
      cases k with
      | zero => rw [Machine.haltsIn_zero] at hk; cases hk
      | succ k =>
        exact (Machine.haltsIn_succ rfl).mpr (ih k (by omega) h ((Machine.haltsIn_succ rfl).mp hk))
    | @loop b b' p q hb hp =>
      cases k with
      | zero => rw [Machine.haltsIn_zero] at hk; cases hk
      | succ k =>
        refine (Machine.haltsIn_succ rfl).mpr
          (ih k (by omega) ?_ ((Machine.haltsIn_succ rfl).mp hk))
        cases Tape.cells t 0
        · exact hp
        · exact hb.append (.loop hb hp)
    | @swap p q h =>
      obtain ⟨d, hd, hst⟩ := hse
      obtain ⟨t', hr⟩ := hst t
      obtain ⟨u, hu⟩ := hk
      by_cases hdk : d ≤ k
      · obtain ⟨j, rfl⟩ : ∃ j : Nat, k = d + j := ⟨k - d, by omega⟩
        rw [Machine.steps_add, (hr p).1, Option.bind_some] at hu
        obtain ⟨u', hu'⟩ := ih j (by omega) h ⟨u, hu⟩
        exact ⟨u', by rw [Machine.steps_add, (hr q).2, Option.bind_some]; exact hu'⟩
      · have hnone : (Machine.mk t (s₁ ++ p)) ⇒ (k + 1) = none := by
          rw [Machine.steps_add, hu, Option.bind_some]; rfl
        have hsome := Machine.isSome_steps_of_le (hr p).1 (by omega : k + 1 ≤ d)
        rw [hnone] at hsome; cases hsome

theorem Congr.equiv {s₁ s₂ p q : Program} :
    StepEquiv s₁ s₂ → Congr s₁ s₂ p q → p ~ q := fun hse hc _ =>
  ⟨fun hk => Program.haltsIn_of (Congr.haltsIn hse hc (hk SpecTape)),
   fun hk => Program.haltsIn_of (Congr.haltsIn hse.symm hc.symm (hk SpecTape))⟩

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
      (List.range (r - 1)).map fun (a : Nat) => .loop (gap? a) (gap? (r - 2 - a))

theorem nonShiftShapes_cover {r : Program} :
    r° → NonShift r → ∃ c ∈ nonShiftShapes ‖r‖, r ⊑ c := by
  intro hr hns
  cases r with
  | nil => exact ⟨ε, by simp [nonShiftShapes, size], .nil⟩
  | left _ | right _ => exact absurd hns id
  | gap => exact absurd hr id
  | flip p => exact ⟨.flip (gap? ‖p‖), by simp [nonShiftShapes, size], .flip (refines_gap? hr rfl)⟩
  | loop b p =>
    refine ⟨.loop (gap? ‖b‖) (gap? ‖p‖), ?_,
      .loop (refines_gap? hr.1 rfl) (refines_gap? hr.2 rfl)⟩
    simp only [nonShiftShapes, size, show ¬ (‖b‖ + ‖p‖ + 2 = 0) by omega, ↓reduceIte,
      List.mem_append]
    exact .inr (List.mem_map.mpr ⟨‖b‖, List.mem_range.mpr (by omega), by congr 2; omega⟩)

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

theorem shapes_cover (noShift : Bool) {s : Program} :
    s° →
      ∃ c ∈ shapes noShift ‖s‖,
        s ⊑ c ∨
        (noShift = true ∧ s.mirror ⊑ c) ∨
        (∃ s₁ s₂ s' : Program,
          StepEquiv s₁ s₂ ∧ s'° ∧ ‖s'‖ = ‖s‖ ∧ s' ⊑ c ∧ Congr s₁ s₂ s s') := by
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
        obtain ⟨c, hc, hrc⟩ := nonShiftShapes_cover ht_cl ht_ns
        rw [hst] at hc hrc
        exact ⟨c, by simp only [shapes, h0, ↓reduceIte, List.mem_append]; exact .inr hc, .inl hrc⟩
      · have hseq : s = rep .right (countR s) (shiftTail s) := by
          simpa [shiftPrefix_eq_right ha, rep_append .right right_append] using hsp.symm
        cases noShift with
        | false =>
          obtain ⟨c, hc, hrc⟩ := nonShiftShapes_cover ht_cl ht_ns
          refine ⟨rep .right (countR s) c, ?_, .inl ?_⟩
          · simp only [shapes, h0, ↓reduceIte, Bool.false_eq_true, List.mem_append]
            exact .inl (.inr (mem_flatMap_rep (by omega) (by omega) hc))
          · have hr := refines_rep .right (fun h => .right h) (n := countR s) hrc
            rwa [← hseq] at hr
        | true =>
          have htm_ns : NonShift (shiftTail s).mirror := by
            cases h : shiftTail s with
            | left _ | right _ => rw [h] at ht_ns; exact absurd ht_ns id
            | _ => simp [mirror, NonShift]
          obtain ⟨c, hc, hrc⟩ := nonShiftShapes_cover (closed_mirror ht_cl) htm_ns
          refine ⟨rep .left (countR s) c, ?_, .inr (.inl ⟨rfl, ?_⟩)⟩
          · simp only [shapes, h0, ↓reduceIte, List.mem_append]
            exact .inl (.inl (mem_flatMap_rep (by omega) (by rw [size_mirror]; omega) hc))
          · have hr := refines_rep .left (fun h => .left h) (n := countR s) hrc
            rw [← mirror_rep_right, ← hseq] at hr; exact hr
    · by_cases hb : countR s = 0
      · have hseq : s = rep .left (countL s) (shiftTail s) := by
          simpa [shiftPrefix_eq_left hb, rep_append .left left_append] using hsp.symm
        obtain ⟨c, hc, hrc⟩ := nonShiftShapes_cover ht_cl ht_ns
        refine ⟨rep .left (countL s) c, ?_, .inl ?_⟩
        · simp only [shapes, h0, ↓reduceIte, List.mem_append]
          exact .inl (.inl (mem_flatMap_rep (by omega) (by omega) hc))
        · have hr := refines_rep .left (fun h => .left h) (n := countL s) hrc
          rwa [← hseq] at hr
      · obtain ⟨u, hu_cl, hu_sz, hnorm⟩ :=
          normShifts_eq_flip (Nat.pos_of_ne_zero ha) (Nat.pos_of_ne_zero hb)
        have hse : StepEquiv (shiftPrefix s) (normShifts (countL s) (countR s)) :=
          ⟨countL s + countR s, by omega, fun t =>
            ⟨shiftTape t ((countR s : Int) - (countL s : Int)), fun r =>
              ⟨steps_shiftPrefix s t r, steps_normShifts (countL s) (countR s) t r⟩⟩⟩
        refine ⟨.flip (gap? (‖s‖ - 1)), ?_, .inr (.inr ⟨shiftPrefix s, normShifts (countL s) (countR s),
          normShifts (countL s) (countR s) ++ shiftTail s, hse,
          closed_append (closed_normShifts _ _) ht_cl,
          by rw [size_append, size_normShifts]; omega, ?_, ?_⟩)⟩
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
          ∃ p' : Program, p'° ∧ p' ⊑ q[i ↦ c] ∧ Congr s₁ s₂ p p') := by
  intro hg hp hpq
  induction hpq generalizing i with
  | nil => cases hg
  | left _ ih =>
    obtain ⟨s, hs, hk, hc, hcm, hcg⟩ := ih hg hp
    exact ⟨s, hs, hk, fun c h => .left (hc c h), fun c h => .right (hcm c h),
      fun s₁ s₂ s' c hs' hsc hcs =>
        let ⟨p', hp', hp'c, hcp⟩ := hcg s₁ s₂ s' c hs' hsc hcs; ⟨.left p', hp', .left hp'c, .left hcp⟩⟩
  | right _ ih =>
    obtain ⟨s, hs, hk, hc, hcm, hcg⟩ := ih hg hp
    exact ⟨s, hs, hk, fun c h => .right (hc c h), fun c h => .left (hcm c h),
      fun s₁ s₂ s' c hs' hsc hcs =>
        let ⟨p', hp', hp'c, hcp⟩ := hcg s₁ s₂ s' c hs' hsc hcs; ⟨.right p', hp', .right hp'c, .right hcp⟩⟩
  | flip _ ih =>
    obtain ⟨s, hs, hk, hc, hcm, hcg⟩ := ih hg hp
    exact ⟨s, hs, hk, fun c h => .flip (hc c h), fun c h => .flip (hcm c h),
      fun s₁ s₂ s' c hs' hsc hcs =>
        let ⟨p', hp', hp'c, hcp⟩ := hcg s₁ s₂ s' c hs' hsc hcs; ⟨.flip p', hp', .flip hp'c, .flip hcp⟩⟩
  | @loop b' b p q hb hp_ref ihb ihp =>
    simp only [gapSize?] at hg
    split at hg
    · next hi =>
      obtain ⟨s, hs, hk, hc, hcm, hcg⟩ := ihb hg hp.1
      refine ⟨s, hs, hk,
        fun c h => by simp only [subst, hi, ↓reduceIte]; exact .loop (hc c h) hp_ref,
        fun c h => by simp only [mirror, subst, numGaps_mirror, hi, ↓reduceIte]; exact .loop (hcm c h) hp_ref.mirror,
        fun s₁ s₂ s' c hs' hsc hcs => ?_⟩
      obtain ⟨b'', hb'', hb''c, hcb⟩ := hcg s₁ s₂ s' c hs' hsc hcs
      exact ⟨.loop b'' p, ⟨hb'', hp.2⟩,
        by simp only [subst, hi, ↓reduceIte]; exact .loop hb''c hp_ref, .loop hcb (Congr.refl hp.2)⟩
    · next hi =>
      obtain ⟨s, hs, hk, hc, hcm, hcg⟩ := ihp hg hp.2
      refine ⟨s, hs, hk,
        fun c h => by simp only [subst, hi, ↓reduceIte]; exact .loop hb (hc c h),
        fun c h => by simp only [mirror, subst, numGaps_mirror, hi, ↓reduceIte]; exact .loop hb.mirror (hcm c h),
        fun s₁ s₂ s' c hs' hsc hcs => ?_⟩
      obtain ⟨p'', hp'', hp''c, hcp⟩ := hcg s₁ s₂ s' c hs' hsc hcs
      exact ⟨.loop b' p'', ⟨hp.1, hp''⟩,
        by simp only [subst, hi, ↓reduceIte]; exact .loop hb hp''c, .loop (Congr.refl hp.1) hcp⟩
  | @gap m _ s₀ p' q' hm hp_ref ihp =>
    obtain ⟨hs₀, hp'⟩ := closed_of_append hp
    cases i with
    | zero =>
      simp only [gapSize?, Option.some.injEq] at hg; subst hg
      exact ⟨s₀, hs₀, hm,
        fun c h => h.append hp_ref,
        fun c h => by rw [mirror_append]; exact h.append hp_ref.mirror,
        fun _ _ s' c hs' hsc hcs =>
          ⟨s' ++ p', closed_append hs' hp', hsc.append hp_ref, hcs.append (Congr.refl hp')⟩⟩
    | succ j =>
      obtain ⟨s, hs, hk, hc, hcm, hcg⟩ := ihp hg hp'
      exact ⟨s, hs, hk,
        fun c h => Refines.gap hm (hc c h),
        fun c h => by rw [mirror_append]; exact Refines.gap (by rw [size_mirror, hm]) (hcm c h),
        fun s₁ s₂ s' c hs' hsc hcs =>
          let ⟨p'', hp'', hp''c, hcp⟩ := hcg s₁ s₂ s' c hs' hsc hcs
          ⟨s₀ ++ p'', closed_append hs₀ hp'', Refines.gap hm hp''c, (Congr.refl hs₀).append hcp⟩⟩

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

def runExpand (q : Program) (i : Fin q.numGaps) : List Program :=
  (shapes q.noShift (gapSize q i)).map (q[i.val ↦ ·])

theorem runExpand_cover {p q : Program} (i : Fin q.numGaps) :
    p° → p ⊑ q → ∃ c ∈ runExpand q i, ∃ p', p'° ∧ p' ⊑ c ∧ p ~ p' := by
  intro hp hpq
  obtain ⟨s, hs, hsz, hsub, hsubm, hsubc⟩ := subst_cover (gapSize?_eq_some q i) hp hpq
  obtain ⟨c, hc, hsc | ⟨hns, hsc⟩ | ⟨s₁, s₂, s', hse, hs', _, hs'c, hcs⟩⟩ :=
    shapes_cover q.noShift hs
  · rw [hsz] at hc
    exact ⟨q[i.val ↦ c], List.mem_map.mpr ⟨c, hc, rfl⟩, p, hp, hsub c hsc, Equiv.refl p⟩
  · rw [hsz] at hc
    have hm := hsubm c hsc; rw [mirror_eq_self hns] at hm
    exact ⟨q[i.val ↦ c], List.mem_map.mpr ⟨c, hc, rfl⟩, p.mirror, closed_mirror hp, hm, Equiv.mirror p⟩
  · rw [hsz] at hc
    obtain ⟨p', hp', hp'c, hcp⟩ := hsubc s₁ s₂ s' c hs' hs'c hcs
    exact ⟨q[i.val ↦ c], List.mem_map.mpr ⟨c, hc, rfl⟩, p', hp', hp'c, Congr.equiv hse hcp⟩

theorem gapSum_rep_left : ∀ (m : Nat) (c : Program), (rep .left m c).gapSum = c.gapSum
  | 0,     _ => rfl
  | m + 1, c => by simp [rep, gapSum, gapSum_rep_left m c]

theorem gapSum_rep_right : ∀ (m : Nat) (c : Program), (rep .right m c).gapSum = c.gapSum
  | 0,     _ => rfl
  | m + 1, c => by simp [rep, gapSum, gapSum_rep_right m c]

theorem gapSum_nonShiftShapes {r : Nat} {c : Program} :
    c ∈ nonShiftShapes r → c.gapSum ≤ r - 1 := by
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
    0 < k → c ∈ shapes noShift k → c.gapSum < k := by
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

theorem runExpand_decreasing {q c : Program} {i : Fin q.numGaps} :
    c ∈ runExpand q i → c.gapSum < q.gapSum := by
  intro hc
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hc
  have h₀ := gapSize?_pos (gapSize?_eq_some q i)
  have h₁ := gapSum_subst s (gapSize?_eq_some q i)
  have h₂ := gapSum_shapes h₀ hs
  omega

end Program

open scoped Program in
structure Expander where
  expand     : (q : Program) → Fin q.numGaps → List Program
  cover      : ∀ {p q : Program} (i : Fin q.numGaps),
    p° → p ⊑ q → ∃ c ∈ expand q i, ∃ p', p'° ∧ p' ⊑ c ∧ p ~ p'
  /-- Every child is strictly less unknown than its parent, so expansion cannot go on forever. -/
  decreasing : ∀ {q c : Program} {i : Fin q.numGaps}, c ∈ expand q i → c.gapSum < q.gapSum

namespace Expander

def tnf : Expander where
  expand     := Program.runExpand
  cover      := Program.runExpand_cover
  decreasing := Program.runExpand_decreasing

end Expander

end Bf
