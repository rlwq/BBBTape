import BBBTape.Core.Decider
import BBBTape.Core.Expander
import BBBTape.Tapes.Spec

namespace BBBTape

open scoped Program Machine

def Bounded (B : Nat) (q : Program) : Prop :=
  ∀ (p : Program) (k : Nat), p° → p ⊑ q → p ⇓ k → k ≤ B

namespace Bounded

theorem of_halts {B t : Nat} {q : Program} :
    q ⇓ t → t ≤ B → Bounded B q := by
  intro hq ht p k _ hpq hk
  rw [Machine.HaltsIn.unique (hk SpecTape) (hpq.haltsIn hq SpecTape)]
  exact ht

theorem of_diverges {B : Nat} {q : Program} :
    q⇑ → Bounded B q := by
  intro hq p k _ hpq hk
  exact absurd ⟨k, hk SpecTape⟩ (Machine.not_halts_of_diverges (hpq.diverges hq SpecTape))

theorem of_expand {e : Expander} {B : Nat} {q : Program} (i : Fin q.numGaps) :
    (∀ c ∈ e.expand q i, Bounded B c) → Bounded B q := by
  intro hcs p k hp hpq hk
  obtain ⟨c, hc, p', hp', hp'c, hdom⟩ := e.cover i hp hpq
  obtain ⟨k', hkk', hk'⟩ := hdom k hk
  exact Nat.le_trans hkk' (hcs c hc p' k' hp' hp'c hk')

theorem upper {B n : Nat} :
    Bounded B (ω n) →
    ∀ (p : Program) (k : Nat), p° → ‖p‖ = n → p ⇓ k → k ≤ B := by
  intro h p k hp hn hk
  exact h p k hp (Program.refines_gap? hp hn) hk

end Bounded


/-- What a search leaves behind: the programs it could not settle,
and the longest halt it found together with a program that achieves it. -/
structure Outcome where
  holdouts : List Program
  longest  : Option (Nat × Program)

namespace Outcome

/-- The longer of two halts, preferring the first on a tie. -/
def pick (x y : Nat × Program) : Nat × Program := if x.1 < y.1 then y else x

theorem pick_assoc (x y z : Nat × Program) : pick (pick x y) z = pick x (pick y z) := by
  unfold pick
  by_cases h₁ : x.1 < y.1 <;> by_cases h₂ : y.1 < z.1 <;> by_cases h₃ : x.1 < z.1 <;>
    simp [h₁, h₂, h₃] <;> omega

def longer : Option (Nat × Program) → Option (Nat × Program) → Option (Nat × Program)
  | none,   b      => b
  | some x, none   => some x
  | some x, some y => some (pick x y)

theorem longer_assoc (a b c : Option (Nat × Program)) :
    longer (longer a b) c = longer a (longer b c) := by
  cases a <;> cases b <;> cases c <;> simp only [longer, pick_assoc]

theorem longer_none (a : Option (Nat × Program)) : longer a none = a := by
  cases a <;> rfl

def append (a b : Outcome) : Outcome :=
  ⟨a.holdouts ++ b.holdouts, longer a.longest b.longest⟩

instance : EmptyCollection Outcome := ⟨⟨[], none⟩⟩
instance : Append Outcome := ⟨append⟩

/-- Outcomes form a monoid componentwise: holdouts concatenate, and the longer halt wins. -/
instance : Std.Associative append where
  assoc a b c := by simp only [append, List.append_assoc, longer_assoc]

instance : Std.LawfulIdentity append ∅ where
  left_id _  := rfl
  right_id a := by
    show Outcome.mk (a.holdouts ++ []) (longer a.longest none) = a
    rw [List.append_nil, longer_none]

def concat (os : List Outcome) : Outcome := os.foldr (· ++ ·) ∅

/-- Every halt found takes at most `B` steps. -/
def Below (B : Nat) (o : Outcome) : Prop := ∀ x ∈ o.longest, x.1 ≤ B

/-- The value of the Busy Beaver function, if the search settled every program. -/
def value? (o : Outcome) : Option Nat :=
  if o.holdouts.isEmpty then o.longest.map (·.1) else none

theorem longer_cases {a b : Option (Nat × Program)} {x : Nat × Program} :
    longer a b = some x → a = some x ∨ b = some x := by
  intro h
  match a, b with
  | none, _ => exact .inr h
  | some _, none => exact .inl h
  | some y, some z =>
    simp only [longer, pick, Option.some.injEq] at h
    split at h
    · exact .inr (congrArg some h)
    · exact .inl (congrArg some h)

theorem below_longer {B : Nat} {a b : Option (Nat × Program)} :
    (∀ x ∈ longer a b, x.1 ≤ B) → (∀ x ∈ a, x.1 ≤ B) ∧ (∀ x ∈ b, x.1 ≤ B) := by
  intro h
  match a, b with
  | none, _ => exact ⟨fun _ hx => (nomatch hx), h⟩
  | some _, none => exact ⟨fun x hx => h x hx, fun _ hx => nomatch hx⟩
  | some y, some z =>
    have hp := h _ rfl
    simp only [pick] at hp
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩ <;> cases hx <;> split at hp <;> simp_all <;> omega

theorem holdouts_concat (os : List Outcome) :
    (concat os).holdouts = os.flatMap (·.holdouts) := by
  induction os with
  | nil => rfl
  | cons o os ih =>
    show o.holdouts ++ (concat os).holdouts = _
    rw [ih, List.flatMap_cons]

theorem below_concat {B : Nat} {os : List Outcome} :
    (concat os).Below B → ∀ o ∈ os, o.Below B := by
  induction os with
  | nil => intro _ o ho; exact nomatch ho
  | cons o os ih =>
    intro h o' ho'
    have ⟨h₁, h₂⟩ := below_longer h
    rcases List.mem_cons.mp ho' with rfl | ho'
    · exact h₁
    · exact ih h₂ o' ho'

theorem longest_concat {os : List Outcome} {x : Nat × Program} :
    (concat os).longest = some x → ∃ o ∈ os, o.longest = some x := by
  induction os with
  | nil => intro h; exact nomatch h
  | cons o os ih =>
    intro h
    rcases longer_cases h with h | h
    · exact ⟨o, List.mem_cons_self .., h⟩
    · obtain ⟨o', ho', h'⟩ := ih h
      exact ⟨o', List.mem_cons_of_mem _ ho', h'⟩

end Outcome

/-- Settle `q` with the decider, expanding a gap whenever execution gets stuck on it. -/
def search (e : Expander) (d : Decider) (q : Program) : Outcome :=
  match d q with
  | .halts t _  => ⟨[], some (t, q)⟩
  | .diverges _ => ∅
  | .stuck i    =>
    .concat ((e.expand q i).attach.map fun c => search e d c.1)
  | .unknown    => ⟨[q], none⟩
termination_by ‖q‖°
decreasing_by exact e.decreasing c.2

theorem search_bounded {e : Expander} {d : Decider} {B : Nat} (q : Program) :
    (∀ r ∈ (search e d q).holdouts, Bounded B r) → (search e d q).Below B → Bounded B q := by
  intro hh hb
  rw [search] at hh hb
  cases hv : d q with
  | halts t hq =>
    rw [hv] at hb
    exact Bounded.of_halts hq (hb (t, q) rfl)
  | diverges hq => exact Bounded.of_diverges hq
  | stuck i =>
    rw [hv] at hh hb
    refine Bounded.of_expand (e := e) i fun c hc => search_bounded (e := e) (d := d) c ?_ ?_
    · intro r hr
      apply hh
      rw [Outcome.holdouts_concat]
      exact List.mem_flatMap.mpr ⟨_, List.mem_map.mpr ⟨⟨c, hc⟩, List.mem_attach _ _, rfl⟩, hr⟩
    · exact Outcome.below_concat hb _ (List.mem_map.mpr ⟨⟨c, hc⟩, List.mem_attach _ _, rfl⟩)
  | unknown =>
    rw [hv] at hh
    exact hh q (List.mem_singleton_self _)
termination_by ‖q‖°
decreasing_by exact e.decreasing hc

theorem search_longest {e : Expander} {d : Decider} {t : Nat} {c : Program} (q : Program) :
    (search e d q).longest = some (t, c) → c ⇓ t ∧ ‖c‖ = ‖q‖ := by
  intro h
  rw [search] at h
  cases hv : d q with
  | halts s hq =>
    rw [hv] at h
    cases h
    exact ⟨hq, rfl⟩
  | diverges _ => rw [hv] at h; exact nomatch h
  | stuck i =>
    rw [hv] at h
    obtain ⟨o, ho, h'⟩ := Outcome.longest_concat h
    obtain ⟨⟨c', hc'⟩, _, rfl⟩ := List.mem_map.mp ho
    obtain ⟨ht, hs⟩ := search_longest (e := e) (d := d) c' h'
    exact ⟨ht, hs.trans (e.size hc')⟩
  | unknown => rw [hv] at h; exact nomatch h
termination_by ‖q‖°
decreasing_by exact e.decreasing hc'

namespace Program

/-- Fill every gap with moves to the left, leaving a program with no gaps. -/
def fill : Program → Program
  | ε         => ε
  | .left p   => .left p.fill
  | .right p  => .right p.fill
  | .flip p   => .flip p.fill
  | .loop b p => .loop b.fill p.fill
  | .gap k _ p => rep .left k ε ++ p.fill

theorem fill_refines : ∀ p : Program, p.fill ⊑ p
  | ε         => .nil
  | .left p   => .left (fill_refines p)
  | .right p  => .right (fill_refines p)
  | .flip p   => .flip (fill_refines p)
  | .loop b p => .loop (fill_refines b) (fill_refines p)
  | .gap k _ p => .gap (by rw [size_rep .left (fun _ => rfl)]; rfl) (fill_refines p)

theorem closed_fill : ∀ p : Program, p.fill°
  | ε         => trivial
  | .left p   => closed_fill p
  | .right p  => closed_fill p
  | .flip p   => closed_fill p
  | .loop b p => ⟨closed_fill b, closed_fill p⟩
  | .gap _ _ p => closed_append (closed_rep .left (fun _ h => h) trivial) (closed_fill p)

end Program

/-- A search from `n?` that settles every program and finds `B` as its longest halt
proves that `BB(n) = B`. -/
theorem IsBB.of_search (e : Expander) (d : Decider) {n B : Nat} :
    (search e d (ω n)).value? = some B → IsBB n B := by
  intro h
  simp only [Outcome.value?] at h
  split at h
  · next hh =>
    obtain ⟨⟨t, c⟩, hl, rfl⟩ := Option.map_eq_some_iff.mp h
    have hb : Bounded t (ω n) :=
      search_bounded _ (fun r hr => by rw [List.isEmpty_iff.mp hh] at hr; exact nomatch hr)
        (fun x hx => by rw [hl] at hx; cases hx; exact Nat.le_refl _)
    obtain ⟨ht, hs⟩ := search_longest _ hl
    exact ⟨fun ⟨p, hp, hsz⟩ k hk => hb.upper p k hp hsz hk,
      ⟨⟨c.fill, c.closed_fill, by rw [(c.fill_refines).size, hs, Program.size_gap?]⟩,
        c.fill_refines.haltsIn ht⟩⟩
  · exact nomatch h

end BBBTape
