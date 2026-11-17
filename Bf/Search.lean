import Bf.BB
import Bf.Fill
import Bf.Decider

namespace Bf

inductive Outcome where
  | halted (steps : Nat)
  | stuck (id : Nat)
  | timeout

def Config.stop (c : Config) : Outcome :=
  match c.prog with
  | .hole i _ => .stuck i
  | _         => .halted 0

def Config.run : Nat → Config → Outcome
  | 0, c => match c.step with
    | some _ => .timeout
    | none   => c.stop
  | f + 1, c => match c.step with
    | none    => c.stop
    | some c' => match run f c' with
      | .halted t => .halted (t + 1)
      | o         => o

theorem Config.stop_halted {c : Config} {k : Nat} (hs : c.step = none) (h : c.stop = .halted k) :
    k = 0 ∧ c.prog = .nil := by
  obtain ⟨t, p⟩ := c
  cases p with
  | nil => simp only [stop] at h; cases h; exact ⟨rfl, rfl⟩
  | hole => simp [stop] at h
  | left | right | flip | loop => cases hs

theorem Config.run_halted {f : Nat} {c : Config} {k : Nat} (h : c.run f = .halted k) :
    ∃ t : Tape, c.steps k = some ⟨t, .nil⟩ := by
  induction f generalizing c k with
  | zero =>
    unfold run at h
    cases hs : c.step with
    | some c' => simp [hs] at h
    | none =>
      simp only [hs] at h
      obtain ⟨rfl, hp⟩ := stop_halted hs h
      exact ⟨c.tape, by rw [← hp]; rfl⟩
  | succ f ih =>
    unfold run at h
    cases hs : c.step with
    | none =>
      simp only [hs] at h
      obtain ⟨rfl, hp⟩ := stop_halted hs h
      exact ⟨c.tape, by rw [← hp]; rfl⟩
    | some c' =>
      simp only [hs] at h
      cases hr : run f c' with
      | halted j =>
        rw [hr] at h
        cases h
        obtain ⟨t, ht⟩ := ih hr
        exact ⟨t, by simp [steps, hs, ht]⟩
      | stuck i => rw [hr] at h; cases h
      | timeout => rw [hr] at h; cases h

namespace Program

def shapes (i fresh k : Nat) : List Program :=
  if k = 0 then [nil]
  else [left (hole i (k - 1)), right (hole i (k - 1)), flip (hole i (k - 1))] ++
    (List.range (k - 1)).map fun (a : Nat) => loop (hole fresh a) (hole i (k - 2 - a))

theorem shapes_cover (i fresh : Nat) {k : Nat} {p : Program} (hc : p.Closed) (hs : p.size = k) :
    ∃ c ∈ shapes i fresh k, Fills c p := by
  cases p with
  | nil => exact ⟨nil, by simp [shapes, ← hs, size], .nil⟩
  | hole => exact absurd hc id
  | left p =>
    refine ⟨left (hole i (k - 1)), ?_, .left (.hole i hc ?_)⟩ <;> simp [shapes, ← hs, size]
  | right p =>
    refine ⟨right (hole i (k - 1)), ?_, .right (.hole i hc ?_)⟩ <;> simp [shapes, ← hs, size]
  | flip p =>
    refine ⟨flip (hole i (k - 1)), ?_, .flip (.hole i hc ?_)⟩ <;> simp [shapes, ← hs, size]
  | loop b p =>
    refine ⟨loop (hole fresh b.size) (hole i (k - 2 - b.size)), ?_,
      .loop (.hole fresh hc.1 rfl) (.hole i hc.2 ?_)⟩
    · simp only [shapes, ← hs, size]
      simp only [show ¬ (b.size + p.size + 2 = 0) by omega, ↓reduceIte]
      exact List.mem_append_right _ (List.mem_map.mpr ⟨b.size, List.mem_range.mpr (by omega), rfl⟩)
    · simp only [← hs, size]; omega

def expand (i fresh : Nat) : Program → Option (List Program)
  | nil      => none
  | left p   => (expand i fresh p).map fun (cs : List Program) => cs.map left
  | right p  => (expand i fresh p).map fun (cs : List Program) => cs.map right
  | flip p   => (expand i fresh p).map fun (cs : List Program) => cs.map flip
  | loop b p => match expand i fresh b with
    | some cs => some (cs.map fun (c : Program) => loop c p)
    | none    => (expand i fresh p).map fun (cs : List Program) => cs.map (loop b)
  | hole j k => if j = i then some (shapes i fresh k) else none

theorem expand_cover {i fresh : Nat} {q p : Program} {cs : List Program}
    (he : expand i fresh q = some cs) (h : Fills q p) : ∃ c ∈ cs, Fills c p := by
  induction h generalizing cs with
  | nil => cases he
  | left _ ih =>
    simp only [expand, Option.map_eq_some_iff] at he
    obtain ⟨ds, hd, rfl⟩ := he
    obtain ⟨c, hc, hf⟩ := ih hd
    exact ⟨_, List.mem_map.mpr ⟨c, hc, rfl⟩, .left hf⟩
  | right _ ih =>
    simp only [expand, Option.map_eq_some_iff] at he
    obtain ⟨ds, hd, rfl⟩ := he
    obtain ⟨c, hc, hf⟩ := ih hd
    exact ⟨_, List.mem_map.mpr ⟨c, hc, rfl⟩, .right hf⟩
  | flip _ ih =>
    simp only [expand, Option.map_eq_some_iff] at he
    obtain ⟨ds, hd, rfl⟩ := he
    obtain ⟨c, hc, hf⟩ := ih hd
    exact ⟨_, List.mem_map.mpr ⟨c, hc, rfl⟩, .flip hf⟩
  | @loop b b' q p hb hq ihb ih =>
    simp only [expand] at he
    cases hx : expand i fresh b with
    | some ds =>
      rw [hx] at he
      cases he
      obtain ⟨c, hc, hf⟩ := ihb hx
      exact ⟨_, List.mem_map.mpr ⟨c, hc, rfl⟩, .loop hf hq⟩
    | none =>
      rw [hx] at he
      simp only [Option.map_eq_some_iff] at he
      obtain ⟨ds, hd, rfl⟩ := he
      obtain ⟨c, hc, hf⟩ := ih hd
      exact ⟨_, List.mem_map.mpr ⟨c, hc, rfl⟩, .loop hb hf⟩
  | hole j hc hs =>
    simp only [expand] at he
    split at he
    · cases he; exact shapes_cover i fresh hc hs
    · cases he

end Program

structure Brancher where
  P      : Program → Prop
  expand : Nat → Nat → Program → Option (List Program)
  cover  : ∀ {i fresh : Nat} {q p : Program} {cs : List Program},
    expand i fresh q = some cs → q.Fills p → P p → ∃ c ∈ cs, c.Fills p
  norm   : ∀ p : Program, p.Closed →
    ∃ p' : Program, P p' ∧ p'.Closed ∧ p'.size = p.size ∧ p.SameTime p'

def Brancher.naive : Brancher where
  P := fun (_ : Program) => True
  expand := fun (i fresh : Nat) (q : Program) => q.expand i fresh
  cover := fun {i fresh : Nat} {q p : Program} {cs : List Program}
    (he : q.expand i fresh = some cs) (h : q.Fills p) (_ : True) => Program.expand_cover he h
  norm := fun (p : Program) (hc : p.Closed) => ⟨p, trivial, hc, rfl, .refl p⟩

def omax (best : Option Nat) (t : Nat) : Option Nat :=
  match best with
  | none   => some t
  | some b => some (max b t)

def search (B : Brancher) (d : Decider) (limit n : Nat) : Nat → List (Program × Nat) → Option Nat → Option (Option Nat)
  | _, [], best => some best
  | 0, _ :: _, _ => none
  | f + 1, (q, fresh) :: rest, best =>
    match q.init.run limit with
    | .halted t => if q.size = n then search B d limit n f rest (omax best t) else none
    | .stuck i => match B.expand i fresh q with
      | some cs => search B d limit n f (cs.map (fun (c : Program) => (c, fresh + 1)) ++ rest) best
      | none    => none
    | .timeout => match d.run q with
      | .nonhalts => search B d limit n f rest best
      | _         => none

def Bound (best : Option Nat) (p : Program) : Prop :=
  ∀ k : Nat, p.init.HaltsIn k → ∃ b : Nat, best = some b ∧ k ≤ b

theorem Bound.omax {best : Option Nat} {p : Program} (h : Bound best p) (t : Nat) :
    Bound (omax best t) p := by
  intro k hk
  obtain ⟨b, rfl, hb⟩ := h k hk
  exact ⟨max b t, rfl, by omega⟩

theorem search_bound {B : Brancher} {d : Decider} {limit n f : Nat} {stack : List (Program × Nat)}
    {best r : Option Nat} (h : search B d limit n f stack best = some r) (p : Program) (hP : B.P p)
    (hp : (∃ x ∈ stack, x.1.Fills p) ∨ Bound best p) : Bound r p := by
  induction f generalizing stack best with
  | zero =>
    cases stack with
    | nil =>
      simp only [search] at h; cases h
      rcases hp with ⟨x, hx, _⟩ | hp
      · cases hx
      · exact hp
    | cons x rest => simp [search] at h
  | succ f ih =>
    cases stack with
    | nil =>
      simp only [search] at h; cases h
      rcases hp with ⟨x, hx, _⟩ | hp
      · cases hx
      · exact hp
    | cons x rest =>
      obtain ⟨q, fresh⟩ := x
      simp only [search] at h
      cases hrun : q.init.run limit with
      | halted t =>
        rw [hrun] at h
        simp only at h
        split at h
        · refine ih h ?_
          rcases hp with ⟨x, hx, hf⟩ | hp
          · rcases List.mem_cons.mp hx with rfl | hx
            · obtain ⟨u, hu⟩ := Config.run_halted hrun
              have hh := hf.refines.haltsIn hu
              refine .inr fun (k : Nat) (hk : p.init.HaltsIn k) => ?_
              rw [hk.unique hh]
              cases best with
              | none => exact ⟨t, rfl, Nat.le_refl t⟩
              | some b => exact ⟨max b t, rfl, by omega⟩
            · exact .inl ⟨x, hx, hf⟩
          · exact .inr (hp.omax t)
        · cases h
      | stuck i =>
        rw [hrun] at h
        simp only at h
        cases he : B.expand i fresh q with
        | none => rw [he] at h; cases h
        | some cs =>
          rw [he] at h
          refine ih h ?_
          rcases hp with ⟨x, hx, hf⟩ | hp
          · rcases List.mem_cons.mp hx with rfl | hx
            · obtain ⟨c, hc, hcf⟩ := B.cover he hf hP
              exact .inl ⟨(c, fresh + 1), List.mem_append_left _ (List.mem_map.mpr ⟨c, hc, rfl⟩), hcf⟩
            · exact .inl ⟨x, List.mem_append_right _ hx, hf⟩
          · exact .inr hp
      | timeout =>
        rw [hrun] at h
        simp only at h
        have hsound := d.sound q
        cases hv : d.run q with
        | halts j => rw [hv] at h; cases h
        | unknown => rw [hv] at h; cases h
        | nonhalts =>
          rw [hv] at h hsound
          refine ih h ?_
          rcases hp with ⟨x, hx, hf⟩ | hp
          · rcases List.mem_cons.mp hx with rfl | hx
            · exact .inr fun (k : Nat) (hk : p.init.HaltsIn k) =>
                absurd ⟨k, hk⟩ (hf.refines.not_halts hsound)
            · exact .inl ⟨x, hx, hf⟩
          · exact .inr hp

theorem search_reach {B : Brancher} {d : Decider} {limit n f : Nat} {stack : List (Program × Nat)}
    {best r : Option Nat} (h : search B d limit n f stack best = some r)
    (hb : ∀ b : Nat, best = some b → Reachable n b) (s : Nat) (hr : r = some s) : Reachable n s := by
  induction f generalizing stack best with
  | zero =>
    cases stack with
    | nil => simp only [search] at h; cases h; exact hb s hr
    | cons x rest => simp [search] at h
  | succ f ih =>
    cases stack with
    | nil => simp only [search] at h; cases h; exact hb s hr
    | cons x rest =>
      obtain ⟨q, fresh⟩ := x
      simp only [search] at h
      cases hrun : q.init.run limit with
      | halted t =>
        rw [hrun] at h
        simp only at h
        split at h
        · next hsize =>
          refine ih h fun (b : Nat) (hbe : omax best t = some b) => ?_
          obtain ⟨u, hu⟩ := Config.run_halted hrun
          have ht : Reachable n t :=
            ⟨q.fill, q.fills_fill.closed, by rw [q.fills_fill.size, hsize], q.fills_fill.refines.haltsIn hu⟩
          cases best with
          | none => simp only [omax] at hbe; cases hbe; exact ht
          | some b₀ =>
            simp only [omax] at hbe; cases hbe
            rcases Nat.le_total b₀ t with hle | hle
            · rw [Nat.max_eq_right hle]; exact ht
            · rw [Nat.max_eq_left hle]; exact hb b₀ rfl
        · cases h
      | stuck i =>
        rw [hrun] at h
        simp only at h
        cases he : B.expand i fresh q with
        | none => rw [he] at h; cases h
        | some cs => rw [he] at h; exact ih h hb
      | timeout =>
        rw [hrun] at h
        simp only at h
        cases hv : d.run q with
        | halts j => rw [hv] at h; cases h
        | unknown => rw [hv] at h; cases h
        | nonhalts => rw [hv] at h; exact ih h hb

end Bf
