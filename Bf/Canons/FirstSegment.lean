import Bf.Canon
import Bf.Simulation
import Bf.Canons.Seg

namespace Bf

namespace Seg

def relEff (s : Seg) : List Bool :=
  window (fun (i : Int) => par s (i + disp s)) (2 * s.length)

theorem apply_blank_eq {s s' : Seg} (hl : s.length = s'.length) (he : relEff s = relEff s') :
    apply s .blank = apply s' .blank := by
  unfold relEff at he
  rw [hl] at he
  have b₁ := disp_bound s
  have b₂ := disp_bound s'
  have hpar : ∀ i : Int, par s (i + disp s) = par s' (i + disp s') := by
    intro i
    by_cases hi : -((2 * s'.length : Nat) : Int) ≤ i ∧ i ≤ (2 * s'.length : Nat)
    · exact eq_of_window he i hi
    · rw [par_eq_false s _ (by omega), par_eq_false s' _ (by omega)]
  ext i
  simp [cells_apply, Tape.blank, hpar]

def firstCandidates (s : Seg) : List Seg :=
  let L : Nat := s.length
  let G : List Int := support (fun (i : Int) => par s (i + disp s)) (2 * L)
  (List.range (2 * L + 1)).filterMap fun (k : Nat) =>
    let d : Int := (k : Int) - L
    let w : Seg := greedy d L 0 (G.map fun (x : Int) => x + d)
    if w.length = L ∧ relEff w = relEff s then some w else none

theorem mem_firstCandidates {s w : Seg} (h : w ∈ firstCandidates s) :
    w.length = s.length ∧ apply w .blank = apply s .blank := by
  simp only [firstCandidates, List.mem_filterMap] at h
  obtain ⟨k, -, hk⟩ := h
  split at hk
  · next hc => cases hk; exact ⟨hc.1, apply_blank_eq hc.1 hc.2⟩
  · cases hk

def least (a : Seg) (l : List Seg) : Seg :=
  l.foldl (fun (a w : Seg) => if lt w a then w else a) a

theorem least_eq_or_mem (a : Seg) (l : List Seg) : least a l = a ∨ least a l ∈ l := by
  induction l generalizing a with
  | nil => exact .inl rfl
  | cons w l ih =>
    have h := ih (if lt w a then w else a)
    simp only [least, List.foldl_cons] at h ⊢
    rcases h with h | h
    · rw [h]; split <;> simp
    · exact .inr (List.mem_cons_of_mem _ h)

def canonFirst (s : Seg) : Seg := least s (firstCandidates s)

theorem canonFirst_spec (s : Seg) :
    (canonFirst s).length = s.length ∧ apply (canonFirst s) .blank = apply s .blank := by
  unfold canonFirst
  rcases least_eq_or_mem s (firstCandidates s) with h | h
  · rw [h]; exact ⟨rfl, rfl⟩
  · exact mem_firstCandidates h

end Seg

namespace Program

def canonHead (p : Program) : Program :=
  Seg.prepend (Seg.canonFirst (splitSeg p).1) (splitSeg p).2

def canonFirstSeg : Program → Program
  | loop b p => loop b (canonFirstSeg p)
  | p        => canonHead p

theorem size_canonHead (p : Program) : (canonHead p).size = p.size := by
  conv => rhs; rw [← prepend_splitSeg p]
  rw [canonHead, Seg.size_prepend, Seg.size_prepend, (Seg.canonFirst_spec _).1]

theorem size_canonFirstSeg (p : Program) : (canonFirstSeg p).size = p.size := by
  induction p with
  | loop b q _ ih => simp [canonFirstSeg, size, ih]
  | nil | left | right | flip => exact size_canonHead _

inductive FirstRel : Program → Program → Prop
  | loop {b p q : Program} : FirstRel p q → FirstRel (loop b p) (loop b q)
  | seg {s s' : Seg} {r : Program} :
      s.length = s'.length → Seg.apply s .blank = Seg.apply s' .blank →
      FirstRel (Seg.prepend s r) (Seg.prepend s' r)

theorem firstRel_canonHead (p : Program) : FirstRel p (canonHead p) := by
  conv => lhs; rw [← prepend_splitSeg p]
  exact .seg (Seg.canonFirst_spec _).1.symm (Seg.canonFirst_spec _).2.symm

theorem firstRel_canonFirstSeg (p : Program) : FirstRel p (canonFirstSeg p) := by
  induction p with
  | loop b q _ ih => exact .loop ih
  | nil | left | right | flip => exact firstRel_canonHead _

def FirstConf (c d : Config) : Prop :=
  c = d ∨ (c.tape = .blank ∧ d.tape = .blank ∧ FirstRel c.prog d.prog)

theorem FirstConf.refl_sim (c : Config) :
    (c.step = none ∧ c.step = none) ∨
    ∃ (k : Nat) (c' d' : Config), 0 < k ∧ c.steps k = some c' ∧ c.steps k = some d' ∧
      FirstConf c' d' := by
  cases hs : c.step with
  | none => exact .inl ⟨rfl, rfl⟩
  | some c' =>
    have h : c.steps 1 = some c' := by simp [Config.steps, hs]
    exact .inr ⟨1, c', c', by omega, h, h, .inl rfl⟩

theorem FirstConf.sim : Config.Simulation FirstConf := by
  rintro c d (rfl | ⟨h₁, h₂, hr⟩)
  · exact FirstConf.refl_sim c
  obtain ⟨t, p⟩ := c
  obtain ⟨t', q⟩ := d
  dsimp only at h₁ h₂ hr
  subst h₁ h₂
  cases hr with
  | loop h => exact .inr ⟨1, _, _, by omega, rfl, rfl, .inr ⟨rfl, rfl, h⟩⟩
  | @seg s s' r hl ha =>
    cases s with
    | nil =>
      obtain rfl : s' = [] := List.length_eq_zero_iff.mp hl.symm
      exact FirstConf.refl_sim _
    | cons c s =>
      have h₁ := Seg.steps_prepend (c :: s) .blank r
      have h₂ := Seg.steps_prepend s' .blank r
      rw [← hl] at h₂
      exact .inr ⟨s.length + 1, _, _, by omega, h₁, h₂, .inl (by rw [ha])⟩

end Program

def Canon.firstSeg : Canon where
  f := Program.canonFirstSeg
  size_eq := Program.size_canonFirstSeg
  sound := fun (p : Program) => Program.FirstConf.sim.sameTime
    (.inr ⟨rfl, rfl, Program.firstRel_canonFirstSeg p⟩)

end Bf
