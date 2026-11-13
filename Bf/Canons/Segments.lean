import Bf.Canon
import Bf.Simulation
import Bf.Canons.Seg

namespace Bf

namespace Seg

def eff (s : Seg) : Int × List Bool := (disp s, window (par s) s.length)

theorem apply_eq_of_eff {s s' : Seg} (hl : s.length = s'.length) (he : eff s = eff s')
    (t : Tape) : apply s t = apply s' t := by
  obtain ⟨hd, hw⟩ := Prod.mk.inj he
  rw [hl] at hw
  have hpar : ∀ j : Int, par s j = par s' j := by
    intro j
    by_cases hj : -(s'.length : Int) ≤ j ∧ j ≤ s'.length
    · exact eq_of_window hw j hj
    · rw [par_eq_false s j (by omega), par_eq_false s' j (by omega)]
  ext i
  rw [cells_apply, cells_apply, hd, hpar]

def canon (s : Seg) : Seg :=
  let w : Seg := greedy (disp s) s.length 0 (support (par s) s.length)
  if w.length = s.length ∧ eff w = eff s then w else s

theorem length_canon (s : Seg) : (canon s).length = s.length := by
  unfold canon; dsimp only; split
  · next h => exact h.1
  · rfl

theorem apply_canon (s : Seg) (t : Tape) : apply (canon s) t = apply s t := by
  unfold canon; dsimp only; split
  · next h => exact apply_eq_of_eff h.1 h.2 t
  · rfl

end Seg

namespace Program

def canonSegs : Seg → Program → Program
  | acc, nil      => Seg.prepend (Seg.canon acc.reverse) nil
  | acc, left p   => canonSegs (.left :: acc) p
  | acc, right p  => canonSegs (.right :: acc) p
  | acc, flip p   => canonSegs (.flip :: acc) p
  | acc, loop b p => Seg.prepend (Seg.canon acc.reverse) (loop (canonSegs [] b) (canonSegs [] p))

theorem size_canonSegs (p : Program) (acc : Seg) :
    (canonSegs acc p).size = acc.length + p.size := by
  induction p generalizing acc with
  | nil => simp [canonSegs, Seg.size_prepend, Seg.length_canon, size]
  | left p ih | right p ih | flip p ih =>
    simp only [canonSegs, ih, List.length_cons, size]; omega
  | loop b p ihb ih =>
    simp only [canonSegs, Seg.size_prepend, Seg.length_canon, List.length_reverse, size, ihb, ih,
      List.length_nil]
    omega

inductive SegRel : Program → Program → Prop
  | nil : SegRel nil nil
  | seg {s s' : Seg} {p q : Program} :
      s.length = s'.length → (∀ t : Tape, Seg.apply s t = Seg.apply s' t) → SegRel p q →
      SegRel (Seg.prepend s p) (Seg.prepend s' q)
  | loop {b b' p q : Program} : SegRel b b' → SegRel p q → SegRel (loop b p) (loop b' q)

theorem SegRel.append {b b' x x' : Program} (hb : SegRel b b') (hx : SegRel x x') :
    SegRel (b ++ x) (b' ++ x') := by
  induction hb with
  | nil => exact hx
  | seg hl ha _ ih => rw [Seg.prepend_append, Seg.prepend_append]; exact .seg hl ha ih
  | loop hb₁ _ _ ih => exact .loop hb₁ ih

theorem SegRel.canon (s : Seg) {p q : Program} (h : SegRel p q) :
    SegRel (Seg.prepend s p) (Seg.prepend (Seg.canon s) q) :=
  .seg (Seg.length_canon s).symm (fun (t : Tape) => (Seg.apply_canon s t).symm) h

theorem segRel_canonSegs (p : Program) (acc : Seg) :
    SegRel (Seg.prepend acc.reverse p) (canonSegs acc p) := by
  induction p generalizing acc with
  | nil => exact .canon _ .nil
  | left p ih => simpa [Seg.prepend, Cmd.prepend, canonSegs] using ih (.left :: acc)
  | right p ih => simpa [Seg.prepend, Cmd.prepend, canonSegs] using ih (.right :: acc)
  | flip p ih => simpa [Seg.prepend, Cmd.prepend, canonSegs] using ih (.flip :: acc)
  | loop b p ihb ih => exact .canon _ (.loop (ihb []) (ih []))

def SegConf (c d : Config) : Prop := c.tape = d.tape ∧ SegRel c.prog d.prog

theorem SegConf.sim : Config.Simulation SegConf := by
  rintro ⟨t, p⟩ ⟨_, q⟩ ⟨rfl, hr⟩
  dsimp only at hr
  induction hr with
  | nil => exact .inl ⟨rfl, rfl⟩
  | @seg s s' p q hl ha hr ih =>
    cases s with
    | nil =>
      obtain rfl : s' = [] := List.length_eq_zero_iff.mp hl.symm
      exact ih
    | cons c s =>
      have h₁ := Seg.steps_prepend (c :: s) t p
      have h₂ := Seg.steps_prepend s' t q
      rw [← hl] at h₂
      exact .inr ⟨s.length + 1, _, _, by omega, h₁, h₂, ha t, hr⟩
  | @loop b b' p q hb hp _ _ =>
    refine .inr ⟨1, _, _, by omega, rfl, rfl, rfl, ?_⟩
    cases hh : t.head
    · simpa [hh] using hp
    · simpa [hh] using hb.append (.loop hb hp)

end Program

def Canon.segments : Canon where
  f := Program.canonSegs []
  size_eq := fun (p : Program) => by simpa using Program.size_canonSegs p []
  sound := fun (p : Program) => Program.SegConf.sim.sameTime ⟨rfl, Program.segRel_canonSegs p []⟩

end Bf
