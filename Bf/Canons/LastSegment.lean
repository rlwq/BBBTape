import Bf.Canon
import Bf.Simulation

namespace Bf

namespace Program

def canonLast (p : Program) : Program :=
  if p.loopFree then stars p.size
  else match p with
    | nil      => nil
    | left q   => left (canonLast q)
    | right q  => right (canonLast q)
    | flip q   => flip (canonLast q)
    | loop b q => loop b (canonLast q)

theorem size_canonLast (p : Program) : (canonLast p).size = p.size := by
  induction p with
  | nil => rfl
  | left q ih | right q ih | flip q ih | loop _ q _ ih =>
    unfold canonLast; split
    · simp
    · simp [size, ih]

inductive LastRel : Program → Program → Prop
  | tail {p q : Program} : p.loopFree = true → q.loopFree = true → p.size = q.size → LastRel p q
  | left {p q : Program} : LastRel p q → LastRel (left p) (left q)
  | right {p q : Program} : LastRel p q → LastRel (right p) (right q)
  | flip {p q : Program} : LastRel p q → LastRel (flip p) (flip q)
  | loop {b p q : Program} : LastRel p q → LastRel (loop b p) (loop b q)

theorem LastRel.prefix (b : Program) {x y : Program} (h : LastRel x y) :
    LastRel (b ++ x) (b ++ y) := by
  induction b with
  | nil => exact h
  | left _ ih => exact .left ih
  | right _ ih => exact .right ih
  | flip _ ih => exact .flip ih
  | loop _ _ _ ih => exact .loop ih

theorem lastRel_canonLast (p : Program) : LastRel p (canonLast p) := by
  induction p with
  | nil => exact .tail rfl rfl rfl
  | left q ih | right q ih | flip q ih | loop _ q _ ih =>
    unfold canonLast; split
    · next h => exact .tail h (loopFree_stars _) (size_stars _).symm
    · first | exact .left ih | exact .right ih | exact .flip ih | exact .loop ih

def LastConf (c d : Config) : Prop :=
  (c.step = none ∧ d.step = none) ∨ (c.tape = d.tape ∧ LastRel c.prog d.prog)

theorem LastConf.sim : Config.Simulation LastConf := by
  rintro c d (h | ⟨ht, hr⟩)
  · exact .inl h
  obtain ⟨t, p⟩ := c
  obtain ⟨_, q⟩ := d
  dsimp only at ht hr
  subst ht
  cases hr with
  | @tail p q hp hq hs =>
    obtain ⟨c', h₁, h₁'⟩ := haltsIn_size_of_loopFree hp t
    obtain ⟨d', h₂, h₂'⟩ := haltsIn_size_of_loopFree hq t
    rw [← hs] at h₂
    cases hk : p.size with
    | zero =>
      rw [hk] at h₁ h₂
      cases h₁; cases h₂
      exact .inl ⟨h₁', h₂'⟩
    | succ k =>
      rw [hk] at h₁ h₂
      exact .inr ⟨k + 1, c', d', by omega, h₁, h₂, .inl ⟨h₁', h₂'⟩⟩
  | left h => exact .inr ⟨1, _, _, by omega, rfl, rfl, .inr ⟨rfl, h⟩⟩
  | right h => exact .inr ⟨1, _, _, by omega, rfl, rfl, .inr ⟨rfl, h⟩⟩
  | flip h => exact .inr ⟨1, _, _, by omega, rfl, rfl, .inr ⟨rfl, h⟩⟩
  | @loop b p q h =>
    refine .inr ⟨1, _, _, by omega, rfl, rfl, .inr ⟨rfl, ?_⟩⟩
    cases hh : t.head
    · simpa [hh] using h
    · simpa [hh] using LastRel.prefix b (.loop h)

end Program

def Canon.lastSeg : Canon where
  f := Program.canonLast
  size_eq := Program.size_canonLast
  sound := fun (p : Program) => Program.LastConf.sim.sameTime
    (.inr ⟨rfl, Program.lastRel_canonLast p⟩)

end Bf
