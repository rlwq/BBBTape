import Bf.Simulation
import Bf.Seg

namespace Bf

namespace Program

def canonSegs : Seg → Program → Program
  | acc, nil      => Seg.prepend (Seg.canon acc.reverse) nil
  | acc, left p   => canonSegs (.left :: acc) p
  | acc, right p  => canonSegs (.right :: acc) p
  | acc, flip p   => canonSegs (.flip :: acc) p
  | acc, loop b p => Seg.prepend (Seg.canon acc.reverse) (loop (canonSegs [] b) (canonSegs [] p))
  | acc, hole i k => Seg.prepend (Seg.canon acc.reverse) (hole i k)

theorem size_canonSegs (p : Program) (acc : Seg) :
    (canonSegs acc p).size = acc.length + p.size := by
  induction p generalizing acc with
  | nil => simp [canonSegs, Seg.size_prepend, Seg.length_canon, size]
  | hole => simp [canonSegs, Seg.size_prepend, Seg.length_canon, size]
  | left p ih | right p ih | flip p ih =>
    simp only [canonSegs, ih, List.length_cons, size]; omega
  | loop b p ihb ih =>
    simp only [canonSegs, Seg.size_prepend, Seg.length_canon, List.length_reverse, size, ihb, ih,
      List.length_nil]
    omega

inductive SegRel : Program → Program → Prop
  | nil : SegRel nil nil
  | hole (i k : Nat) : SegRel (hole i k) (hole i k)
  | seg {s s' : Seg} {p q : Program} :
      s.length = s'.length → (∀ t : Tape, Seg.apply s t = Seg.apply s' t) → SegRel p q →
      SegRel (Seg.prepend s p) (Seg.prepend s' q)
  | loop {b b' p q : Program} : SegRel b b' → SegRel p q → SegRel (loop b p) (loop b' q)

theorem SegRel.append {b b' x x' : Program} (hb : SegRel b b') (hx : SegRel x x') :
    SegRel (b ++ x) (b' ++ x') := by
  induction hb with
  | nil => exact hx
  | hole i k => exact .hole i k
  | seg hl ha _ ih => rw [Seg.prepend_append, Seg.prepend_append]; exact .seg hl ha ih
  | loop hb₁ _ _ ih => exact .loop hb₁ ih

theorem SegRel.canon (s : Seg) {p q : Program} (h : SegRel p q) :
    SegRel (Seg.prepend s p) (Seg.prepend (Seg.canon s) q) :=
  .seg (Seg.length_canon s).symm (fun (t : Tape) => (Seg.apply_canon s t).symm) h

theorem segRel_canonSegs (p : Program) (acc : Seg) :
    SegRel (Seg.prepend acc.reverse p) (canonSegs acc p) := by
  induction p generalizing acc with
  | nil => exact .canon _ .nil
  | hole i k => exact .canon _ (.hole i k)
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
  | hole => exact .inl ⟨rfl, rfl⟩
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

def canonLast (p : Program) : Program :=
  if p.loopFree then stars p.size
  else match p with
    | nil      => nil
    | left q   => left (canonLast q)
    | right q  => right (canonLast q)
    | flip q   => flip (canonLast q)
    | loop b q => loop b (canonLast q)
    | hole i k => hole i k

theorem size_canonLast (p : Program) : (canonLast p).size = p.size := by
  induction p with
  | nil => rfl
  | hole => rfl
  | left q ih | right q ih | flip q ih | loop _ q _ ih =>
    unfold canonLast; split
    · simp
    · simp [size, ih]

inductive LastRel : Program → Program → Prop
  | tail {p q : Program} : p.loopFree = true → q.loopFree = true → p.size = q.size → LastRel p q
  | hole (i k : Nat) : LastRel (hole i k) (hole i k)
  | left {p q : Program} : LastRel p q → LastRel (left p) (left q)
  | right {p q : Program} : LastRel p q → LastRel (right p) (right q)
  | flip {p q : Program} : LastRel p q → LastRel (flip p) (flip q)
  | loop {b p q : Program} : LastRel p q → LastRel (loop b p) (loop b q)

theorem LastRel.prefix (b : Program) {x y : Program} (h : LastRel x y) :
    LastRel (b ++ x) (b ++ y) := by
  induction b with
  | nil => exact h
  | hole i k => exact .hole i k
  | left _ ih => exact .left ih
  | right _ ih => exact .right ih
  | flip _ ih => exact .flip ih
  | loop _ _ _ ih => exact .loop ih

theorem lastRel_canonLast (p : Program) : LastRel p (canonLast p) := by
  induction p with
  | nil => exact .tail rfl rfl rfl
  | hole i k => exact .hole i k
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
  | hole => exact .inl ⟨rfl, rfl⟩
  | left h => exact .inr ⟨1, _, _, by omega, rfl, rfl, .inr ⟨rfl, h⟩⟩
  | right h => exact .inr ⟨1, _, _, by omega, rfl, rfl, .inr ⟨rfl, h⟩⟩
  | flip h => exact .inr ⟨1, _, _, by omega, rfl, rfl, .inr ⟨rfl, h⟩⟩
  | @loop b p q h =>
    refine .inr ⟨1, _, _, by omega, rfl, rfl, .inr ⟨rfl, ?_⟩⟩
    cases hh : t.head
    · simpa [hh] using h
    · simpa [hh] using LastRel.prefix b (.loop h)

theorem closed_prepend (s : Seg) (x : Program) : (Seg.prepend s x).Closed ↔ x.Closed := by
  induction s with
  | nil => exact Iff.rfl
  | cons c s ih => cases c <;> exact ih

theorem closed_canonSegs {p : Program} (h : p.Closed) (acc : Seg) : (canonSegs acc p).Closed := by
  induction p generalizing acc with
  | nil => exact (closed_prepend _ _).mpr trivial
  | hole => exact absurd h id
  | left p ih | right p ih | flip p ih => exact ih h _
  | loop b p ihb ih => exact (closed_prepend _ _).mpr ⟨ihb h.1 [], ih h.2 []⟩

theorem closed_canonLast {p : Program} (h : p.Closed) : (canonLast p).Closed := by
  induction p with
  | nil => trivial
  | hole => exact absurd h id
  | left q ih | right q ih | flip q ih =>
    unfold canonLast; split
    · exact closed_stars _
    · exact ih h
  | loop b q _ ih =>
    unfold canonLast; split
    · exact closed_stars _
    · exact ⟨h.1, ih h.2⟩

def Normal (top : Bool) : Seg → Program → Prop
  | acc, nil      => match top with
    | true  => ∀ c ∈ acc, c = Cmd.flip
    | false => acc.reverse ∈ Seg.mids acc.length
  | acc, left p   => Normal top (.left :: acc) p
  | acc, right p  => Normal top (.right :: acc) p
  | acc, flip p   => Normal top (.flip :: acc) p
  | acc, loop b p => acc.reverse ∈ Seg.mids acc.length ∧ Normal false [] b ∧ Normal top [] p
  | _,   hole _ _ => False

theorem normal_prepend (top : Bool) (s acc : Seg) (x : Program) :
    Normal top acc (Seg.prepend s x) ↔ Normal top (s.reverse ++ acc) x := by
  induction s generalizing acc with
  | nil => exact Iff.rfl
  | cons c s ih =>
    have h : (c :: s).reverse ++ acc = s.reverse ++ c :: acc := by simp
    rw [h]
    cases c <;> exact ih _

theorem normal_canonSegs {p : Program} (h : p.Closed) (acc : Seg) :
    Normal false [] (canonSegs acc p) := by
  have hm : ∀ r : Seg, ((Seg.canon r).reverse ++ []).reverse ∈ Seg.mids ((Seg.canon r).reverse ++ []).length := by
    intro r
    simp only [List.append_nil, List.reverse_reverse, List.length_reverse, Seg.length_canon]
    exact Seg.canon_mem_mids r
  induction p generalizing acc with
  | nil => exact (normal_prepend _ _ _ _).mpr (hm _)
  | hole => exact absurd h id
  | left p ih | right p ih | flip p ih => exact ih h _
  | loop b p ihb ih => exact (normal_prepend _ _ _ _).mpr ⟨hm _, ihb h.1 [], ih h.2 []⟩

theorem normal_stars {acc : Seg} (h : ∀ c ∈ acc, c = Cmd.flip) (k : Nat) : Normal true acc (stars k) := by
  induction k generalizing acc with
  | zero => exact h
  | succ k ih =>
    refine ih (acc := .flip :: acc) fun (c : Cmd) (hc : c ∈ Cmd.flip :: acc) => ?_
    rcases List.mem_cons.mp hc with rfl | hc
    · rfl
    · exact h c hc

theorem normal_canonLast {p : Program} (acc : Seg) (ha : acc = [] ∨ p.loopFree = false)
    (h : Normal false acc p) : Normal true acc (canonLast p) := by
  induction p generalizing acc with
  | nil =>
    rcases ha with rfl | ha
    · exact fun (c : Cmd) (hc : c ∈ []) => by cases hc
    · cases ha
  | hole => exact h
  | left q ih =>
    unfold canonLast; split
    · next hl =>
      rcases ha with rfl | ha
      · exact normal_stars (fun (c : Cmd) (hc : c ∈ []) => by cases hc) _
      · rw [hl] at ha; cases ha
    · next hl => exact ih _ (.inr (by simpa [loopFree] using hl)) h
  | right q ih =>
    unfold canonLast; split
    · next hl =>
      rcases ha with rfl | ha
      · exact normal_stars (fun (c : Cmd) (hc : c ∈ []) => by cases hc) _
      · rw [hl] at ha; cases ha
    · next hl => exact ih _ (.inr (by simpa [loopFree] using hl)) h
  | flip q ih =>
    unfold canonLast; split
    · next hl =>
      rcases ha with rfl | ha
      · exact normal_stars (fun (c : Cmd) (hc : c ∈ []) => by cases hc) _
      · rw [hl] at ha; cases ha
    · next hl => exact ih _ (.inr (by simpa [loopFree] using hl)) h
  | loop b q _ ih =>
    unfold canonLast; split
    · next hl => cases hl
    · exact ⟨h.1, h.2.1, ih [] (.inl rfl) h.2.2⟩

def norm (p : Program) : Program := canonLast (canonSegs [] p)

theorem sameTime_norm (p : Program) : p.SameTime (norm p) := by
  have h₁ : p.SameTime (canonSegs [] p) :=
    SegConf.sim.sameTime (p := p) (q := canonSegs [] p) ⟨rfl, segRel_canonSegs p []⟩
  have h₂ : (canonSegs [] p).SameTime (canonLast (canonSegs [] p)) :=
    LastConf.sim.sameTime (p := canonSegs [] p) (q := canonLast (canonSegs [] p))
      (.inr ⟨rfl, lastRel_canonLast _⟩)
  exact h₁.trans h₂

theorem norm_spec {p : Program} (h : p.Closed) :
    Normal true [] (norm p) ∧ (norm p).Closed ∧ (norm p).size = p.size ∧ p.SameTime (norm p) :=
  ⟨normal_canonLast [] (.inl rfl) (normal_canonSegs h []), closed_canonLast (closed_canonSegs h []),
    by simp [norm, size_canonLast, size_canonSegs], sameTime_norm p⟩

end Program

end Bf
