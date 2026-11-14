import Bf.Simulation
import Bf.Syntax
import Bf.Solved

namespace Bf.Solved.Block

def blk (lo hi : Int) : Tape := ⟨fun (i : Int) => decide (lo ≤ i ∧ i ≤ hi)⟩

theorem steps_trans {c d e : Config} {a b : Nat} (h₁ : c.steps a = some d)
    (h₂ : d.steps b = some e) : c.steps (a + b) = some e := by
  rw [Config.steps_add, h₁]; exact h₂

theorem iterate {T : Int → Int → Tape} {P : Program} {t : Nat} {dlo dhi : Int}
    {C : Int → Int → Prop}
    (h : ∀ lo hi : Int, C lo hi →
      (Config.mk (T lo hi) P).steps t = some ⟨T (lo + dlo) (hi + dhi), P⟩)
    (j : Nat) : ∀ lo hi : Int, (∀ i : Nat, i < j → C (lo + i * dlo) (hi + i * dhi)) →
      (Config.mk (T lo hi) P).steps (t * j) = some ⟨T (lo + j * dlo) (hi + j * dhi), P⟩ := by
  induction j with
  | zero => intro lo hi _; simp [Config.steps]
  | succ j ih =>
    intro lo hi hC
    have h₁ := h lo hi (by simpa using hC 0 (by omega))
    have h₂ := ih (lo + dlo) (hi + dhi) (fun (i : Nat) (hi' : i < j) => by
      have := hC (i + 1) (by omega)
      rw [show lo + dlo + i * dlo = lo + ((i + 1 : Nat) : Int) * dlo by
          push_cast; rw [Int.add_mul, Int.one_mul]; ac_rfl,
        show hi + dhi + i * dhi = hi + ((i + 1 : Nat) : Int) * dhi by
          push_cast; rw [Int.add_mul, Int.one_mul]; ac_rfl]
      exact this)
    rw [show t * (j + 1) = t + t * j by rw [Nat.mul_succ, Nat.add_comm], steps_trans h₁ h₂]
    congr 3 <;> push_cast <;> rw [Int.add_mul, Int.one_mul] <;> ac_rfl

theorem not_halts {prog P : Program} {a b j : Nat}
    (start : prog.init.steps j = some ⟨blk 0 b, P⟩)
    (pass : ∀ m : Nat, ∃ k : Nat, 0 < k ∧
      (Config.mk (blk 0 (a * m + b)) P).steps k = some ⟨blk 0 (a * (m + 1) + b), P⟩) :
    ¬ prog.init.Halts := by
  refine Config.not_halts_of_steps start ?_
  refine Config.Progress.not_halts
    (S := fun (c : Config) => ∃ m : Nat, c = ⟨blk 0 (a * m + b), P⟩) ?_ ⟨0, by simp⟩
  rintro _ ⟨m, rfl⟩
  obtain ⟨k, hk, hs⟩ := pass m
  exact ⟨k, _, hk, hs, m + 1, rfl⟩

theorem shift {T : Int → Int → Tape} {c : Config} {k : Nat} {P : Program} {lo hi lo' hi' : Int}
    (h : c.steps k = some ⟨T lo hi, P⟩) (hlo : lo = lo') (hhi : hi = hi') :
    c.steps k = some ⟨T lo' hi', P⟩ := by
  subst hlo hhi; exact h

structure Shape where
  outer : Program
  inner : Program
  tA : Nat
  tB : Nat
  tC : Nat
  tD : Nat
  gA : Nat
  e : Nat
  pos : 0 < tA
  ge : e ≤ gA + 1
  hA : ∀ h : Nat, (Config.mk (blk 0 h) outer).steps tA = some ⟨blk 0 (h + gA), inner⟩
  hB : ∀ lo hi : Int, lo ≤ 0 → 0 ≤ hi →
    (Config.mk (blk lo hi) inner).steps tB = some ⟨blk (lo - 1) (hi - 1), inner⟩
  hC : ∀ lo : Int, lo ≤ -1 →
    (Config.mk (blk lo (-1)) inner).steps tC = some ⟨blk (lo + e) 0, outer⟩
  hD : ∀ lo hi : Int, lo ≤ -1 → 0 ≤ hi →
    (Config.mk (blk lo hi) outer).steps tD = some ⟨blk (lo + 1) (hi + 1), outer⟩

theorem Shape.pass (B : Shape) (h : Nat) : ∃ k : Nat, 0 < k ∧
    (Config.mk (blk 0 h) B.outer).steps k =
      some ⟨blk 0 ((h + B.gA + 1 - B.e : Nat) : Int), B.outer⟩ := by
  have h₁ := B.hA h
  have h₂ := iterate (C := fun (lo hi : Int) => lo ≤ 0 ∧ 0 ≤ hi)
    (fun (lo hi : Int) (hc : lo ≤ 0 ∧ 0 ≤ hi) => by
      have := B.hB lo hi hc.1 hc.2
      rw [show lo - 1 = lo + -1 by omega, show hi - 1 = hi + -1 by omega] at this
      exact this) (h + B.gA + 1) 0 ((h + B.gA : Nat) : Int)
    (fun (i : Nat) (hi : i < h + B.gA + 1) => ⟨by omega, by omega⟩)
  have h₂' := shift h₂ (lo' := -((h + B.gA + 1 : Nat) : Int)) (hi' := -1) (by omega) (by omega)
  have h₃ := B.hC (-((h + B.gA + 1 : Nat) : Int)) (by omega)
  have h₄ := iterate (C := fun (lo hi : Int) => lo ≤ -1 ∧ 0 ≤ hi)
    (fun (lo hi : Int) (hc : lo ≤ -1 ∧ 0 ≤ hi) => B.hD lo hi hc.1 hc.2) (h + B.gA + 1 - B.e)
    (-((h + B.gA + 1 : Nat) : Int) + B.e) 0
    (fun (i : Nat) (hi : i < h + B.gA + 1 - B.e) => ⟨by have := B.ge; omega, by omega⟩)
  have h₄' := shift h₄ (lo' := 0) (hi' := ((h + B.gA + 1 - B.e : Nat) : Int))
    (by have := B.ge; omega) (by have := B.ge; omega)
  have h₁' := shift h₁ (lo' := 0) (hi' := ((h + B.gA : Nat) : Int)) rfl (by omega)
  exact ⟨_, by have := B.pos; omega, steps_trans (steps_trans (steps_trans h₁' h₂') h₃) h₄'⟩

theorem Shape.not_halts (B : Shape) {prog : Program} {j b : Nat}
    (start : prog.init.steps j = some ⟨blk 0 b, B.outer⟩) : ¬ prog.init.Halts := by
  refine Block.not_halts (a := B.gA + 1 - B.e) start fun (m : Nat) => ?_
  obtain ⟨k, hk, hs⟩ := B.pass ((B.gA + 1 - B.e) * m + b)
  refine ⟨k, hk, shift hs rfl ?_⟩
  have := B.ge
  have hg : (B.gA + 1 - B.e) * (m + 1) = (B.gA + 1 - B.e) * m + (B.gA + 1 - B.e) := Nat.mul_succ _ _
  rw [show ((B.gA + 1 - B.e : Nat) : Int) * ((m : Int) + 1) + (b : Int) =
    (((B.gA + 1 - B.e) * (m + 1) + b : Nat) : Int) by push_cast; rfl, hg]
  generalize (B.gA + 1 - B.e) * m = q
  omega

theorem mul_step {i J d : Nat} (hi : i < J) : i * d + d ≤ J * d := by
  have := Nat.mul_le_mul_right d (show i + 1 ≤ J by omega)
  rw [Nat.succ_mul] at this
  exact this

structure Wide where
  outer : Program
  inner : Program
  tA : Nat
  tB : Nat
  tC : Nat
  tD : Nat
  d : Nat
  dD : Nat
  gA : Nat
  r : Nat
  e : Nat
  L : Nat
  hmin : Nat
  pos : 0 < tA
  hA : ∀ h : Nat, hmin ≤ h →
    (Config.mk (blk 0 h) outer).steps tA = some ⟨blk 0 (h + gA), inner⟩
  hB : ∀ lo hi : Int, lo ≤ 0 → 0 ≤ hi →
    (Config.mk (blk lo hi) inner).steps tB = some ⟨blk (lo - d) (hi - d), inner⟩
  hC : ∀ lo : Int, lo ≤ -(L : Int) →
    (Config.mk (blk lo (-(r : Int))) inner).steps tC = some ⟨blk (lo + e) 0, outer⟩
  hD : ∀ lo hi : Int, lo ≤ -(dD : Int) → 0 ≤ hi →
    (Config.mk (blk lo hi) outer).steps tD = some ⟨blk (lo + dD) (hi + dD), outer⟩

theorem Wide.pass (W : Wide) {h J K : Nat} (hh : W.hmin ≤ h) (hr : W.r ≤ W.d)
    (hJ : J * W.d = h + W.gA + W.r) (hK : K * W.dD + W.e = h + W.gA + W.r)
    (hL : W.L ≤ h + W.gA + W.r) :
    ∃ k : Nat, 0 < k ∧
      (Config.mk (blk 0 h) W.outer).steps k = some ⟨blk 0 ((K * W.dD : Nat) : Int), W.outer⟩ := by
  have h₁ := shift (W.hA h hh) (lo' := 0) (hi' := ((h + W.gA : Nat) : Int)) rfl (by omega)
  have h₂ := iterate (C := fun (lo hi : Int) => lo ≤ 0 ∧ 0 ≤ hi)
    (fun (lo hi : Int) (hc : lo ≤ 0 ∧ 0 ≤ hi) => by
      have := W.hB lo hi hc.1 hc.2
      rw [show lo - W.d = lo + -(W.d : Int) by omega, show hi - W.d = hi + -(W.d : Int) by omega] at this
      exact this) J 0 ((h + W.gA : Nat) : Int)
    (fun (i : Nat) (hi : i < J) => by
      have hm := mul_step (d := W.d) hi
      constructor
      · rw [Int.mul_neg, ← Int.natCast_mul]; omega
      · rw [Int.mul_neg, ← Int.natCast_mul]; omega)
  have h₂' := shift h₂ (lo' := -((h + W.gA + W.r : Nat) : Int)) (hi' := -(W.r : Int))
    (by rw [Int.mul_neg, ← Int.natCast_mul]; omega) (by rw [Int.mul_neg, ← Int.natCast_mul]; omega)
  have h₃ := W.hC (-((h + W.gA + W.r : Nat) : Int)) (by omega)
  have h₄ := iterate (C := fun (lo hi : Int) => lo ≤ -(W.dD : Int) ∧ 0 ≤ hi)
    (fun (lo hi : Int) (hc : lo ≤ -(W.dD : Int) ∧ 0 ≤ hi) => W.hD lo hi hc.1 hc.2) K
    (-((h + W.gA + W.r : Nat) : Int) + W.e) 0
    (fun (i : Nat) (hi : i < K) => by
      have hm := mul_step (d := W.dD) hi
      constructor
      · rw [← Int.natCast_mul]; omega
      · rw [← Int.natCast_mul]; omega)
  have h₄' := shift h₄ (lo' := 0) (hi' := ((K * W.dD : Nat) : Int))
    (by rw [← Int.natCast_mul]; omega) (by rw [← Int.natCast_mul]; omega)
  exact ⟨_, by have := W.pos; omega, steps_trans (steps_trans (steps_trans h₁ h₂') h₃) h₄'⟩

theorem Wide.not_halts (W : Wide) {prog : Program} {j b g : Nat} (J K : Nat → Nat)
    (start : prog.init.steps j = some ⟨blk 0 b, W.outer⟩) (hb : W.hmin ≤ b) (hr : W.r ≤ W.d)
    (hJ : ∀ m : Nat, J m * W.d = b + g * m + W.gA + W.r)
    (hK : ∀ m : Nat, K m * W.dD + W.e = b + g * m + W.gA + W.r)
    (hg : ∀ m : Nat, K m * W.dD = b + g * (m + 1))
    (hL : W.L ≤ b + W.gA + W.r) : ¬ prog.init.Halts := by
  refine Block.not_halts (a := g) (b := b) start fun (m : Nat) => ?_
  obtain ⟨k, hk, hs⟩ := W.pass (h := g * m + b) (J := J m) (K := K m) (by omega) hr
    (by rw [hJ m]; omega) (by rw [hK m]; omega) (by omega)
  refine ⟨k, hk, ?_⟩
  rw [show ((g * m + b : Nat) : Int) = (g : Int) * m + b by push_cast; rfl] at hs
  rw [hs]
  congr 3
  rw [hg m]
  push_cast
  omega

def nf (lo hi : Int) (xs : List Int) : Tape :=
  ⟨fun (i : Int) => (decide (lo ≤ i ∧ i ≤ hi)).xor (decide (xs.count i % 2 = 1))⟩

theorem count_map_add (xs : List Int) (k i : Int) :
    (xs.map fun (x : Int) => x + k).count i = xs.count (i - k) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.count_cons, ih, beq_iff_eq]
    congr 1
    by_cases h : x = i - k
    · subst h; simp
    · rw [if_neg (by omega), if_neg h]

theorem blk_eq_nf (lo hi : Int) : blk lo hi = nf lo hi [] := by
  unfold blk nf
  congr 1
  funext i
  simp

theorem nf_moveL (lo hi : Int) (xs : List Int) :
    (nf lo hi xs).moveL = nf (lo + 1) (hi + 1) (xs.map fun (x : Int) => x + 1) := by
  unfold nf Tape.moveL
  congr 1
  funext i
  rw [count_map_add]
  have e : (lo ≤ i - 1 ∧ i - 1 ≤ hi) = (lo + 1 ≤ i ∧ i ≤ hi + 1) := propext (by omega)
  simp only [e]

theorem nf_moveR (lo hi : Int) (xs : List Int) :
    (nf lo hi xs).moveR = nf (lo + -1) (hi + -1) (xs.map fun (x : Int) => x + -1) := by
  unfold nf Tape.moveR
  congr 1
  funext i
  rw [count_map_add, show i - -1 = i + 1 by omega]
  have e : (lo ≤ i + 1 ∧ i + 1 ≤ hi) = (lo + -1 ≤ i ∧ i ≤ hi + -1) := propext (by omega)
  simp only [e]

theorem nf_flip (lo hi : Int) (xs : List Int) : (nf lo hi xs).flip = nf lo hi (0 :: xs) := by
  unfold nf Tape.flip Tape.head
  congr 1
  funext i
  by_cases h : i = 0
  · subst h
    simp only [↓reduceIte, List.count_cons_self]
    cases decide (lo ≤ 0 ∧ 0 ≤ hi) <;> cases hc : decide (xs.count 0 % 2 = 1) <;>
      simp_all <;> omega
  · rw [if_neg h, List.count_cons_of_ne (Ne.symm h)]

theorem nf_head (lo hi : Int) (xs : List Int) :
    (nf lo hi xs).head = (decide (lo ≤ 0 ∧ 0 ≤ hi)).xor (decide (xs.count 0 % 2 = 1)) := rfl

theorem nf_cells (lo hi : Int) (xs : List Int) (i : Int) :
    (nf lo hi xs).cells i = (decide (lo ≤ i ∧ i ≤ hi)).xor (decide (xs.count i % 2 = 1)) := rfl

theorem blank_eq_nf : Tape.blank = nf 0 (-1) [] := by
  unfold nf Tape.blank
  congr 1
  funext i
  simp only [List.count_nil]
  rw [Bool.eq_iff_iff]
  simp
  omega

theorem xor_decide (p q : Prop) [Decidable p] [Decidable q] :
    (decide p ^^ decide q) = decide (¬ (p ↔ q)) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

attribute [irreducible] nf

macro "nf_tac" : tactic => `(tactic| (
  (try simp only [blk_eq_nf, Program.init, blank_eq_nf])
  all_goals (set_option linter.deprecated false in
    (try simp (disch := omega) [Config.steps, Config.step, nf_moveL, nf_moveR, nf_flip, nf_cells, nf_head,
      decide_eq_true, decide_eq_false, if_pos, if_neg, Int.add_assoc]))
  all_goals (
    unfold nf
    congr 1)
  all_goals (funext i)
  all_goals (try simp only [xor_decide])
  all_goals (try rw [decide_eq_decide])
  all_goals (try simp only [List.count_cons, List.count_nil, beq_iff_eq])
  all_goals (repeat' split)
  all_goals omega))

macro "blk_tac" : tactic => `(tactic| (
  set_option linter.deprecated false in
  simp (disch := omega) [Config.steps, Config.step, blk, Tape.head, Tape.moveL, Tape.moveR,
    Tape.flip, Program.init, Tape.blank, if_pos, if_neg]
  all_goals (
    funext i
    repeat' split
    all_goals (
      (try simp only [Bool.not_eq_true', Bool.not_eq_false', Bool.not_not] at *)
      (try (rw [Bool.eq_iff_iff]; simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true',
        decide_eq_true_eq, decide_eq_false_iff_not]))
      omega))))

end Bf.Solved.Block
