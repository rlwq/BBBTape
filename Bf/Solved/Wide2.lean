import Bf.Solved.Block

namespace Bf.Solved.Block

structure Wide2 where
  outer : Program
  inner : Program
  tA : Nat
  tB : Nat
  tC : Nat
  tD : Nat
  d : Nat
  dD : Nat
  a : Nat
  gA : Nat
  r : Nat
  c : Nat
  e : Int
  L : Nat
  hmin : Nat
  pos : 0 < tA + tC
  hA : ∀ h : Nat, hmin ≤ h →
    (Config.mk (blk 0 h) outer).steps tA = some ⟨blk (-(a : Int)) ((h : Int) + (gA : Int)), inner⟩
  hB : ∀ lo hi : Int, lo ≤ 0 → 0 ≤ hi →
    (Config.mk (blk lo hi) inner).steps tB = some ⟨blk (lo - d) (hi - d), inner⟩
  hC : ∀ lo : Int, lo ≤ -(L : Int) →
    (Config.mk (blk lo (-(r : Int))) inner).steps tC = some ⟨blk (lo + e) (c : Int), outer⟩
  hD : ∀ lo hi : Int, lo ≤ -(dD : Int) → 0 ≤ hi →
    (Config.mk (blk lo hi) outer).steps tD = some ⟨blk (lo + dD) (hi + dD), outer⟩

theorem Wide2.pass (W : Wide2) {h J K : Nat} (hh : W.hmin ≤ h) (hr : W.r ≤ W.d)
    (hJ : J * W.d = h + W.gA + W.r)
    (hK : ((K * W.dD : Nat) : Int) + W.e = W.a + h + W.gA + W.r)
    (hL : W.L ≤ W.a + h + W.gA + W.r) :
    ∃ k : Nat, 0 < k ∧
      (Config.mk (blk 0 h) W.outer).steps k =
        some ⟨blk 0 ((W.c : Int) + ((K * W.dD : Nat) : Int)), W.outer⟩ := by
  have h₁ := W.hA h hh
  have h₂ := iterate (C := fun (lo hi : Int) => lo ≤ 0 ∧ 0 ≤ hi)
    (fun (lo hi : Int) (hc : lo ≤ 0 ∧ 0 ≤ hi) => by
      have := W.hB lo hi hc.1 hc.2
      rw [show lo - W.d = lo + -(W.d : Int) by omega, show hi - W.d = hi + -(W.d : Int) by omega] at this
      exact this) J (-(W.a : Int)) ((h : Int) + (W.gA : Int))
    (fun (i : Nat) (hi : i < J) => by
      have hm := mul_step (d := W.d) hi
      constructor
      · rw [Int.mul_neg, ← Int.natCast_mul]; omega
      · rw [Int.mul_neg, ← Int.natCast_mul]; omega)
  have h₂' := shift h₂ (lo' := -((W.a + h + W.gA + W.r : Nat) : Int)) (hi' := -(W.r : Int))
    (by rw [Int.mul_neg, ← Int.natCast_mul]; omega) (by rw [Int.mul_neg, ← Int.natCast_mul]; omega)
  have h₃ := W.hC (-((W.a + h + W.gA + W.r : Nat) : Int)) (by omega)
  have h₄ := iterate (C := fun (lo hi : Int) => lo ≤ -(W.dD : Int) ∧ 0 ≤ hi)
    (fun (lo hi : Int) (hc : lo ≤ -(W.dD : Int) ∧ 0 ≤ hi) => W.hD lo hi hc.1 hc.2) K
    (-((W.a + h + W.gA + W.r : Nat) : Int) + W.e) (W.c : Int)
    (fun (i : Nat) (hi : i < K) => by
      have hm := mul_step (d := W.dD) hi
      constructor
      · rw [← Int.natCast_mul]; omega
      · rw [← Int.natCast_mul]; omega)
  have h₄' := shift h₄ (lo' := 0) (hi' := (W.c : Int) + ((K * W.dD : Nat) : Int))
    (by rw [← Int.natCast_mul] <;> omega) (by rw [← Int.natCast_mul] <;> omega)
  have hJpos : 0 < W.tA + W.tC := W.pos
  exact ⟨_, by omega, steps_trans (steps_trans (steps_trans h₁ h₂') h₃) h₄'⟩

theorem Wide2.not_halts (W : Wide2) {prog : Program} {j b g : Nat} (J K : Nat → Nat)
    (start : prog.init.steps j = some ⟨blk 0 b, W.outer⟩) (hb : W.hmin ≤ b) (hr : W.r ≤ W.d)
    (hJ : ∀ m : Nat, J m * W.d = b + g * m + W.gA + W.r)
    (hK : ∀ m : Nat, ((K m * W.dD : Nat) : Int) + W.e = W.a + (b + g * m) + W.gA + W.r)
    (hg : ∀ m : Nat, W.c + K m * W.dD = b + g * (m + 1))
    (hL : W.L ≤ W.a + b + W.gA + W.r) : ¬ prog.init.Halts := by
  refine Block.not_halts (a := g) (b := b) start fun (m : Nat) => ?_
  obtain ⟨k, hk, hs⟩ := W.pass (h := g * m + b) (J := J m) (K := K m) (by omega) hr
    (by rw [hJ m]; omega) (by rw [hK m]; push_cast; omega) (by omega)
  refine ⟨k, hk, ?_⟩
  rw [show ((g * m + b : Nat) : Int) = (g : Int) * m + b by push_cast; rfl] at hs
  rw [hs]
  congr 3
  rw [← Int.natCast_add, hg m]
  push_cast
  omega

end Bf.Solved.Block
