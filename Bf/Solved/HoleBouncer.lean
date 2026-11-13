import Bf.Solved.Block

namespace Bf.Solved.HoleBouncer

open Block

def hb (lo hi : Int) : Tape := ⟨fun (i : Int) => decide (lo ≤ i ∧ i ≤ hi ∧ i ≠ -1)⟩

def L : Program := bf!"[<[>]*<*>]"

def J : Program := bf!"[>]*<*>[<[>]*<*>]"

theorem extend (h : Nat) : (Config.mk (blk 0 h) L).steps 7 = some ⟨blk (-1) (h + 1), L⟩ := by
  simp only [L]; blk_tac

theorem enter (hi : Int) (h : 1 ≤ hi) :
    (Config.mk (blk (-1) hi) L).steps 2 = some ⟨blk 0 (hi + 1), J⟩ := by
  simp only [L, J]; blk_tac

theorem run (lo hi : Int) (h₁ : lo ≤ 0) (h₂ : 0 ≤ hi) :
    (Config.mk (blk lo hi) J).steps 2 = some ⟨blk (lo + -1) (hi + -1), J⟩ := by
  simp only [J]; blk_tac

theorem punch (lo : Int) (h : lo ≤ -2) :
    (Config.mk (blk lo (-1)) J).steps 5 = some ⟨hb lo 0, L⟩ := by
  simp only [J, L, hb]; blk_tac

theorem walk (lo hi : Int) (h₁ : lo ≤ -2) (h₂ : 0 ≤ hi) :
    (Config.mk (hb lo hi) L).steps 7 = some ⟨hb (lo + 1) (hi + 1), L⟩ := by
  simp only [L, hb]; blk_tac

theorem hb_eq (hi : Int) : hb (-1) hi = blk 0 hi := by
  unfold hb blk
  congr 1
  funext i
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq]
  omega

theorem pass (h : Nat) : ∃ k : Nat, 0 < k ∧
    (Config.mk (blk 0 (2 * h + 0)) L).steps k = some ⟨blk 0 (2 * (h + 1) + 0), L⟩ := by
  have h₁ := extend (2 * h)
  have h₂ := enter (((2 * h : Nat) : Int) + 1) (by omega)
  have h₃ := iterate (C := fun (lo hi : Int) => lo ≤ 0 ∧ 0 ≤ hi)
    (fun (lo hi : Int) (hc : lo ≤ 0 ∧ 0 ≤ hi) => run lo hi hc.1 hc.2) (2 * h + 3) 0
    (((2 * h : Nat) : Int) + 1 + 1) (fun (i : Nat) (_ : i < 2 * h + 3) => ⟨by omega, by omega⟩)
  have h₃' := shift h₃ (lo' := -((2 * h + 3 : Nat) : Int)) (hi' := -1) (by omega) (by omega)
  have h₄ := punch (-((2 * h + 3 : Nat) : Int)) (by omega)
  have h₅ := iterate (C := fun (lo hi : Int) => lo ≤ -2 ∧ 0 ≤ hi)
    (fun (lo hi : Int) (hc : lo ≤ -2 ∧ 0 ≤ hi) => by
      have := walk lo hi hc.1 hc.2
      exact this) (2 * h + 2) (-((2 * h + 3 : Nat) : Int)) 0
    (fun (i : Nat) (_ : i < 2 * h + 2) => ⟨by omega, by omega⟩)
  have h₅' := shift h₅ (lo' := -1) (hi' := ((2 * (h + 1) + 0 : Nat) : Int)) (by omega) (by omega)
  rw [hb_eq] at h₅'
  have h₁' := shift h₁ (T := blk) (lo' := -1) (hi' := ((2 * h : Nat) : Int) + 1) rfl (by omega)
  rw [show (2 * (h : Int) + 0) = ((2 * h : Nat) : Int) by omega,
    show (2 * ((h : Int) + 1) + 0) = ((2 * (h + 1) + 0 : Nat) : Int) by omega]
  exact ⟨_, by omega, steps_trans (steps_trans (steps_trans (steps_trans h₁' h₂) h₃') h₄) h₅'⟩

def prog : Program := bf!"*[<[>]*<*>]"

theorem not_halts : ¬ prog.init.Halts :=
  Block.not_halts (a := 2) (b := 0) (j := 1) (by simp only [prog, L]; blk_tac) pass

def solved : Bf.Solved := ⟨prog, .nonhalts, not_halts⟩

end Bf.Solved.HoleBouncer
