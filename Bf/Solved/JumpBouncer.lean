import Bf.Solved.Bouncer

namespace Bf.Solved.JumpBouncer

open Program
open Bouncer (blk steps_trans)

def L : Program := bf!"[<*[>>]*]"

def J : Program := bf!"[>>]*[<*[>>]*]"

theorem extend (m : Nat) :
    (Config.mk (blk 0 (2 * m)) L).steps 3 = some ⟨blk 0 (2 * m + 1), J⟩ := by
  have c₁ : (0 : Int) ≤ 2 * m := by omega
  simp [Config.steps, Config.step, L, J, blk, Tape.head, Tape.moveL, Tape.flip, c₁]
  funext i
  by_cases h0 : i = 0 <;> simp [h0]
  all_goals (try (rw [Bool.eq_iff_iff]; simp only [Bool.and_eq_true, decide_eq_true_eq])); omega

theorem jump (lo hi : Int) (h₁ : lo ≤ 0) (h₂ : 0 ≤ hi) :
    (Config.mk (blk lo hi) J).steps 3 = some ⟨blk (lo - 2) (hi - 2), J⟩ := by
  have a : lo ≤ 0 ∧ 0 ≤ hi := ⟨h₁, h₂⟩
  simp [Config.steps, Config.step, J, blk, Tape.head, Tape.moveR, a]
  funext i
  rw [Bool.eq_iff_iff]; simp only [Bool.and_eq_true, decide_eq_true_eq]; omega

theorem jumps (j : Nat) : ∀ lo hi : Int, lo ≤ 0 → 2 * (j : Int) ≤ hi + 2 →
    (Config.mk (blk lo hi) J).steps (3 * j) = some ⟨blk (lo - 2 * j) (hi - 2 * j), J⟩ := by
  induction j with
  | zero => intro lo hi _ _; simp [Config.steps]
  | succ j ih =>
    intro lo hi h₁ h₂
    have := steps_trans (jump lo hi h₁ (by omega)) (ih (lo - 2) (hi - 2) (by omega) (by omega))
    rw [show 3 * (j + 1) = 3 + 3 * j by omega, this]
    congr 3 <;> omega

theorem exit (lo : Int) (h : lo ≤ -1) :
    (Config.mk (blk lo (-1)) J).steps 2 = some ⟨blk lo 0, L⟩ := by
  simp [Config.steps, Config.step, J, L, blk, Tape.head, Tape.flip]
  funext i
  by_cases h0 : i = 0 <;> simp [h0]
  all_goals (try (rw [Bool.eq_iff_iff]; simp only [Bool.and_eq_true, decide_eq_true_eq])); omega

theorem sweep (lo hi : Int) (h₁ : lo < 0) (h₂ : 0 ≤ hi) :
    (Config.mk (blk lo hi) L).steps 5 = some ⟨blk (lo + 1) (hi + 1), L⟩ := by
  have a : lo ≤ 0 ∧ 0 ≤ hi := ⟨by omega, h₂⟩
  have c₁ : lo ≤ -1 := by omega
  have c₂ : -1 ≤ hi := by omega
  simp [Config.steps, Config.step, L, blk, Tape.head, Tape.moveL, Tape.flip, a, c₁, c₂]
  funext i
  by_cases h0 : i = 0 <;> simp [h0]
  all_goals (try (rw [Bool.eq_iff_iff]; simp only [Bool.and_eq_true, decide_eq_true_eq])); omega

theorem sweeps (j : Nat) : ∀ lo hi : Int, lo + j ≤ 0 → 0 ≤ hi →
    (Config.mk (blk lo hi) L).steps (5 * j) = some ⟨blk (lo + j) (hi + j), L⟩ := by
  induction j with
  | zero => intro lo hi _ _; simp [Config.steps]
  | succ j ih =>
    intro lo hi h₁ h₂
    have := steps_trans (sweep lo hi (by omega) h₂) (ih (lo + 1) (hi + 1) (by omega) (by omega))
    rw [show 5 * (j + 1) = 5 + 5 * j by omega, this]
    congr 3 <;> omega

def S (m : Nat) : Config := ⟨blk 0 (2 * m), L⟩

theorem pass (m : Nat) : (S m).steps (3 + 3 * (m + 1) + 2 + 5 * (2 * m + 2)) = some (S (m + 1)) := by
  have h₁ := extend m
  have h₂ := jumps (m + 1) 0 (2 * m + 1) (by omega) (by omega)
  rw [show (0 : Int) - 2 * ((m + 1 : Nat) : Int) = -(2 * m + 2 : Nat) by omega,
      show (2 * m + 1 : Int) - 2 * ((m + 1 : Nat) : Int) = -1 by omega] at h₂
  have h₃ := exit (-(2 * m + 2 : Nat)) (by omega)
  have h₄ := sweeps (2 * m + 2) (-(2 * m + 2 : Nat)) 0 (by omega) (by omega)
  rw [show -((2 * m + 2 : Nat) : Int) + ((2 * m + 2 : Nat) : Int) = 0 by omega,
      show (0 : Int) + ((2 * m + 2 : Nat) : Int) = 2 * ((m + 1 : Nat) : Int) by omega] at h₄
  exact steps_trans (steps_trans (steps_trans h₁ h₂) h₃) h₄

def prog : Program := bf!"*[<*[>>]*]"

theorem start : prog.init.steps 1 = some (S 0) := by
  simp [Config.steps, Config.step, prog, L, Program.init, S, blk, Tape.blank, Tape.flip, Tape.head]
  funext i
  by_cases h0 : i = 0 <;> simp [h0] <;> omega

theorem not_halts : ¬ prog.init.Halts := by
  refine Config.not_halts_of_steps start ?_
  refine Config.Progress.not_halts (S := fun (c : Config) => ∃ m : Nat, c = S m) ?_ ⟨0, rfl⟩
  rintro _ ⟨m, rfl⟩
  exact ⟨_, _, by omega, pass m, m + 1, rfl⟩

def solved : Bf.Solved := ⟨prog, .nonhalts, not_halts⟩

end Bf.Solved.JumpBouncer
