import Bf.Simulation
import Bf.Syntax
import Bf.Solved

namespace Bf.Solved.Bouncer

open Program

def L : Program := bf!"[<*[>]*]"

def I : Program := bf!"[>]*[<*[>]*]"

def blk (lo hi : Int) : Tape := ⟨fun (i : Int) => decide (lo ≤ i ∧ i ≤ hi)⟩

theorem steps_trans {c d e : Config} {a b : Nat} (h₁ : c.steps a = some d) (h₂ : d.steps b = some e) :
    c.steps (a + b) = some e := by
  rw [Config.steps_add, h₁]; exact h₂

theorem sweepL (lo hi : Int) (h₁ : lo < 0) (h₂ : 0 ≤ hi) :
    (Config.mk (blk lo hi) L).steps 5 = some ⟨blk (lo + 1) (hi + 1), L⟩ := by
  have a : lo ≤ 0 ∧ 0 ≤ hi := ⟨by omega, h₂⟩
  have c₁ : lo ≤ -1 := by omega
  have c₂ : -1 ≤ hi := by omega
  simp [Config.steps, Config.step, L, blk, Tape.head, Tape.moveL, Tape.flip, a, c₁, c₂]
  funext i
  by_cases h0 : i = 0 <;> simp [h0]
  all_goals (try (rw [Bool.eq_iff_iff]; simp only [Bool.and_eq_true, decide_eq_true_eq])); omega

theorem sweepsL (j : Nat) : ∀ lo hi : Int, lo + j ≤ 0 → 0 ≤ hi →
    (Config.mk (blk lo hi) L).steps (5 * j) = some ⟨blk (lo + j) (hi + j), L⟩ := by
  induction j with
  | zero => intro lo hi _ _; simp [Config.steps]
  | succ j ih =>
    intro lo hi h₁ h₂
    have := steps_trans (sweepL lo hi (by omega) h₂) (ih (lo + 1) (hi + 1) (by omega) (by omega))
    rw [show 5 * (j + 1) = 5 + 5 * j by omega]
    rw [this, show lo + 1 + j = lo + (j + 1 : Nat) by omega, show hi + 1 + j = hi + (j + 1 : Nat) by omega]

theorem turn (m : Int) (hm : 0 ≤ m) :
    (Config.mk (blk 0 m) L).steps 3 = some ⟨blk 0 (m + 1), I⟩ := by
  have c₁ : (0 : Int) ≤ m := hm
  simp [Config.steps, Config.step, L, I, blk, Tape.head, Tape.moveL, Tape.flip, c₁]
  funext i
  by_cases h0 : i = 0 <;> simp [h0]
  all_goals (try (rw [Bool.eq_iff_iff]; simp only [Bool.and_eq_true, decide_eq_true_eq])); omega

theorem sweepR (lo hi : Int) (h₁ : lo ≤ 0) (h₂ : 0 ≤ hi) :
    (Config.mk (blk lo hi) I).steps 2 = some ⟨blk (lo - 1) (hi - 1), I⟩ := by
  have a : lo ≤ 0 ∧ 0 ≤ hi := ⟨h₁, h₂⟩
  simp [Config.steps, Config.step, I, blk, Tape.head, Tape.moveR, a]
  funext i
  rw [Bool.eq_iff_iff]; simp only [Bool.and_eq_true, decide_eq_true_eq]; omega

theorem sweepsR (j : Nat) : ∀ lo hi : Int, lo ≤ 0 → (j : Int) ≤ hi + 1 →
    (Config.mk (blk lo hi) I).steps (2 * j) = some ⟨blk (lo - j) (hi - j), I⟩ := by
  induction j with
  | zero => intro lo hi _ _; simp [Config.steps]
  | succ j ih =>
    intro lo hi h₁ h₂
    have := steps_trans (sweepR lo hi h₁ (by omega)) (ih (lo - 1) (hi - 1) (by omega) (by omega))
    rw [show 2 * (j + 1) = 2 + 2 * j by omega]
    rw [this, show lo - 1 - j = lo - (j + 1 : Nat) by omega, show hi - 1 - j = hi - (j + 1 : Nat) by omega]

theorem exit (lo : Int) (h : lo ≤ -1) :
    (Config.mk (blk lo (-1)) I).steps 2 = some ⟨blk lo 0, L⟩ := by
  simp [Config.steps, Config.step, I, L, blk, Tape.head, Tape.flip]
  funext i
  by_cases h0 : i = 0 <;> simp [h0]
  all_goals (try (rw [Bool.eq_iff_iff]; simp only [Bool.and_eq_true, decide_eq_true_eq])); omega

def S (m : Nat) : Config := ⟨blk (-m) 0, L⟩

theorem pass (m : Nat) : (S m).steps (5 * m + 3 + 2 * (m + 2) + 2) = some (S (m + 2)) := by
  have h₁ := sweepsL m (-m) 0 (by omega) (by omega)
  rw [show -(m : Int) + m = 0 by omega, show (0 : Int) + m = m by omega] at h₁
  have h₂ := turn m (by omega)
  have h₃ := sweepsR (m + 2) 0 (m + 1) (by omega) (by omega)
  rw [show (0 : Int) - (m + 2 : Nat) = -(m + 2 : Nat) by omega,
      show (m : Int) + 1 - (m + 2 : Nat) = -1 by omega] at h₃
  have h₄ := exit (-(m + 2 : Nat)) (by omega)
  exact steps_trans (steps_trans (steps_trans h₁ h₂) h₃) h₄

def prog : Program := bf!"*[<*[>]*]"

theorem not_halts : ¬ prog.init.Halts := by
  have h₀ : prog.init.steps 1 = some (S 0) := by
    simp [Config.steps, Config.step, prog, L, Program.init, S, blk, Tape.blank, Tape.flip, Tape.head]
    funext i
    by_cases h0 : i = 0 <;> simp [h0] <;> omega
  refine Config.not_halts_of_steps h₀ ?_
  refine Config.Progress.not_halts (S := fun (c : Config) => ∃ m : Nat, c = S m) ?_ ⟨0, rfl⟩
  rintro _ ⟨m, rfl⟩
  exact ⟨_, _, by omega, pass m, m + 2, rfl⟩

def solved : Bf.Solved := ⟨prog, .nonhalts, not_halts⟩

end Bf.Solved.Bouncer
