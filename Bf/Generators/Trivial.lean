import Bf.Generator

namespace Bf

namespace Generator.trivial

open Program

def gen : Nat → List Program
  | 0     => [nil]
  | n + 1 =>
    (gen n).flatMap (fun (p : Program) => [left p, right p, flip p]) ++
    (List.range n).flatMap fun (a : Nat) =>
      (List.range n).flatMap fun (b : Nat) =>
        if a + b + 1 = n then
          (gen a).flatMap fun (body : Program) => (gen b).map (loop body)
        else []
termination_by n => n
decreasing_by all_goals simp_all <;> omega

theorem mem_gen {n : Nat} {p : Program} : p ∈ gen n ↔ p.size = n := by
  induction p generalizing n with
  | nil => cases n <;> simp [gen, Program.size]
  | left p ih | right p ih | flip p ih => cases n <;> simp [gen, Program.size, ih]
  | loop body p ihb ih =>
    cases n with
    | zero => simp [gen, Program.size]
    | succ n =>
      simp [gen, Program.size, ihb, ih]
      constructor
      · rintro ⟨a, -, b, -, h, rfl, rfl⟩
        exact h
      · intro (h : body.size + p.size + 1 = n)
        exact ⟨body.size, by omega, p.size, by omega, h, rfl, rfl⟩

end Generator.trivial

def Generator.trivial : Generator where
  gen   := Generator.trivial.gen
  size  := Generator.trivial.mem_gen.mp
  cover := fun (p : Program) => ⟨p, Generator.trivial.mem_gen.mpr rfl, fun (_ : Nat) => .rfl⟩

end Bf
