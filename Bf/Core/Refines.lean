import Bf.Core.Program

namespace Bf

namespace Program

inductive Refines : Program → Program → Prop
  | nil   : Refines ε ε
  | left  {p q : Program} : Refines p q → Refines (.left p) (.left q)
  | right {p q : Program} : Refines p q → Refines (.right p) (.right q)
  | flip  {p q : Program} : Refines p q → Refines (.flip p) (.flip q)
  | loop  {b' b p q : Program} : Refines b' b → Refines p q → Refines (.loop b' p) (.loop b q)
  | gap   {k : Nat} {h : 0 < k} {s p q : Program} :
      ‖s‖ = k → Refines p q → Refines (s ++ p) (.gap k h q)

scoped infix:50 " ⊑ " => Refines

namespace Refines

theorem size {p q : Program} : p ⊑ q → p.size = q.size := by
  intro h
  induction h with
  | nil => rfl
  | left _ ih | right _ ih | flip _ ih => simp [Program.size, ih]
  | loop _ _ ihb ihp => simp [Program.size, ihb, ihp]
  | gap hs _ ihp => simp [Program.size, hs, ihp]

theorem append {p₁ q₁ p₂ q₂ : Program} : p₁ ⊑ q₁ → p₂ ⊑ q₂ → (p₁ ++ p₂) ⊑ (q₁ ++ q₂) := by
  intro h₁ h₂
  induction h₁ with
  | nil => exact h₂
  | left _ ih => exact .left ih
  | right _ ih => exact .right ih
  | flip _ ih => exact .flip ih
  | loop hb _ _ ihp => exact .loop hb ihp
  | gap hk _ ihp =>
    rw [append_assoc, gap_append]
    exact .gap hk ihp

theorem refl : ∀ (p : Program), p ⊑ p
  | ε         => .nil
  | .left p   => .left (refl p)
  | .right p  => .right (refl p)
  | .flip p   => .flip (refl p)
  | .loop b p => .loop (refl b) (refl p)
  | .gap k h p => .gap (s := .gap k h ε) (by simp [Program.size]) (refl p)

theorem mirror {p q : Program} : p ⊑ q → p.mirror ⊑ q.mirror := by
  intro h
  induction h with
  | nil => exact .nil
  | left _ ih => exact .right ih
  | right _ ih => exact .left ih
  | flip _ ih => exact .flip ih
  | loop _ _ ihb ihp => exact .loop ihb ihp
  | gap hk _ ihp =>
    rw [mirror_append]
    exact .gap (by rw [size_mirror, hk]) ihp

end Refines

theorem refines_gap? {s : Program} {k : Nat} : s° → ‖s‖ = k → s ⊑ ω k := by
  intro hs hk
  cases k with
  | zero => rw [size_eq_zero_of_closed hs hk]; exact .nil
  | succ k => simpa [gap?] using Refines.gap (h := Nat.succ_pos k) hk .nil

theorem refines_rep (f : Program → Program) (hf : ∀ {p q : Program}, p ⊑ q → f p ⊑ f q) :
    ∀ {n : Nat} {p q : Program}, p ⊑ q → rep f n p ⊑ rep f n q
  | 0,     _, _, h => h
  | _ + 1, _, _, h => hf (refines_rep f hf h)

end Program

end Bf
