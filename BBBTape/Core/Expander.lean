import BBBTape.Core.Machine

namespace BBBTape

open scoped Program in
structure Expander where
  expand     : (q : Program) → Fin q.numGaps → List Program
  cover      : ∀ {p q : Program} (i : Fin q.numGaps),
    p° → p ⊑ q → ∃ c ∈ expand q i, ∃ p', p'° ∧ p' ⊑ c ∧ p ≼ p'
  /-- Every child is strictly less unknown than its parent, so expansion cannot go on forever. -/
  decreasing : ∀ {q c : Program} {i : Fin q.numGaps}, c ∈ expand q i → ‖c‖° < ‖q‖°
  /-- Expansion only fills gaps, so every child has the length of its parent. -/
  size       : ∀ {q c : Program} {i : Fin q.numGaps}, c ∈ expand q i → ‖c‖ = ‖q‖

end BBBTape
