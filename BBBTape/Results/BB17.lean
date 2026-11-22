import BBBTape.Results.BB17.Part0
import BBBTape.Results.BB17.Part1
import BBBTape.Results.BB17.Part2
import BBBTape.Results.BB17.Part3
import BBBTape.Results.BB17.Part4
import BBBTape.Results.BB17.Part5
import BBBTape.Results.BB17.Part6
import BBBTape.Results.BB17.Part7
import BBBTape.Results.BB17.Part8
import BBBTape.Results.BB17.Part9
import BBBTape.Results.BB17.Part10
import BBBTape.Results.BB17.Part11
import BBBTape.Results.BB17.Part12
import BBBTape.Results.BB17.Part13
import BBBTape.Results.BB17.Part14
import BBBTape.Results.BB17.Part15

namespace BBBTape

open scoped Program
open BB17

theorem BB17.parts : ∀ j, j < 16 → ∀ q ∈ part j, Bounded 871 q := by
  intro j hj
  match j, hj with
  | 0, _ => exact part0
  | 1, _ => exact part1
  | 2, _ => exact part2
  | 3, _ => exact part3
  | 4, _ => exact part4
  | 5, _ => exact part5
  | 6, _ => exact part6
  | 7, _ => exact part7
  | 8, _ => exact part8
  | 9, _ => exact part9
  | 10, _ => exact part10
  | 11, _ => exact part11
  | 12, _ => exact part12
  | 13, _ => exact part13
  | 14, _ => exact part14
  | 15, _ => exact part15
  | j + 16, h => exact absurd h (by omega)

theorem bb17 : IsBB 17 871 :=
  IsBB.of_bounded (e := Φ₁) (d := Ξ₅) (.flip (.loop (.loop (.left (.flip (.left (.flip (.loop (.right .nil) (.right .nil)))))) (.left (.flip (.left (.left .nil))))) .nil)) (by native_decide)
    (by simp [Program.Closed]) (by decide)
    (bounded_of_hashParts (e := Φ₁) (d := Ξ₅) 3 (by decide) rfl BB17.parts)

end BBBTape
