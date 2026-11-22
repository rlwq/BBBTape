import BBBTape.Results.BB18.Part0
import BBBTape.Results.BB18.Part1
import BBBTape.Results.BB18.Part2
import BBBTape.Results.BB18.Part3
import BBBTape.Results.BB18.Part4
import BBBTape.Results.BB18.Part5
import BBBTape.Results.BB18.Part6
import BBBTape.Results.BB18.Part7
import BBBTape.Results.BB18.Part8
import BBBTape.Results.BB18.Part9
import BBBTape.Results.BB18.Part10
import BBBTape.Results.BB18.Part11
import BBBTape.Results.BB18.Part12
import BBBTape.Results.BB18.Part13
import BBBTape.Results.BB18.Part14
import BBBTape.Results.BB18.Part15
import BBBTape.Results.BB18.Part16
import BBBTape.Results.BB18.Part17
import BBBTape.Results.BB18.Part18
import BBBTape.Results.BB18.Part19
import BBBTape.Results.BB18.Part20
import BBBTape.Results.BB18.Part21
import BBBTape.Results.BB18.Part22
import BBBTape.Results.BB18.Part23
import BBBTape.Results.BB18.Part24
import BBBTape.Results.BB18.Part25
import BBBTape.Results.BB18.Part26
import BBBTape.Results.BB18.Part27
import BBBTape.Results.BB18.Part28
import BBBTape.Results.BB18.Part29
import BBBTape.Results.BB18.Part30
import BBBTape.Results.BB18.Part31

namespace BBBTape

open scoped Program
open BB18

theorem BB18.parts : ∀ j, j < 32 → ∀ q ∈ part j, Bounded 12202 q := by
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
  | 16, _ => exact part16
  | 17, _ => exact part17
  | 18, _ => exact part18
  | 19, _ => exact part19
  | 20, _ => exact part20
  | 21, _ => exact part21
  | 22, _ => exact part22
  | 23, _ => exact part23
  | 24, _ => exact part24
  | 25, _ => exact part25
  | 26, _ => exact part26
  | 27, _ => exact part27
  | 28, _ => exact part28
  | 29, _ => exact part29
  | 30, _ => exact part30
  | 31, _ => exact part31
  | j + 32, h => exact absurd h (by omega)

theorem bb18 : IsBB 18 12202 :=
  IsBB.of_bounded (e := Φ₁) (d := Ξ₆) (.flip (.left (.flip (.loop (.left (.flip (.loop (.left (.left (.flip (.loop (.right .nil) (.flip (.right .nil)))))) (.left .nil)))) .nil)))) (by native_decide)
    (by simp [Program.Closed]) (by decide)
    (bounded_of_hashParts (e := Φ₁) (d := Ξ₆) 3 (by decide) rfl BB18.parts)

end BBBTape
