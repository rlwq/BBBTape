namespace BBBTape

class Tape (T : Type) where
  cells       : T → Int → Bool
  blank       : T
  flip        : T → T
  moveL       : T → T
  moveR       : T → T
  cells_blank : ∀ i : Int, cells blank i = false
  cells_flip  : ∀ (t : T) (i : Int), cells (flip t) i = if i = 0 then !cells t 0 else cells t i
  cells_moveL : ∀ (t : T) (i : Int), cells (moveL t) i = cells t (i - 1)
  cells_moveR : ∀ (t : T) (i : Int), cells (moveR t) i = cells t (i + 1)

namespace Tape

attribute [simp] cells_blank

end Tape

end BBBTape
