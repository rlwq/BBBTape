import Bf.Core.Tape

namespace Bf

abbrev SpecTape : Type := Int → Bool

instance : Tape SpecTape where
  cells t i := t i
  blank _ := false
  flip t i := if i = 0 then !t 0 else t i
  moveL t i := t (i - 1)
  moveR t i := t (i + 1)
  cells_blank _ := rfl
  cells_flip _ _ := rfl
  cells_moveL _ _ := rfl
  cells_moveR _ _ := rfl

end Bf
