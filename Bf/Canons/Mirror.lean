import Bf.Canon
import Bf.Mirror

namespace Bf

def Program.firstShift : Program → Option Bool
  | nil      => none
  | left _   => some false
  | right _  => some true
  | flip p   => p.firstShift
  | loop b p => b.firstShift <|> p.firstShift

def Canon.mirror : Canon where
  f := fun (p : Program) => if p.firstShift = some true then p.mirror else p
  size_eq := fun (p : Program) => by
    split
    · exact p.size_mirror
    · rfl
  sound := fun (p : Program) => by
    split
    · exact p.sameTime_mirror.symm
    · exact .refl p

end Bf
