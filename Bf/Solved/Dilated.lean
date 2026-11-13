import Bf.Dilate
import Bf.Solved.Bouncer

namespace Bf.Solved.Dilated

theorem not_halts : ¬ (bf!"*[<<*[>>]*]").init.Halts :=
  Program.not_halts_dilate Bouncer.not_halts

def solved : Bf.Solved := ⟨bf!"*[<<*[>>]*]", .nonhalts, not_halts⟩

end Bf.Solved.Dilated
