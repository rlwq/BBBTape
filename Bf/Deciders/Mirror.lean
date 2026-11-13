import Bf.Decider
import Bf.Mirror

namespace Bf

def Decider.mirror (d : Decider) : Decider where
  run := fun (p : Program) => d.run p.mirror
  sound := fun (p : Program) => by
    have h := d.sound p.mirror
    cases hv : d.run p.mirror with
    | halts n =>
      rw [hv] at h
      exact (p.sameTime_mirror n).mp h
    | nonhalts =>
      rw [hv] at h
      exact fun (hp : p.init.Halts) => h (hp.imp fun (k : Nat) => (p.sameTime_mirror k).mpr)
    | unknown => trivial

end Bf
