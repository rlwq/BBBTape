import BBBTape.Results.BB18.Frontier

namespace BBBTape.BB18

theorem part14 : ∀ q ∈ part 14, Bounded 12202 q :=
  Bounded.of_all_within (e := Φ₁) (d := Ξ₆) (by native_decide)

end BBBTape.BB18
