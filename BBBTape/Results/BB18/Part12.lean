import BBBTape.Results.BB18.Frontier

namespace BBBTape.BB18

theorem part12 : ∀ q ∈ part 12, Bounded 12202 q :=
  Bounded.of_all_within (e := Φ₁) (d := Ξ₆) (by native_decide)

end BBBTape.BB18
