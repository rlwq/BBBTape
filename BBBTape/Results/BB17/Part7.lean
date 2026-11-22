import BBBTape.Results.BB17.Frontier

namespace BBBTape.BB17

theorem part7 : ∀ q ∈ part 7, Bounded 871 q :=
  Bounded.of_all_within (e := Φ₁) (d := Ξ₅) (by native_decide)

end BBBTape.BB17
