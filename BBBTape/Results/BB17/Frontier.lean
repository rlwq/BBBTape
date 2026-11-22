import BBBTape.Core.Split
import BBBTape.Deciders.Chains
import BBBTape.Expanders.TNF

namespace BBBTape.BB17

open scoped Program

def nodes : List Program := frontier Φ₁ Ξ₅ 3 (ω 17)

def part (j : Nat) : List Program := hashPart nodes 16 j

end BBBTape.BB17
