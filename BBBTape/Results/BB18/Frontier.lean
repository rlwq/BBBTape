import BBBTape.Core.Split
import BBBTape.Deciders.Chains
import BBBTape.Expanders.TNF

namespace BBBTape.BB18

open scoped Program

def nodes : List Program := frontier Φ₁ Ξ₆ 3 (ω 18)

def part (j : Nat) : List Program := hashPart nodes 32 j

end BBBTape.BB18
