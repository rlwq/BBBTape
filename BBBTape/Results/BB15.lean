import BBBTape.Core.Search
import BBBTape.Deciders.Chains
import BBBTape.Expanders.TNF

namespace BBBTape

theorem bb15 : IsBB 15 276 := IsBB.of_search Φ₁ Ξ₃ (by native_decide)

end BBBTape
