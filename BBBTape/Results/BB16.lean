import BBBTape.Core.Search
import BBBTape.Deciders.Chains
import BBBTape.Expanders.TNF

namespace BBBTape

theorem bb16 : IsBB 16 352 := IsBB.of_search Φ₁ Ξ₄ (by native_decide)

end BBBTape
