import BBBTape.Core.Search
import BBBTape.Deciders.Chains
import BBBTape.Expanders.TNF

namespace BBBTape

theorem bb18 : IsBB 18 12202 := IsBB.of_search Φ₁ Ξ₆ (by native_decide)

end BBBTape
