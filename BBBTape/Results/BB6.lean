import BBBTape.Core.Search
import BBBTape.Expanders.TNF
import BBBTape.Deciders.Chains

namespace BBBTape

theorem bb6 : IsBB 6 8 := IsBB.of_search Φ₁ Ξ₁ (by native_decide)

end BBBTape
