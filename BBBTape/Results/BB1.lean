import BBBTape.Core.Search
import BBBTape.Expanders.TNF
import BBBTape.Deciders.Chains

namespace BBBTape

theorem bb1 : IsBB 1 1 := IsBB.of_search Φ₁ Ξ₁ (by native_decide)

end BBBTape
