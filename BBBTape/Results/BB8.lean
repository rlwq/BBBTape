import BBBTape.Core.Search
import BBBTape.Expanders.TNF
import BBBTape.Deciders.Chains

namespace BBBTape

theorem bb8 : IsBB 8 14 := IsBB.of_search Φ₁ Ξ₁ (by native_decide)

end BBBTape
