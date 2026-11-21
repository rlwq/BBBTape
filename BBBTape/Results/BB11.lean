import BBBTape.Core.Search
import BBBTape.Expanders.TNF
import BBBTape.Deciders.Chains

namespace BBBTape

theorem bb11 : IsBB 11 35 := IsBB.of_search Φ₁ Ξ₁ (by native_decide)

end BBBTape
