import BBBTape.Core.Search
import BBBTape.Expanders.TNF
import BBBTape.Deciders.Chains

namespace BBBTape

theorem bb9 : IsBB 9 18 := IsBB.of_search Φ₁ Ξ₁ (by native_decide)

end BBBTape
