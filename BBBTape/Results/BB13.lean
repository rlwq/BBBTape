import BBBTape.Core.Search
import BBBTape.Expanders.TNF
import BBBTape.Deciders.Chains

namespace BBBTape

theorem bb13 : IsBB 13 120 := IsBB.of_search Φ₁ Ξ₂ (by native_decide)

end BBBTape
