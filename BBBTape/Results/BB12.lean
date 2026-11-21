import BBBTape.Core.Search
import BBBTape.Expanders.TNF
import BBBTape.Deciders.Chains

namespace BBBTape

theorem bb12 : IsBB 12 72 := IsBB.of_search Φ₁ Ξ₂ (by native_decide)

end BBBTape
