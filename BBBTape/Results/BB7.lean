import BBBTape.Core.Search
import BBBTape.Expanders.TNF
import BBBTape.Deciders.Chains

namespace BBBTape

theorem bb7 : IsBB 7 10 := IsBB.of_search Φ₁ Ξ₁ (by native_decide)

end BBBTape
