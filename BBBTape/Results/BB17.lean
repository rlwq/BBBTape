import BBBTape.Core.Search
import BBBTape.Deciders.Chains
import BBBTape.Expanders.TNF

namespace BBBTape

theorem bb17 : IsBB 17 871 := IsBB.of_search Φ₁ Ξ₅ (by native_decide)

end BBBTape
