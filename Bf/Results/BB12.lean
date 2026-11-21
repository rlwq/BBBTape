import Bf.Core.Search
import Bf.Expanders.TNF
import Bf.Deciders.Chains

namespace Bf

theorem bb12 : IsBB 12 72 := IsBB.of_search Φ₁ Ξ₂ (by native_decide)

end Bf
