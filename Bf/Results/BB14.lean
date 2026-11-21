import Bf.Core.Search
import Bf.Expanders.TNF
import Bf.Deciders.Chains

namespace Bf

theorem bb14 : IsBB 14 158 := IsBB.of_search Φ₁ Ξ₂ (by native_decide)

end Bf
