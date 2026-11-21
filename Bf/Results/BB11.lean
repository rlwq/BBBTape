import Bf.Core.Search
import Bf.Expanders.TNF
import Bf.Deciders.Chains

namespace Bf

theorem bb11 : IsBB 11 35 := IsBB.of_search Φ₁ Ξ₁ (by native_decide)

end Bf
