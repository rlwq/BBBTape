import Bf.Results

namespace Bf

theorem bb12 : IsBB 12 72 := Certificate.isBB ⟨.tnf, fullChain, bf"*[<*[>>*>]<]", by native_decide⟩

end Bf
