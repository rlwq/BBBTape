import Bf.Certificate
import Bf.Syntax
import Bf.Simulator
import Bf.Windows
import Bf.Translated
import Bf.Blocks

namespace Bf

def chain : Decider :=
  Decider.simulator Zipper 1000 <|> .windows 1 200 <|> .windows 2 200 <|> .windows 3 200

def fullChain : Decider :=
  Decider.simulator Zipper 300 <|> .translatedUpTo 50 24 <|> .windows 1 200 <|>
    .translated 300 24 <|> .translatedUpTo 500 50 <|> .windows 2 200 <|> .blocksUpTo 2000 <|>
    .translated 2000 132 <|> .translated 2000 144

theorem bb0  : IsBB 0  0  := Certificate.isBB ⟨.tnf, chain, bf"",            by native_decide⟩
theorem bb1  : IsBB 1  1  := Certificate.isBB ⟨.tnf, chain, bf"<",           by native_decide⟩
theorem bb2  : IsBB 2  2  := Certificate.isBB ⟨.tnf, chain, bf"<<",          by native_decide⟩
theorem bb3  : IsBB 3  3  := Certificate.isBB ⟨.tnf, chain, bf"<<<",         by native_decide⟩
theorem bb4  : IsBB 4  4  := Certificate.isBB ⟨.tnf, chain, bf"<<<<",        by native_decide⟩
theorem bb5  : IsBB 5  5  := Certificate.isBB ⟨.tnf, chain, bf"<<<<<",       by native_decide⟩
theorem bb6  : IsBB 6  8  := Certificate.isBB ⟨.tnf, chain, bf"*<*[>]",      by native_decide⟩
theorem bb7  : IsBB 7  10 := Certificate.isBB ⟨.tnf, chain, bf"*<*[*>]",     by native_decide⟩
theorem bb8  : IsBB 8  14 := Certificate.isBB ⟨.tnf, chain, bf"*[<<*>*]",    by native_decide⟩
theorem bb9  : IsBB 9  18 := Certificate.isBB ⟨.tnf, chain, bf"*[[<]>>*]",   by native_decide⟩
theorem bb10 : IsBB 10 30 := Certificate.isBB ⟨.tnf, chain, bf"*[<*[>]<<]",  by native_decide⟩
theorem bb11 : IsBB 11 35 := Certificate.isBB ⟨.tnf, chain, bf"*[<*[>]*<<]", by native_decide⟩

end Bf
