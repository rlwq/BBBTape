import Bf.Deciders.Simulator
import Bf.Deciders.Windows
import Bf.Deciders.Translated
import Bf.Deciders.Blocks

namespace Bf

def Ξ₁ : Decider :=
  Decider.simulator Zipper 1000 <|> .windows 1 200 <|> .windows 2 200 <|> .windows 3 200

def Ξ₂ : Decider :=
  Decider.simulator Zipper 300 <|> .translatedUpTo 50 24 <|> .windows 1 200 <|>
    .translated 300 24 <|> .translatedUpTo 500 50 <|> .windows 2 200 <|> .blocksUpTo 2000 <|>
    .translated 2000 132 <|> .translated 2000 144

end Bf
