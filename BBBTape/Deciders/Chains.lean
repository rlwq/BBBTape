import BBBTape.Deciders.Simulator
import BBBTape.Deciders.Windows
import BBBTape.Deciders.Translated
import BBBTape.Deciders.Blocks

namespace BBBTape

def Ξ₁ : Decider :=
  Decider.simulator WordTape 1000 <|> .windows 1 200 <|> .windows 2 200 <|> .windows 3 200

def Ξ₂ : Decider :=
  Decider.simulator WordTape 300 <|> .translatedUpTo 50 24 <|> .windows 1 200 <|>
    .translated 300 24 <|> .translatedUpTo 500 50 <|> .windows 2 200 <|> .blocksUpTo 2000 <|>
    .translated 2000 132 <|> .translated 2000 144

end BBBTape
