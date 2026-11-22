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

def Ξ₃ : Decider :=
  Ξ₂ <|> .windows 3 200 <|> .windows 4 500 <|> .windows 5 500 <|>
    .blocks 4 2 2000 <|> .translated 2000 154 <|> .translated 2000 156 <|>
    .translated 3000 164 <|> .translated 4000 198

def Ξ₄ : Decider :=
  Decider.simulator WordTape 400 <|>
    Ξ₃ <|>
    .phased 2 1 200 <|> .phased 2 3 200 <|>
    .windows 6 500 <|> .windows 7 500 <|> .windows 8 500 <|> .windows 13 1500 <|>
    .blocks 6 2 2000 <|> .translated 2000 150 <|> .translated 2000 160 <|>
    .translated 5000 145 <|> .translated 5000 171

def Ξ₅ : Decider :=
  Ξ₄ <|> .phased 3 2 200 <|> .simulator WordTape 1000 <|>
    .blocks 2 3 20000 <|> .blocks 3 2 20000 <|> .blocks 3 3 20000 <|> .blocks 5 2 20000 <|>
    .blocks 6 2 20000 <|> .blocks 8 2 20000 <|> .windows 16 3000

end BBBTape
