import Bf.Certificate
import Bf.Canonical
import Bf.Deciders.Simulator
import Bf.Deciders.Translated
import Bf.Deciders.Windows
import Bf.Deciders.Blocks

namespace Bf

def chain : Decider :=
  Decider.translatedUpTo 50 24 <|> .windows 1 200 <|> .translated 300 24 <|> .translatedUpTo 500 50 <|>
    .windows 2 200 <|> .blocksUpTo 2000

def bb0 : Certificate 0 0 := ⟨.canonical 0, chain, [], 0, 1000000000, by native_decide⟩
def bb1 : Certificate 1 1 := ⟨.canonical 1, chain, [], 1, 1000000000, by native_decide⟩
def bb2 : Certificate 2 2 := ⟨.canonical 2, chain, [], 2, 1000000000, by native_decide⟩
def bb3 : Certificate 3 3 := ⟨.canonical 3, chain, [], 3, 1000000000, by native_decide⟩
def bb4 : Certificate 4 4 := ⟨.canonical 4, chain, [], 4, 1000000000, by native_decide⟩
def bb5 : Certificate 5 5 := ⟨.canonical 5, chain, [], 5, 1000000000, by native_decide⟩
def bb6 : Certificate 6 8 := ⟨.canonical 6, chain, [], 8, 1000000000, by native_decide⟩
def bb7 : Certificate 7 10 := ⟨.canonical 7, chain, [], 10, 1000000000, by native_decide⟩
def bb8 : Certificate 8 14 := ⟨.canonical 8, chain, [], 14, 1000000000, by native_decide⟩
def bb9 : Certificate 9 18 := ⟨.canonical 9, chain, [], 18, 1000000000, by native_decide⟩
def bb10 : Certificate 10 30 := ⟨.canonical 10, chain, [], 30, 1000000000, by native_decide⟩
set_option maxHeartbeats 0 in
def bb11 : Certificate 11 35 := ⟨.canonical 11, chain, [], 35, 1000000000, by native_decide⟩
set_option maxHeartbeats 0 in
def bb12 : Certificate 12 72 := ⟨.canonical 12, chain, [], 72, 1000000000, by native_decide⟩

set_option maxHeartbeats 0 in
def bb13 : Certificate 13 120 := ⟨.canonical 13, chain <|> .translated 2000 144, [], 120, 1000000000, by native_decide⟩

set_option maxHeartbeats 0 in
def bb14 : Certificate 14 158 :=
  ⟨.canonical 14, chain <|> .translated 2000 132 <|> .translated 2000 144, [], 158, 1000000000, by native_decide⟩

#print axioms bb12
#print axioms bb13
#print axioms bb14

end Bf
