import Bf.Certificate
import Bf.Generators.Trivial
import Bf.Canons.All
import Bf.Deciders.LoopFree
import Bf.Deciders.Simulator
import Bf.Deciders.Translated
import Bf.Deciders.Reduce
import Bf.Solved.Bouncer
import Bf.Solved.JumpBouncer
import Bf.Solved.StepBouncer
import Bf.Solved.Bouncers11
import Bf.Solved.HoleBouncer
import Bf.Solved.Dilated

namespace Bf

def bb0 : Certificate 0 0 where
  generator := .trivial
  canon     := .all
  decider   := .simulator 0
  manual    := []
  check     := by native_decide

def bb1 : Certificate 1 1 where
  generator := .trivial
  canon     := .all
  decider   := .simulator 1
  manual    := []
  check     := by native_decide

def bb2 : Certificate 2 2 where
  generator := .trivial
  canon     := .all
  decider   := .simulator 2
  manual    := []
  check     := by native_decide

def bb3 : Certificate 3 3 where
  generator := .trivial
  canon     := .all
  decider   := Decider.simulator 3 <|> .translatedUpTo 4 4
  manual    := []
  check     := by native_decide

def bb4 : Certificate 4 4 where
  generator := .trivial
  canon     := .all
  decider   := Decider.simulator 4 <|> .translatedUpTo 4 4
  manual    := []
  check     := by native_decide

def bb5 : Certificate 5 5 where
  generator := .trivial
  canon     := .all
  decider   := Decider.simulator 5 <|> .translatedUpTo 10 6
  manual    := []
  check     := by native_decide

def bb6 : Certificate 6 8 where
  generator := .trivial
  canon     := .all
  decider   := Decider.simulator 8 <|> .translatedUpTo 20 10
  manual    := []
  check     := by native_decide

def bb7 : Certificate 7 10 where
  generator := .trivial
  canon     := .all
  decider   := Decider.simulator 10 <|> .translatedUpTo 30 16
  manual    := []
  check     := by native_decide

def bb8 : Certificate 8 14 where
  generator := .trivial
  canon     := .all
  decider   := Decider.simulator 14 <|> .translatedUpTo 50 24 <|> .translated 300 24
  manual    := []
  check     := by native_decide

def bb9 : Certificate 9 18 where
  generator := .trivial
  canon     := .all
  decider   := Decider.simulator 18 <|> .translatedUpTo 50 24 <|> .translated 300 24
  manual    := [Solved.Bouncer.solved]
  check     := by native_decide

def known : List Solved :=
  [Solved.Bouncer.solved, Solved.JumpBouncer.solved, Solved.StepBouncer.solved]

set_option maxHeartbeats 0 in
def bb10 : Certificate 10 30 where
  generator := .trivial
  canon     := .all
  decider   := Decider.simulator 30 <|> .translatedUpTo 50 24 <|> .translated 300 24 <|>
    .translatedUpTo 500 50 <|> .reduce known 3
  manual    := known
  check     := by native_decide

def known11 : List Solved :=
  known ++ Solved.Bouncers11.all ++ [Solved.HoleBouncer.solved, Solved.Dilated.solved]

set_option maxHeartbeats 0 in
def bb11 : Certificate 11 35 where
  generator := .trivial
  canon     := .all
  decider   := Decider.simulator 35 <|> .translatedUpTo 50 24 <|> .translated 300 24 <|>
    .translatedUpTo 500 50 <|> .reduce known11 3
  manual    := known11
  check     := by native_decide

#print axioms Bf.bb0
#print axioms Bf.bb1
#print axioms Bf.bb2
#print axioms Bf.bb3
#print axioms Bf.bb4
#print axioms Bf.bb5
#print axioms Bf.bb6
#print axioms Bf.bb7
#print axioms Bf.bb8
#print axioms Bf.bb9
#print axioms Bf.bb10
#print axioms Bf.bb11

end Bf
