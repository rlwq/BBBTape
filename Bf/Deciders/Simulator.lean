import Bf.Decider

def deciderSimulator (n : Nat) (m : Machine) : Bool :=
  decide (m.run n).halted

theorem deciderSimulator_correct (n : Nat) (m : Machine) :
    deciderSimulator n m = true → m.halts := by
  intro h
  exists n
  unfold deciderSimulator at h
  exact of_decide_eq_true h

def simulator (n : Nat) : Decider where
  run p := if deciderSimulator n p.toMachine then .halts else .unknown
  sound_h p h := by
    by_cases hs : deciderSimulator n p.toMachine = true
    · exact deciderSimulator_correct n p.toMachine hs
    · simp [hs] at h
  sound_nh p h := by
    by_cases hs : deciderSimulator n p.toMachine = true <;> simp [hs] at h
