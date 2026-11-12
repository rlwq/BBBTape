import Bf.Print
import Bf.Decider
import Bf.Deciders.Simulator

def BusyBeaver (n s : Nat) : Prop :=
  (∃ p ∈ Program.enumerate n, p.toMachine.haltsIn s) ∧
  ∀ p ∈ Program.enumerate n, ∀ k, p.toMachine.haltsIn k → k ≤ s

theorem Decider.halts_of_all (d : Decider) {ps : List Program}
    (h : ∀ p ∈ ps, d.run p = .halts) : ∀ p ∈ ps, p.toMachine.halts :=
  fun p hp => d.sound_h p (h p hp)

theorem halts_len0 : ∀ p ∈ Program.enumerate 0, p.toMachine.halts :=
  (simulator 10).halts_of_all (by decide +kernel)

theorem halts_len1 : ∀ p ∈ Program.enumerate 1, p.toMachine.halts :=
  (simulator 10).halts_of_all (by decide +kernel)
