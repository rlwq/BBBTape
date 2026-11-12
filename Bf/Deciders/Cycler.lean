import Bf.Lemmas
import Bf.Decider

def cyclerDecider (k n : Nat) : Decider where
  run p :=
    let m₁ := p.toMachine.run k
    let m₂ := m₁.run n
    if 0 < n ∧ ¬ m₁.halted ∧ m₂.program = m₁.program ∧ m₂.tape.AgreeOn (k + n) m₁.tape
    then .nonhalts else .unknown
  sound_h p h := by
    by_cases hc : 0 < n ∧ ¬ (p.toMachine.run k).halted ∧
        ((p.toMachine.run k).run n).program = (p.toMachine.run k).program ∧
        ((p.toMachine.run k).run n).tape.AgreeOn (k + n) (p.toMachine.run k).tape
      <;> simp [hc] at h
  sound_nh p h hp := by
    by_cases hc : 0 < n ∧ ¬ (p.toMachine.run k).halted ∧
        ((p.toMachine.run k).run n).program = (p.toMachine.run k).program ∧
        ((p.toMachine.run k).run n).tape.AgreeOn (k + n) (p.toMachine.run k).tape
    · obtain ⟨hn, hm, hprog, ha⟩ := hc
      have z₁ := p.toMachine.zeroBeyond_run 0 k Tape.zeroBeyond_blank
      have z₂ := (p.toMachine.run k).zeroBeyond_run (0 + k) n z₁
      have ht : ((p.toMachine.run k).run n).tape = (p.toMachine.run k).tape :=
        Tape.eq_of_agreeOn ha (z₂.mono (by omega)) (z₁.mono (by omega))
      exact (p.toMachine.run k).not_halts_of_cycle n hn hm (Machine.ext ht hprog)
        (p.toMachine.halts_run k hp)
    · simp [hc] at h
