import Bf.Search

namespace Bf

open scoped Program

structure Certificate (n B : Nat) where
  expander : Expander
  decider  : Decider
  witness  : Program
  check    : search expander decider B (Program.gap? n) = [] ∧
    witness° ∧ ‖witness‖ = n ∧ decider.run witness = .halts B

theorem Certificate.isBB {n v : Nat} (C : Certificate n v) : IsBB n v := by
  obtain ⟨hs, hc, hn, hr⟩ := C.check
  have hroot : Bounded v (Program.gap? n) :=
    search_bounded (e := C.expander) (d := C.decider) _ (by
      rw [hs]
      intro r hr
      cases hr)
  have hw := C.decider.sound C.witness
  rw [hr] at hw
  exact ⟨fun ⟨p, hp, hsz⟩ k hk => hroot.upper p k hp hsz hk, ⟨C.witness, hc, hn⟩, hw⟩

end Bf
