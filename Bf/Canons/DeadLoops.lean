import Bf.Canon
import Bf.Simulation

namespace Bf

namespace Program

def deadMass : Program → Nat
  | loop b p => b.size + p.deadMass
  | _        => 0

inductive DeadMode where
  | live
  | dead
  | chain

def canonDead : DeadMode → Program → Program
  | _,      nil      => nil
  | _,      left p   => left (canonDead .live p)
  | _,      right p  => right (canonDead .live p)
  | _,      flip p   => flip (canonDead .live p)
  | .live,  loop b p => loop (canonDead .live b) (canonDead .dead p)
  | .dead,  loop b p => loop (stars (b.size + p.deadMass)) (canonDead .chain p)
  | .chain, loop _ p => loop nil (canonDead .chain p)

theorem size_canonDead (p : Program) (m : DeadMode) :
    (canonDead m p).size + (match m with | .chain => p.deadMass | _ => 0) = p.size := by
  induction p generalizing m with
  | nil => cases m <;> rfl
  | left p ih | right p ih | flip p ih =>
    have := ih .live
    cases m <;> simp only [canonDead, size, deadMass] at * <;> omega
  | loop b p ihb ih =>
    have := ihb .live; have := ih .dead; have := ih .chain
    cases m <;> simp only [canonDead, size, deadMass, size_stars] at * <;> omega

inductive DeadRel : Bool → Program → Program → Prop
  | nil   {z : Bool} : DeadRel z nil nil
  | left  {z : Bool} {p q : Program} : DeadRel false p q → DeadRel z (left p) (left q)
  | right {z : Bool} {p q : Program} : DeadRel false p q → DeadRel z (right p) (right q)
  | flip  {z : Bool} {p q : Program} : DeadRel false p q → DeadRel z (flip p) (flip q)
  | loop  {z : Bool} {b b' p q : Program} :
      DeadRel false b b' → DeadRel true p q → DeadRel z (loop b p) (loop b' q)
  | dead  {b b' p q : Program} : DeadRel true p q → DeadRel true (loop b p) (loop b' q)

theorem DeadRel.weaken {p q : Program} (h : DeadRel false p q) : DeadRel true p q := by
  cases h with
  | nil => exact .nil
  | left h => exact .left h
  | right h => exact .right h
  | flip h => exact .flip h
  | loop hb hp => exact .loop hb hp

theorem DeadRel.append {z : Bool} {b b' x x' : Program} (hb : DeadRel z b b')
    (hx : DeadRel false x x') : DeadRel z (b ++ x) (b' ++ x') := by
  induction hb with
  | @nil z => cases z <;> first | exact hx | exact hx.weaken
  | left _ ih => exact .left ih
  | right _ ih => exact .right ih
  | flip _ ih => exact .flip ih
  | loop hb _ _ ih => exact .loop hb ih
  | dead _ ih => exact .dead ih

theorem deadRel_canonDead (p : Program) (m : DeadMode) :
    DeadRel (match m with | .live => false | _ => true) p (canonDead m p) := by
  induction p generalizing m with
  | nil => cases m <;> exact .nil
  | left p ih => cases m <;> exact .left (ih .live)
  | right p ih => cases m <;> exact .right (ih .live)
  | flip p ih => cases m <;> exact .flip (ih .live)
  | loop b p ihb ih =>
    cases m
    · exact .loop (ihb .live) (ih .dead)
    · exact .dead (ih .chain)
    · exact .dead (ih .chain)

def DeadConf (c d : Config) : Prop :=
  c.tape = d.tape ∧ ∃ z : Bool, DeadRel z c.prog d.prog ∧ (z = true → c.tape.head = false)

theorem DeadConf.sim : Config.Simulation DeadConf := by
  rintro ⟨t, p⟩ ⟨_, q⟩ ⟨rfl, z, hr, hz⟩
  cases hr with
  | nil => exact .inl ⟨rfl, rfl⟩
  | left h => exact .inr ⟨1, _, _, by omega, rfl, rfl, rfl, false, h, nofun⟩
  | right h => exact .inr ⟨1, _, _, by omega, rfl, rfl, rfl, false, h, nofun⟩
  | flip h => exact .inr ⟨1, _, _, by omega, rfl, rfl, rfl, false, h, nofun⟩
  | @loop _ b b' p q hb hp =>
    refine .inr ⟨1, _, _, by omega, rfl, rfl, rfl, ?_⟩
    cases hh : t.head
    · exact ⟨true, by simpa [hh] using hp, fun (_ : true = true) => rfl⟩
    · exact ⟨false, by simpa [hh] using hb.append (.loop hb hp), nofun⟩
  | dead hp =>
    have hh : t.head = false := hz rfl
    exact .inr ⟨1, _, _, by omega, rfl, rfl, rfl, true, by simpa [hh] using hp,
      fun (_ : true = true) => hh⟩

end Program

def Canon.deadLoops : Canon where
  f := Program.canonDead .dead
  size_eq := fun (p : Program) => by simpa using Program.size_canonDead p .dead
  sound := fun (p : Program) => Program.DeadConf.sim.sameTime
    ⟨rfl, true, Program.deadRel_canonDead p .dead, fun (_ : true = true) => rfl⟩

end Bf
