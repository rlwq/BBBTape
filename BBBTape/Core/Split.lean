import BBBTape.Core.Search
import BBBTape.Core.Statement

namespace BBBTape

open scoped Program Machine

def frontier (e : Expander) (d : Decider) : Nat → Program → List Program
  | 0,     q => [q]
  | k + 1, q =>
    match d q with
    | .stuck i => (e.expand q i).flatMap (frontier e d k)
    | _        => [q]

theorem bounded_of_frontier {e : Expander} {d : Decider} {B : Nat} :
    ∀ (k : Nat) (q : Program), (∀ r ∈ frontier e d k q, Bounded B r) → Bounded B q
  | 0,     q, h => h q (List.mem_singleton_self q)
  | k + 1, q, h => by
    simp only [frontier] at h
    split at h
    · next i _ =>
      exact Bounded.of_expand (e := e) i fun c hc =>
        bounded_of_frontier k c fun r hr => h r (List.mem_flatMap.mpr ⟨c, hc, hr⟩)
    · exact h q (List.mem_singleton_self q)

def hashPart (nodes : List Program) (P j : Nat) : List Program :=
  nodes.filter fun q => (hash q).toNat % P == j

theorem bounded_of_hashParts {e : Expander} {d : Decider} {B : Nat} (k : Nat) {q₀ : Program}
    {P : Nat} (hP : 0 < P) {nodes : List Program} (hn : frontier e d k q₀ = nodes)
    (hparts : ∀ j, j < P → ∀ q ∈ hashPart nodes P j, Bounded B q) : Bounded B q₀ :=
  bounded_of_frontier k q₀ fun q hq =>
    hparts ((hash q).toNat % P) (Nat.mod_lt _ hP) q (List.mem_filter.mpr ⟨hn ▸ hq, by simp⟩)

def Outcome.within (B : Nat) (o : Outcome) : Bool :=
  o.holdouts.isEmpty && o.longest.all (·.1 ≤ B)

theorem Bounded.of_within {e : Expander} {d : Decider} {B : Nat} {q : Program}
    (h : (search e d q).within B = true) : Bounded B q := by
  simp only [Outcome.within, Bool.and_eq_true, List.isEmpty_iff, Option.all_eq_true,
    decide_eq_true_eq] at h
  exact search_bounded q (fun r hr => by rw [h.1] at hr; exact nomatch hr) h.2

theorem Bounded.of_all_within {e : Expander} {d : Decider} {B : Nat} {qs : List Program}
    (h : qs.all (fun q => (search e d q).within B) = true) : ∀ q ∈ qs, Bounded B q :=
  fun q hq => Bounded.of_within (List.all_eq_true.mp h q hq)

theorem IsBB.of_bounded {e : Expander} {d : Decider} {n B : Nat} (c : Program)
    (hc : (search e d c).longest = some (B, c)) (hcl : c°) (hsz : ‖c‖ = n)
    (hb : Bounded B (ω n)) : IsBB n B :=
  ⟨fun ⟨p, hp, hpn⟩ k hk => hb.upper p k hp hpn hk,
    ⟨⟨c, hcl, hsz⟩, (search_longest c hc).1⟩⟩

end BBBTape
