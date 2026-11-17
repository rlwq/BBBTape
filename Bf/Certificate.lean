import Bf.Search
import Bf.Solved

namespace Bf

structure Certificate (n s : Nat) where
  brancher : Brancher
  decider  : Decider
  manual   : List Solved
  limit    : Nat
  fuel     : Nat
  check    : search brancher (decider <|> Solved.decider manual) limit n fuel [(.hole 0 n, 1)] none =
    some (some s)

theorem Certificate.isBB {n s : Nat} (C : Certificate n s) : IsBB n s := by
  refine ⟨search_reach C.check (fun (b : Nat) (hb : none = some b) => by cases hb) s rfl, ?_⟩
  rintro k ⟨p, hc, hs, hk⟩
  obtain ⟨p', hP, hc', hs', hst⟩ := C.brancher.norm p hc
  obtain ⟨b, hb, hkb⟩ := search_bound C.check p' hP
    (.inl ⟨_, List.mem_singleton_self _, .hole 0 hc' (hs'.trans hs)⟩) k ((hst k).mp hk)
  cases hb
  exact hkb

end Bf
