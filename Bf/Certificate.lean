import Std.Data.HashSet
import Bf.BB
import Bf.Canon
import Bf.Generator
import Bf.Solved

namespace Bf

deriving instance Hashable for Program

def dedup (ps : List Program) : List Program :=
  (ps.foldl (fun (s : Std.HashSet Program) (p : Program) => s.insert p) ∅).toList

theorem mem_dedup {ps : List Program} {a : Program} : a ∈ dedup ps ↔ a ∈ ps := by
  have h : ∀ (qs : List Program) (s : Std.HashSet Program),
      a ∈ qs.foldl (fun (s : Std.HashSet Program) (p : Program) => s.insert p) s ↔ a ∈ s ∨ a ∈ qs := by
    intro qs
    induction qs with
    | nil => intro s; simp
    | cons q qs ih =>
      intro s
      rw [List.foldl_cons, ih, Std.HashSet.mem_insert, beq_iff_eq, List.mem_cons]
      constructor
      · rintro ((rfl | h) | h)
        · exact .inr (.inl rfl)
        · exact .inl h
        · exact .inr (.inr h)
      · rintro (h | rfl | h)
        · exact .inl (.inr h)
        · exact .inl (.inl rfl)
        · exact .inr h
  unfold dedup
  rw [Std.HashSet.mem_toList, h]
  simp [Std.HashSet.not_mem_empty]

def Generator.reps (g : Generator) (c : Canon) (n : Nat) : List Program :=
  dedup ((g.gen n).map c.f)

theorem Generator.size_of_mem_reps (g : Generator) (c : Canon) {n : Nat} {a : Program}
    (ha : a ∈ g.reps c n) : a.size = n := by
  simp only [reps, mem_dedup, List.mem_map] at ha
  obtain ⟨q, hq, rfl⟩ := ha
  rw [c.size_eq, g.size hq]

theorem Generator.cover_reps (g : Generator) (c : Canon) (p : Program) :
    ∃ a ∈ g.reps c p.size, p.SameTime a := by
  obtain ⟨q, hq, hpq⟩ := g.cover p
  refine ⟨c.f q, ?_, hpq.trans (c.sound q)⟩
  simp only [reps, mem_dedup, List.mem_map]
  exact ⟨q, hq, rfl⟩

structure Certificate (n s : Nat) where
  generator : Generator
  canon     : Canon
  decider   : Decider
  manual    : List Solved
  check     : (decider <|> Solved.decider manual).summary (generator.reps canon n) = .halts s

theorem Certificate.isBB {n s : Nat} (C : Certificate n s) : IsBB n s := by
  obtain ⟨⟨a, ha, hs⟩, hmax⟩ := Decider.summary_halts C.check
  refine ⟨⟨a, C.generator.size_of_mem_reps C.canon ha, hs⟩, ?_⟩
  rintro k ⟨p, rfl, hk⟩
  obtain ⟨b, hb, hpb⟩ := C.generator.cover_reps C.canon p
  exact hmax b hb k ((hpb k).mp hk)

end Bf
