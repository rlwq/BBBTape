import Std.Data.HashSet
import Bf.Decider
import Bf.Zipper

namespace Bf

namespace Blocks

open scoped Program Machine

abbrev Run : Type := List Bool × Nat

def Fits (T c k : Nat) : Prop := 1 ≤ k ∧ (c < T → k = c) ∧ (T ≤ c → T ≤ k)

inductive Expand (T : Nat) : List Run → List Bool → Prop
  | nil : Expand T [] []
  | cons {b : List Bool} {c k : Nat} {rest : List Run} {l : List Bool} :
      Fits T c k → Expand T rest l → Expand T ((b, c) :: rest) ((List.replicate k b).flatten ++ l)

structure St where
  prog  : Program
  left  : List Run
  cur   : List Bool
  off   : Nat
  right : List Run
  deriving DecidableEq, Hashable

def push (T : Nat) (blk : List Bool) : List Run → List Run
  | []            => [(blk, 1)]
  | (b, c) :: rest => if b = blk then (b, min (c + 1) T) :: rest else (blk, 1) :: (b, c) :: rest

def pops (B T : Nat) : List Run → List (List Bool × List Run)
  | []             => [(List.replicate B false, [])]
  | (b, c) :: rest =>
    if c = 1 then [(b, rest)]
    else if c < T then [(b, (b, c - 1) :: rest)]
    else [(b, (b, c) :: rest), (b, (b, T - 1) :: rest)]

def succs (B T : Nat) (s : St) : List St :=
  match s.prog with
  | ε        => []
  | .gap _ _ _ => []
  | .flip p   => [⟨p, s.left, s.cur.set s.off (!s.cur.getD s.off false), s.off, s.right⟩]
  | .loop b q => [⟨if s.cur.getD s.off false then b ++ .loop b q else q, s.left, s.cur, s.off, s.right⟩]
  | .right p  =>
    if s.off + 1 < B then [⟨p, s.left, s.cur, s.off + 1, s.right⟩]
    else (pops B T s.right).map fun (x : List Bool × List Run) => ⟨p, push T s.cur.reverse s.left, x.1, 0, x.2⟩
  | .left p   =>
    if 0 < s.off then [⟨p, s.left, s.cur, s.off - 1, s.right⟩]
    else (pops B T s.left).map fun (x : List Bool × List Run) => ⟨p, x.2, x.1.reverse, B - 1, push T s.cur s.right⟩

def closed (B T : Nat) (S : Std.HashSet St) : Bool :=
  decide (2 ≤ T) && S.toList.all fun (s : St) =>
    s.prog.alive && s.cur.length == B && decide (s.off < B) &&
      (s.left ++ s.right).all (fun (x : Run) => x.1.length == B) && (succs B T s).all S.contains

def Rep (T : Nat) (S : Std.HashSet St) (c : Machine Zipper) : Prop :=
  ∃ s : St, s ∈ S ∧ s.prog = c.prog ∧ c.tape.head = s.cur.getD s.off false ∧
    (∃ l : List Bool, Expand T s.left l ∧
      ∀ i : Nat, c.tape.left.getD i false = ((s.cur.take s.off).reverse ++ l).getD i false) ∧
    (∃ r : List Bool, Expand T s.right r ∧
      ∀ i : Nat, c.tape.right.getD i false = (s.cur.drop (s.off + 1) ++ r).getD i false)

theorem getD_replicate_false (B i : Nat) : (List.replicate B false).getD i false = false := by
  induction B generalizing i with
  | zero => simp
  | succ B ih =>
    cases i with
    | zero => simp [List.replicate_succ]
    | succ i => rw [List.replicate_succ, List.getD_cons_succ]; exact ih i

theorem getD_reverse_last (a : List Bool) (h : a ≠ []) : a.reverse.getD (a.length - 1) false = a.getD 0 false := by
  cases a with
  | nil => exact absurd rfl h
  | cons y a => simp [List.getD_eq_getElem?_getD]

theorem headD_eq (l : List Bool) : l.headD false = l.getD 0 false := by
  cases l <;> rfl

theorem getD_succ_append (a b : List Bool) (h : a ≠ []) (i : Nat) :
    (a ++ b).getD (i + 1) false = (a.drop 1 ++ b).getD i false := by
  cases a with
  | nil => exact absurd rfl h
  | cons x a => simp

theorem getD_zero_append (a b : List Bool) (h : a ≠ []) : (a ++ b).getD 0 false = a.getD 0 false := by
  cases a with
  | nil => exact absurd rfl h
  | cons x a => simp

theorem take_succ_reverse (l : List Bool) (n : Nat) (h : n < l.length) :
    (l.take (n + 1)).reverse = l.getD n false :: (l.take n).reverse := by
  rw [List.take_add_one, List.getElem?_eq_getElem h, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  simp

theorem drop_eq_cons (l : List Bool) (n : Nat) (h : n < l.length) :
    l.drop n = l.getD n false :: l.drop (n + 1) := by
  rw [List.drop_eq_getElem_cons h, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

theorem reverse_take_pred (a : List Bool) : (a.reverse.take (a.length - 1)).reverse = a.drop 1 := by
  cases a with
  | nil => rfl
  | cons y a =>
    simp only [List.reverse_cons, List.length_cons, Nat.add_sub_cancel, List.drop_succ_cons, List.drop_zero]
    rw [List.take_append_of_le_length (by simp), List.take_of_length_le (by simp), List.reverse_reverse]

theorem expand_push {T : Nat} (blk : List Bool) {L : List Run} {l : List Bool} (h : Expand T L l) :
    Expand T (push T blk L) (blk ++ l) := by
  cases h with
  | nil =>
    have := Expand.cons (b := blk) (c := 1) (k := 1) (T := T) ⟨Nat.le_refl 1, fun _ => rfl, fun h => h⟩ Expand.nil
    simpa [push] using this
  | @cons b c k rest l' hf he =>
    simp only [push]
    split
    · next hb =>
      subst hb
      have hf' : Fits T (min (c + 1) T) (k + 1) := by
        obtain ⟨h1, h2, h3⟩ := hf
        refine ⟨by omega, fun h => ?_, fun h => ?_⟩
        · have : c + 1 < T := by omega
          have := h2 (by omega); omega
        · by_cases hc : c < T
          · have := h2 hc; omega
          · have := h3 (by omega); omega
      have := Expand.cons (b := b) hf' he
      simpa [List.replicate_succ] using this
    · have := Expand.cons (b := blk) (c := 1) (k := 1) (T := T) ⟨Nat.le_refl 1, fun _ => rfl, fun h => h⟩
        (Expand.cons (b := b) hf he)
      simpa using this

theorem expand_pop {B T : Nat} (hT : 2 ≤ T) {R : List Run} {r : List Bool} (h : Expand T R r)
    (hB : ∀ x ∈ R, x.1.length = B) :
    ∃ x ∈ pops B T R, x.1.length = B ∧ ∃ r' : List Bool, Expand T x.2 r' ∧
      ∀ i : Nat, r.getD i false = (x.1 ++ r').getD i false := by
  cases h with
  | nil =>
    exact ⟨_, List.mem_singleton_self _, by simp, [], Expand.nil, fun (i : Nat) => by
      rw [List.append_nil, getD_replicate_false]; simp⟩
  | @cons b c k rest l hf he =>
    have hb : b.length = B := hB _ (List.mem_cons_self ..)
    obtain ⟨h1, h2, h3⟩ := hf
    have hk : List.replicate k b = b :: List.replicate (k - 1) b := by
      rw [← List.replicate_succ, Nat.sub_add_cancel h1]
    have e : ((List.replicate k b).flatten ++ l) = b ++ ((List.replicate (k - 1) b).flatten ++ l) := by
      rw [hk]; simp
    rw [e]
    unfold pops
    by_cases hc1 : c = 1
    · subst hc1
      have : k = 1 := h2 (by omega)
      subst this
      exact ⟨(b, rest), by simp, hb, l, he, fun (i : Nat) => by simp⟩
    · by_cases hcT : c < T
      · have hkc := h2 hcT
        refine ⟨(b, (b, c - 1) :: rest), by simp [hc1, hcT], hb, _, Expand.cons ⟨by omega, fun _ => by omega, fun _ => by omega⟩ he,
          fun (i : Nat) => rfl⟩
      · have hk3 := h3 (by omega)
        by_cases hkT : T ≤ k - 1
        · exact ⟨(b, (b, c) :: rest), by simp [hc1, hcT], hb, _,
            Expand.cons ⟨by omega, fun h => absurd h hcT, fun _ => hkT⟩ he, fun (i : Nat) => rfl⟩
        · exact ⟨(b, (b, T - 1) :: rest), by simp [hc1, hcT], hb, _,
            Expand.cons ⟨by omega, fun _ => by omega, fun _ => by omega⟩ he, fun (i : Nat) => rfl⟩

theorem Rep.step {B T : Nat} {S : Std.HashSet St} (hc : closed B T S = true) {c : Machine Zipper}
    (h : Rep T S c) : ∃ c' : Machine Zipper, c⇒ = some c' ∧ Rep T S c' := by
  obtain ⟨s, hS, hp, hh, ⟨l, hl, hL⟩, ⟨r, hr, hR⟩⟩ := h
  simp only [closed, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hc
  obtain ⟨hT, hall⟩ := hc
  have hs := hall s (Std.HashSet.mem_toList.mpr hS)
  simp only [beq_iff_eq, List.mem_append] at hs
  obtain ⟨⟨⟨⟨halive, hlen⟩, hoff⟩, hblk⟩, hsucc₀⟩ := hs
  have hsucc : ∀ x ∈ succs B T s, x ∈ S := fun (x : St) (hx : x ∈ succs B T s) =>
    Std.HashSet.mem_iff_contains.mpr (hsucc₀ x hx)
  obtain ⟨t, p⟩ := c
  obtain ⟨q, L, cur, off, R⟩ := s
  simp only at hp hh hL hR hlen hoff hblk halive hsucc
  subst hp
  have hR' : ∀ x ∈ R, x.1.length = B := fun (x : Run) (hx : x ∈ R) => hblk x (Or.inr hx)
  have hL' : ∀ x ∈ L, x.1.length = B := fun (x : Run) (hx : x ∈ L) => hblk x (Or.inl hx)
  cases q with
  | nil => simp [Program.alive] at halive
  | gap => simp [Program.alive] at halive
  | flip p =>
    refine ⟨⟨t.flip, p⟩, rfl, ⟨p, L, cur.set off (!cur.getD off false), off, R⟩,
      hsucc _ (by simp [succs]), rfl, ?_, ⟨l, hl, fun (i : Nat) => ?_⟩, ⟨r, hr, fun (i : Nat) => ?_⟩⟩
    · show (!t.head) = _
      rw [List.getD_eq_getElem?_getD, List.getElem?_set_self (by omega), hh]
      rfl
    · show t.left.getD i false = _
      rw [List.take_set_of_le (Nat.le_refl off)]; exact hL i
    · show t.right.getD i false = _
      rw [List.drop_set_of_lt (by omega : off < off + 1)]; exact hR i
  | loop b q =>
    refine ⟨⟨t, if t.head then b ++ .loop b q else q⟩, rfl,
      ⟨if cur.getD off false then b ++ .loop b q else q, L, cur, off, R⟩,
      hsucc _ (by simp [succs]), ?_, hh, ⟨l, hl, hL⟩, ⟨r, hr, hR⟩⟩
    show (if cur.getD off false then b ++ .loop b q else q) = (if t.head then b ++ .loop b q else q)
    rw [hh]
  | right p =>
    by_cases ho : off + 1 < B
    · refine ⟨⟨t.moveR, p⟩, rfl, ⟨p, L, cur, off + 1, R⟩, hsucc _ (by simp [succs, ho]), rfl, ?_,
        ⟨l, hl, fun (i : Nat) => ?_⟩, ⟨r, hr, fun (i : Nat) => ?_⟩⟩
      · show t.right.headD false = _
        rw [headD_eq, hR 0, drop_eq_cons cur (off + 1) (by omega)]; rfl
      · show (t.head :: t.left).getD i false = _
        rw [take_succ_reverse cur off (by omega)]
        cases i with
        | zero => simpa using hh
        | succ i => simpa using hL i
      · show t.right.tail.getD i false = _
        rw [Zipper.getD_tail, hR (i + 1), drop_eq_cons cur (off + 1) (by omega)]; rfl
    · have hoB : off + 1 = B := by omega
      obtain ⟨x, hx, hxl, r', hr', hrr⟩ := expand_pop hT hr hR'
      have hx0 : x.1 ≠ [] := by intro e; rw [e] at hxl; simp at hxl; omega
      have hd : cur.drop (off + 1) = [] := by simp; omega
      refine ⟨⟨t.moveR, p⟩, rfl, ⟨p, push T cur.reverse L, x.1, 0, x.2⟩,
        hsucc _ (by simp only [succs, ho, ite_false, List.mem_map]; exact ⟨x, hx, rfl⟩), rfl, ?_,
        ⟨_, expand_push cur.reverse hl, fun (i : Nat) => ?_⟩, ⟨r', hr', fun (i : Nat) => ?_⟩⟩
      · show t.right.headD false = _
        rw [headD_eq, hR 0, hd, List.nil_append, hrr 0, getD_zero_append _ _ hx0]
      · show (t.head :: t.left).getD i false = _
        have hc : cur.reverse = (cur.take (off + 1)).reverse := by rw [List.take_of_length_le (by omega)]
        rw [List.take_zero, List.reverse_nil, List.nil_append, hc,
          take_succ_reverse cur off (by omega)]
        cases i with
        | zero => simpa using hh
        | succ i => simpa using hL i
      · show t.right.tail.getD i false = _
        rw [Zipper.getD_tail, hR (i + 1), hd, List.nil_append, hrr (i + 1), getD_succ_append _ _ hx0]
  | left p =>
    by_cases ho : 0 < off
    · refine ⟨⟨t.moveL, p⟩, rfl, ⟨p, L, cur, off - 1, R⟩, hsucc _ (by simp [succs, ho]), rfl, ?_,
        ⟨l, hl, fun (i : Nat) => ?_⟩, ⟨r, hr, fun (i : Nat) => ?_⟩⟩
      · show t.left.headD false = _
        rw [headD_eq, hL 0, show off = (off - 1) + 1 by omega, take_succ_reverse cur (off - 1) (by omega)]
        simp
      · show t.left.tail.getD i false = _
        rw [Zipper.getD_tail, hL (i + 1), show off = (off - 1) + 1 by omega,
          take_succ_reverse cur (off - 1) (by omega)]
        simp
      · show (t.head :: t.right).getD i false = _
        rw [show off - 1 + 1 = off by omega, drop_eq_cons cur off (by omega)]
        cases i with
        | zero => simpa using hh
        | succ i => simpa using hR i
    · have ho0 : off = 0 := by omega
      subst ho0
      obtain ⟨x, hx, hxl, l', hl', hll⟩ := expand_pop hT hl hL'
      have hx0 : x.1 ≠ [] := by intro e; rw [e] at hxl; simp at hxl; omega
      refine ⟨⟨t.moveL, p⟩, rfl, ⟨p, x.2, x.1.reverse, B - 1, push T cur R⟩,
        hsucc _ (by simp only [succs, ho, ite_false, List.mem_map]; exact ⟨x, hx, rfl⟩), rfl, ?_,
        ⟨l', hl', fun (i : Nat) => ?_⟩, ⟨_, expand_push cur hr, fun (i : Nat) => ?_⟩⟩
      · show t.left.headD false = _
        rw [headD_eq, hL 0, List.take_zero, List.reverse_nil, List.nil_append, hll 0,
          getD_zero_append _ _ hx0, ← hxl]
        exact (getD_reverse_last _ hx0).symm
      · show t.left.tail.getD i false = _
        rw [Zipper.getD_tail, hL (i + 1), List.take_zero, List.reverse_nil, List.nil_append, hll (i + 1),
          getD_succ_append _ _ hx0, ← hxl, reverse_take_pred]
      · show (t.head :: t.right).getD i false = _
        have hd : x.1.reverse.drop (B - 1 + 1) = [] := by simp; omega
        have hc := drop_eq_cons cur 0 (by omega)
        rw [List.drop_zero] at hc
        rw [hd, List.nil_append, hc]
        cases i with
        | zero => simpa using hh
        | succ i => simpa using hR i


theorem Rep.diverges {B T : Nat} {S : Std.HashSet St} (hc : closed B T S = true)
    {c : Machine Zipper} (h : Rep T S c) : c⇑ := by
  intro k
  induction k generalizing c with
  | zero => rfl
  | succ k ih =>
    obtain ⟨c', hs, hr⟩ := Rep.step hc h
    simp only [Machine.steps, hs, Option.bind_some]
    exact ih hr

theorem rep_init {B T : Nat} {S : Std.HashSet St} {q : Program}
    (h0 : (⟨q, [], List.replicate B false, 0, []⟩ : St) ∈ S) : Rep T S (q.init Zipper) := by
  refine ⟨_, h0, rfl, ?_, ⟨[], Expand.nil, fun (i : Nat) => ?_⟩,
    ⟨[], Expand.nil, fun (i : Nat) => ?_⟩⟩
  · show false = _
    rw [getD_replicate_false]
  · show ([] : List Bool).getD i false = _
    simp
  · show ([] : List Bool).getD i false = _
    rw [List.drop_replicate, List.append_nil, getD_replicate_false]
    simp

def explore (B T limit : Nat) : Nat → Std.HashSet St → List St → Option (Std.HashSet St)
  | 0,        _,    _         => none
  | _ + 1,    seen, []        => some seen
  | fuel + 1, seen, s :: todo =>
    if !s.prog.alive || limit < seen.size then none
    else
      let new : List St := (succs B T s).filter fun (x : St) => !seen.contains x
      explore B T limit fuel (new.foldl (fun (h : Std.HashSet St) (x : St) => h.insert x) seen) (new ++ todo)

def check (B T limit : Nat) (q : Program) : Bool :=
  let s₀ : St := ⟨q, [], List.replicate B false, 0, []⟩
  match explore B T limit (10 * limit) ((∅ : Std.HashSet St).insert s₀) [s₀] with
  | some S => closed B T S && S.contains s₀
  | none   => false

theorem check_sound {B T limit : Nat} {q : Program} :
    check B T limit q = true → q⇑ := by
  intro h
  unfold check at h
  dsimp only at h
  split at h
  · simp only [Bool.and_eq_true] at h
    exact Program.diverges_of
      (Rep.diverges h.1 (rep_init (Std.HashSet.mem_iff_contains.mpr h.2)))
  · cases h

end Blocks

def Decider.blocks (B T limit : Nat) : Decider where
  decide := fun (q : Program) => cond (Blocks.check B T limit q) .diverges .unknown
  sound  := fun (q : Program) => by
    cases h : Blocks.check B T limit q with
    | true  => exact Blocks.check_sound h
    | false => trivial

def Decider.blocksUpTo (limit : Nat) : Decider :=
  any ((List.range 3).flatMap fun (b : Nat) =>
    (List.range 3).map fun (t : Nat) => blocks (b + 1) (t + 2) limit)

end Bf
