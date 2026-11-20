import Bf.Decider
import Bf.Zipper

namespace Bf

namespace Windows

open scoped Program Machine

def win (n : Nat) (l : List Bool) : List Bool := (List.range n).map fun (k : Nat) => l.getD k false

theorem win_drop (n k : Nat) (l : List Bool) :
    win n (l.drop k) = (List.range n).map fun (i : Nat) => l.getD (k + i) false := by
  unfold win
  congr 1
  funext i
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem win_succ_cons (m : Nat) (h : Bool) (l : List Bool) :
    win (m + 1) (h :: l) = h :: win m l := by
  unfold win
  rw [List.range_succ_eq_map]
  simp

theorem win_succ (m : Nat) (l : List Bool) : win (m + 1) l = win m l ++ [l.getD m false] := by
  unfold win
  rw [List.range_succ]
  simp

theorem win_tail (m : Nat) (l : List Bool) :
    win (m + 1) l.tail = (win (m + 1) l).tail ++ [l.getD (m + 1) false] := by
  have h1 : win (m + 1 + 1) l = l.getD 0 false :: win (m + 1) l.tail := by
    unfold win
    rw [List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map]
    congr 1
    congr 1
    funext k
    cases l <;> simp
  have h2 := win_succ (m + 1) l
  rw [h1] at h2
  have h3 : (win (m + 1) l).tail ++ [l.getD (m + 1) false] =
      (win (m + 1) l ++ [l.getD (m + 1) false]).tail := by
    cases hw : win (m + 1) l with
    | nil => simp [win] at hw
    | cons a w => simp
  rw [h3, ← h2]
  rfl

theorem win_dropLast (m : Nat) (l : List Bool) : win m l = (win (m + 1) l).dropLast := by
  rw [win_succ, List.dropLast_concat]

theorem win_cons (m : Nat) (h : Bool) (l : List Bool) :
    win (m + 1) (h :: l) = h :: (win (m + 1) l).dropLast := by
  rw [win_succ_cons, win_dropLast]

theorem win_cons_drop (n j : Nat) (h : Bool) (l : List Bool) :
    win n ((h :: l).drop (j + 1)) = win n (l.drop j) := by
  rw [List.drop_succ_cons]

theorem win_tail_drop (n k : Nat) (l : List Bool) :
    win n (l.tail.drop k) = win n (l.drop (k + 1)) := by
  rw [List.drop_tail]

theorem headD_win (m : Nat) (l : List Bool) : (win (m + 1) l).headD false = l.headD false := by
  unfold win
  rw [List.range_succ_eq_map]
  cases l <;> simp

theorem win_nil_drop (n k : Nat) : win n (([] : List Bool).drop k) = List.replicate n false := by
  unfold win
  simp [List.map_const']

structure Loc where
  prog  : Program
  left  : List Bool
  head  : Bool
  right : List Bool
  deriving DecidableEq

def succs (LS RS : List (List Bool)) (s : Loc) : List Loc :=
  match s.prog with
  | ε        => []
  | .gap _ _ _ => []
  | .flip p  => [⟨p, s.left, !s.head, s.right⟩]
  | .loop b q => [⟨if s.head then b ++ .loop b q else q, s.left, s.head, s.right⟩]
  | .right p =>
    ([false, true].filter fun (x : Bool) => decide (s.right.tail ++ [x] ∈ RS)).map fun (x : Bool) =>
      ⟨p, s.head :: s.left.dropLast, s.right.headD false, s.right.tail ++ [x]⟩
  | .left p  =>
    ([false, true].filter fun (x : Bool) => decide (s.left.tail ++ [x] ∈ LS)).map fun (x : Bool) =>
      ⟨p, s.left.tail ++ [x], s.left.headD false, s.head :: s.right.dropLast⟩

def gramOK (LS RS : List (List Bool)) (s : Loc) : Bool :=
  match s.prog with
  | .right _ => decide (s.head :: s.left.dropLast ∈ LS)
  | .left _  => decide (s.head :: s.right.dropLast ∈ RS)
  | _        => true

def closed (S : List Loc) (LS RS : List (List Bool)) : Bool :=
  S.all fun (s : Loc) => s.prog.alive && (succs LS RS s).all (· ∈ S) && gramOK LS RS s

def Rep (m : Nat) (S : List Loc) (LS RS : List (List Bool)) (c : Machine Zipper) : Prop :=
  (⟨c.prog, win (m + 1) c.tape.left, c.tape.head, win (m + 1) c.tape.right⟩ : Loc) ∈ S ∧
  (∀ k : Nat, win (m + 1) (c.tape.left.drop k) ∈ LS) ∧
  (∀ k : Nat, win (m + 1) (c.tape.right.drop k) ∈ RS)

theorem Rep.step {m : Nat} {S : List Loc} {LS RS : List (List Bool)} (hc : closed S LS RS = true)
    {c : Machine Zipper} (h : Rep m S LS RS c) :
    ∃ c' : Machine Zipper, c⇒ = some c' ∧ Rep m S LS RS c' := by
  obtain ⟨hS, hL, hR⟩ := h
  have hcl := List.all_eq_true.mp hc _ hS
  simp only [Bool.and_eq_true, List.all_eq_true] at hcl
  obtain ⟨⟨halive, hsucc⟩, hgram⟩ := hcl
  obtain ⟨t, p⟩ := c
  cases p with
  | nil => simp [Program.alive] at halive
  | gap => simp [Program.alive] at halive
  | flip p =>
    refine ⟨⟨t.flip, p⟩, rfl, ?_, hL, hR⟩
    exact of_decide_eq_true (hsucc _ (by simp [succs]; exact ⟨rfl, rfl, rfl⟩))
  | loop b q =>
    refine ⟨⟨t, if t.head then b ++ .loop b q else q⟩, rfl, ?_, hL, hR⟩
    exact of_decide_eq_true (hsucc _ (by simp [succs]))
  | right p =>
    refine ⟨⟨t.moveR, p⟩, rfl, ?_, ?_, ?_⟩
    · apply of_decide_eq_true
      apply hsucc
      simp only [succs, List.mem_map, List.mem_filter, decide_eq_true_eq]
      refine ⟨t.right.getD (m + 1) false, ⟨by cases t.right.getD (m + 1) false <;> simp, ?_⟩, ?_⟩
      · rw [← win_tail]
        simpa using hR 1
      · show (⟨p, t.head :: (win (m + 1) t.left).dropLast, (win (m + 1) t.right).headD false,
          (win (m + 1) t.right).tail ++ [t.right.getD (m + 1) false]⟩ : Loc) =
          ⟨p, win (m + 1) (t.head :: t.left), t.right.headD false, win (m + 1) t.right.tail⟩
        rw [win_cons, headD_win, win_tail]
    · intro k
      show win (m + 1) ((t.head :: t.left).drop k) ∈ LS
      cases k with
      | zero =>
        simp only [List.drop_zero]
        rw [win_cons]
        simpa [gramOK] using hgram
      | succ j =>
        rw [win_cons_drop]
        exact hL j
    · intro k
      show win (m + 1) (t.right.tail.drop k) ∈ RS
      rw [win_tail_drop]
      exact hR (k + 1)
  | left p =>
    refine ⟨⟨t.moveL, p⟩, rfl, ?_, ?_, ?_⟩
    · apply of_decide_eq_true
      apply hsucc
      simp only [succs, List.mem_map, List.mem_filter, decide_eq_true_eq]
      refine ⟨t.left.getD (m + 1) false, ⟨by cases t.left.getD (m + 1) false <;> simp, ?_⟩, ?_⟩
      · rw [← win_tail]
        simpa using hL 1
      · show (⟨p, (win (m + 1) t.left).tail ++ [t.left.getD (m + 1) false],
          (win (m + 1) t.left).headD false, t.head :: (win (m + 1) t.right).dropLast⟩ : Loc) =
          ⟨p, win (m + 1) t.left.tail, t.left.headD false, win (m + 1) (t.head :: t.right)⟩
        rw [win_cons, headD_win, win_tail]
    · intro k
      show win (m + 1) (t.left.tail.drop k) ∈ LS
      rw [win_tail_drop]
      exact hL (k + 1)
    · intro k
      show win (m + 1) ((t.head :: t.right).drop k) ∈ RS
      cases k with
      | zero =>
        simp only [List.drop_zero]
        rw [win_cons]
        simpa [gramOK] using hgram
      | succ j =>
        rw [win_cons_drop]
        exact hR j

theorem Rep.diverges {m : Nat} {S : List Loc} {LS RS : List (List Bool)}
    (hc : closed S LS RS = true) {c : Machine Zipper} (h : Rep m S LS RS c) : c⇑ := by
  intro k
  induction k generalizing c with
  | zero => rfl
  | succ k ih =>
    obtain ⟨c', hs, hr⟩ := Rep.step hc h
    simp only [Machine.steps, hs, Option.bind_some]
    exact ih hr

def zeros (m : Nat) : List Bool := List.replicate (m + 1) false

abbrev State : Type := List Loc × List (List Bool) × List (List Bool)

def grow : Nat → State → State
  | 0,        st          => st
  | fuel + 1, (S, LS, RS) =>
    let S' : List Loc := S.foldl (fun (acc : List Loc) (s : Loc) =>
      (succs LS RS s).foldl (fun (a : List Loc) (x : Loc) => a.insert x) acc) S
    let LS' : List (List Bool) := S.foldl (fun (acc : List (List Bool)) (s : Loc) =>
      match s.prog with
      | .right _ => acc.insert (s.head :: s.left.dropLast)
      | _        => acc) LS
    let RS' : List (List Bool) := S.foldl (fun (acc : List (List Bool)) (s : Loc) =>
      match s.prog with
      | .left _ => acc.insert (s.head :: s.right.dropLast)
      | _       => acc) RS
    if (S'.length = S.length ∧ LS'.length = LS.length ∧ RS'.length = RS.length) ∨
        S'.any (fun (s : Loc) => !s.prog.alive) ∨ 5000 < S'.length
    then (S', LS', RS')
    else grow fuel (S', LS', RS')

def check (m fuel : Nat) (q : Program) : Bool :=
  let st := grow fuel ([⟨q, zeros m, false, zeros m⟩], [zeros m], [zeros m])
  closed st.1 st.2.1 st.2.2 && decide ((⟨q, zeros m, false, zeros m⟩ : Loc) ∈ st.1) &&
    decide (zeros m ∈ st.2.1) && decide (zeros m ∈ st.2.2)

theorem rep_init {m : Nat} {q : Program} {S : List Loc} {LS RS : List (List Bool)}
    (h0 : (⟨q, zeros m, false, zeros m⟩ : Loc) ∈ S) (hl : zeros m ∈ LS) (hr : zeros m ∈ RS) :
    Rep m S LS RS (q.init Zipper) := by
  refine ⟨?_, fun (k : Nat) => ?_, fun (k : Nat) => ?_⟩
  · have e : win (m + 1) ([] : List Bool) = zeros m := by
      simpa [zeros] using win_nil_drop (m + 1) 0
    show (⟨q, win (m + 1) [], false, win (m + 1) []⟩ : Loc) ∈ S
    rw [e]
    exact h0
  · show win (m + 1) (([] : List Bool).drop k) ∈ LS
    rw [win_nil_drop]
    exact hl
  · show win (m + 1) (([] : List Bool).drop k) ∈ RS
    rw [win_nil_drop]
    exact hr

theorem check_sound {m fuel : Nat} {q : Program} :
    check m fuel q = true → q⇑ := by
  intro h
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hc, h0⟩, hl⟩, hr⟩ := h
  exact Program.diverges_of (Rep.diverges hc (rep_init h0 hl hr))

end Windows

def Decider.windows (m fuel : Nat) : Decider where
  run   := fun (q : Program) => cond (Windows.check m fuel q) .diverges .unknown
  sound := fun (q : Program) => by
    cases h : Windows.check m fuel q with
    | true  => exact Windows.check_sound h
    | false => trivial

end Bf
