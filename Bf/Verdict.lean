namespace Bf

inductive Verdict where
  | halts (steps : Nat)
  | nonhalts
  | unknown
  deriving DecidableEq, Repr

namespace Verdict

instance : ToString Verdict where
  toString
    | halts n  => s!"halts in {n}"
    | nonhalts => "nonhalts"
    | unknown  => "unknown"

def sup : Verdict → Verdict → Verdict
  | unknown,  _        => unknown
  | _,        unknown  => unknown
  | nonhalts, v        => v
  | v,        nonhalts => v
  | halts a,  halts b  => halts (max a b)

theorem nonhalts_sup (v : Verdict) : nonhalts.sup v = v := by cases v <;> rfl

theorem sup_nonhalts (v : Verdict) : v.sup nonhalts = v := by cases v <;> rfl

theorem sup_self (v : Verdict) : v.sup v = v := by cases v <;> simp [sup]

theorem sup_comm (a b : Verdict) : a.sup b = b.sup a := by
  cases a <;> cases b <;> simp [sup, Nat.max_comm]

theorem sup_assoc (a b c : Verdict) : (a.sup b).sup c = a.sup (b.sup c) := by
  cases a <;> cases b <;> cases c <;> simp [sup, Nat.max_assoc]

theorem sup_eq_left_or_right (a b : Verdict) : a.sup b = a ∨ a.sup b = b := by
  cases a <;> cases b <;> simp [sup] <;> omega

theorem of_sup_halts {v : Verdict} {s : Nat} (h : v.sup (halts s) = halts s) :
    v = nonhalts ∨ ∃ k : Nat, k ≤ s ∧ v = halts k := by
  cases v with
  | halts k => exact .inr ⟨k, by simp [sup] at h; omega, rfl⟩
  | nonhalts => exact .inl rfl
  | unknown => simp [sup] at h

def summary (vs : List Verdict) : Verdict := vs.foldr sup nonhalts

theorem sup_summary_of_mem {vs : List Verdict} {v : Verdict} (h : v ∈ vs) :
    v.sup (summary vs) = summary vs := by
  induction vs with
  | nil => cases h
  | cons w vs ih =>
    show v.sup (w.sup (summary vs)) = w.sup (summary vs)
    rcases List.mem_cons.mp h with rfl | h
    · rw [← sup_assoc, sup_self]
    · rw [← sup_assoc, sup_comm v w, sup_assoc, ih h]

theorem summary_eq_nonhalts_or_mem (vs : List Verdict) : summary vs = nonhalts ∨ summary vs ∈ vs := by
  induction vs with
  | nil => exact .inl rfl
  | cons w vs ih =>
    show w.sup (summary vs) = nonhalts ∨ w.sup (summary vs) ∈ w :: vs
    rcases sup_eq_left_or_right w (summary vs) with e | e
    · rw [e]; exact .inr (List.mem_cons_self ..)
    · rw [e]
      rcases ih with ih | ih
      · exact .inl ih
      · exact .inr (List.mem_cons_of_mem _ ih)

end Verdict

end Bf
