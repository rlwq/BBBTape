import BBBTape.Core.Decider
import BBBTape.Tapes.Spec

namespace BBBTape

open scoped Program Machine

def Decider.known (q₀ : Program) (h : q₀⇑) : Decider := fun q =>
  if hq : q = q₀ then .diverges (hq ▸ h) else .unknown

namespace Known

def tp (f : Int → Bool) (p : Int) : SpecTape := fun i => f (p + i)

def flp (f : Int → Bool) (p : Int) : Int → Bool := fun x => if x = p then !f x else f x

theorem step_left (f : Int → Bool) (p : Int) (q : Program) :
    (Machine.mk (tp f p) (.left q))⇒ = some ⟨tp f (p - 1), q⟩ := by
  show some (Machine.mk (Tape.moveL (tp f p)) q) = _
  congr 2; funext i; show f (p + (i - 1)) = f (p - 1 + i); congr 1; omega

theorem step_right (f : Int → Bool) (p : Int) (q : Program) :
    (Machine.mk (tp f p) (.right q))⇒ = some ⟨tp f (p + 1), q⟩ := by
  show some (Machine.mk (Tape.moveR (tp f p)) q) = _
  congr 2; funext i; show f (p + (i + 1)) = f (p + 1 + i); congr 1; omega

theorem step_flip (f : Int → Bool) (p : Int) (q : Program) :
    (Machine.mk (tp f p) (.flip q))⇒ = some ⟨tp (flp f p) p, q⟩ := by
  show some (Machine.mk (Tape.flip (tp f p)) q) = _
  congr 2; funext i
  show (if i = 0 then !f (p + 0) else f (p + i)) = (if p + i = p then !f (p + i) else f (p + i))
  by_cases h : i = 0
  · subst h; simp
  · simp [h, show p + i ≠ p by omega]

theorem step_loop_true {f : Int → Bool} {p : Int} (h : f p = true) (b q : Program) :
    (Machine.mk (tp f p) (.loop b q))⇒ = some ⟨tp f p, b ++ .loop b q⟩ := by
  show some (Machine.mk (tp f p) (if f (p + 0) then b ++ .loop b q else q)) = _
  rw [Int.add_zero, h]; rfl

theorem step_loop_false {f : Int → Bool} {p : Int} (h : f p = false) (b q : Program) :
    (Machine.mk (tp f p) (.loop b q))⇒ = some ⟨tp f p, q⟩ := by
  show some (Machine.mk (tp f p) (if f (p + 0) then b ++ .loop b q else q)) = _
  rw [Int.add_zero, h]; rfl

theorem run {m m' : Machine SpecTape} {n : Nat} {r : Option (Machine SpecTape)}
    (h : m⇒ = some m') (h' : m' ⇒ n = r) : m ⇒ (n + 1) = r := by
  simp [Machine.steps, h, h']

theorem flp_ne {f : Int → Bool} {p x : Int} (h : x ≠ p) : flp f p x = f x := by simp [flp, h]

theorem flp_eq (f : Int → Bool) (p : Int) : flp f p p = !f p := by simp [flp]

theorem diverges_of_tp {q r : Program} {f : Int → Bool} {p : Int} {k : Nat}
    (hs : (q.init SpecTape) ⇒ k = some ⟨tp f p, r⟩) (hd : (Machine.mk (tp f p) r)⇑) : q⇑ :=
  Program.diverges_of (Machine.diverges_of_steps hs hd)

end Known

end BBBTape
