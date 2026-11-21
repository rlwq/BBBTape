namespace Bf

inductive Program where
  | nil
  | left  (rest : Program)
  | right (rest : Program)
  | flip  (rest : Program)
  | loop  (body rest : Program)
  | gap   (size : Nat) (pos : 0 < size) (rest : Program)
  deriving DecidableEq, Repr, Hashable

namespace Program

scoped notation "ε" => Program.nil

def append : Program → Program → Program
  | ε,        q => q
  | left p,   q => left (p.append q)
  | right p,  q => right (p.append q)
  | flip p,   q => flip (p.append q)
  | loop b p, q => loop b (p.append q)
  | gap k h p, q => gap k h (p.append q)

instance : Append Program := ⟨append⟩

@[simp] theorem nil_append (q : Program) : ε ++ q = q := rfl
@[simp] theorem left_append (p q : Program) : left p ++ q = left (p ++ q) := rfl
@[simp] theorem right_append (p q : Program) : right p ++ q = right (p ++ q) := rfl
@[simp] theorem flip_append (p q : Program) : flip p ++ q = flip (p ++ q) := rfl
@[simp] theorem loop_append (b p q : Program) : loop b p ++ q = loop b (p ++ q) := rfl
@[simp] theorem gap_append (k : Nat) (h : 0 < k) (p q : Program) : gap k h p ++ q = gap k h (p ++ q) := rfl

@[simp] theorem append_nil (p : Program) : p ++ ε = p := by
  induction p with
  | nil => rfl
  | left _ ih | right _ ih | flip _ ih | loop _ _ _ ih | gap _ _ _ ih => simp [ih]

theorem append_assoc (p q r : Program) : p ++ q ++ r = p ++ (q ++ r) := by
  induction p with
  | nil => rfl
  | left _ ih | right _ ih | flip _ ih | loop _ _ _ ih | gap _ _ _ ih => simp [ih]

def size : Program → Nat
  | ε        => 0
  | left p   => p.size + 1
  | right p  => p.size + 1
  | flip p   => p.size + 1
  | loop b p => b.size + p.size + 2
  | gap k _ p => k + p.size

scoped notation "‖" p "‖" => Program.size p

@[simp] theorem size_append (p q : Program) : (p ++ q).size = p.size + q.size := by
  induction p with
  | nil => simp [size]
  | left _ ih | right _ ih | flip _ ih | loop _ _ _ ih | gap _ _ _ ih => simp [size, ih]; omega

def toString : Program → String
  | ε        => ""
  | left p   => "<" ++ p.toString
  | right p  => ">" ++ p.toString
  | flip p   => "*" ++ p.toString
  | loop b p => "[" ++ b.toString ++ "]" ++ p.toString
  | gap k _ p => String.ofList (List.replicate k '?') ++ p.toString

instance : ToString Program := ⟨toString⟩

theorem length_toString (p : Program) : p.toString.length = p.size := by
  have : "<".length = 1
       ∧ ">".length = 1
       ∧ "*".length = 1
       ∧ "[".length = 1
       ∧ "]".length = 1
       := by decide
  induction p
    <;> simp [toString, size, String.length_append, *] <;> omega

def numGaps : Program → Nat
  | ε        => 0
  | left p   => p.numGaps
  | right p  => p.numGaps
  | flip p   => p.numGaps
  | loop b p => b.numGaps + p.numGaps
  | gap _ _ p => 1 + p.numGaps

def gapSize? : Nat → Program → Option Nat
  | _, ε        => none
  | i, left p   => gapSize? i p
  | i, right p  => gapSize? i p
  | i, flip p   => gapSize? i p
  | i, loop b p =>
    if i < b.numGaps then gapSize? i b
    else gapSize? (i - b.numGaps) p
  | 0,     gap k _ _ => some k
  | i + 1, gap _ _ p => gapSize? i p

def subst : Nat → Program → Program → Program
  | _, _, ε        => ε
  | i, s, left p   => left (subst i s p)
  | i, s, right p  => right (subst i s p)
  | i, s, flip p   => flip (subst i s p)
  | i, s, loop b p =>
    if i < b.numGaps then loop (subst i s b) p
    else loop b (subst (i - b.numGaps) s p)
  | 0,     s, gap _ _ p => s ++ p
  | i + 1, s, gap k h p => gap k h (subst i s p)

scoped syntax:max term noWs "[" term " ↦ " term "]" : term
scoped macro_rules | `($p[$i ↦ $s]) => `(subst $i $s $p)

/-- How much of a program is still unknown: the total size of its gaps. -/
def gapSum : Program → Nat
  | ε        => 0
  | left p   => p.gapSum
  | right p  => p.gapSum
  | flip p   => p.gapSum
  | loop b p => b.gapSum + p.gapSum
  | gap k _ p => k + p.gapSum

/-- How much of `p` is still unknown, so that `p°` means `‖p‖° = 0`. -/
scoped notation:max "‖" p "‖°" => Program.gapSum p

@[simp] theorem gapSum_append (p q : Program) : ‖p ++ q‖° = ‖p‖° + ‖q‖° := by
  induction p with
  | nil => simp [gapSum]
  | left _ ih | right _ ih | flip _ ih | loop _ _ _ ih | gap _ _ _ ih =>
    simp [gapSum, ih] <;> omega

theorem gapSize?_pos {i k : Nat} {q : Program} : gapSize? i q = some k → 0 < k := by
  intro h
  induction q generalizing i with
  | nil => simp [gapSize?] at h
  | left p ih | right p ih | flip p ih => simp only [gapSize?] at h; exact ih h
  | loop b p ihb ihp =>
    simp only [gapSize?] at h
    split at h
    · exact ihb h
    · exact ihp h
  | gap m hm p ih =>
    cases i with
    | zero => simp only [gapSize?, Option.some.injEq] at h; exact h ▸ hm
    | succ j => simp only [gapSize?] at h; exact ih h

theorem gapSum_subst (s : Program) {i k : Nat} {q : Program} :
    gapSize? i q = some k → ‖q[i ↦ s]‖° + k = ‖q‖° + ‖s‖° := by
  intro h
  induction q generalizing i with
  | nil => simp [gapSize?] at h
  | left p ih | right p ih | flip p ih =>
    simp only [gapSize?] at h
    simp only [subst, gapSum]
    exact ih h
  | loop b p ihb ihp =>
    simp only [gapSize?] at h
    split at h
    · next hi =>
      have := ihb h
      simp only [subst, hi, ↓reduceIte, gapSum]
      omega
    · next hi =>
      have := ihp h
      simp only [subst, hi, ↓reduceIte, gapSum]
      omega
  | gap m _ p ih =>
    cases i with
    | zero =>
      simp only [gapSize?, Option.some.injEq] at h
      subst h
      simp only [subst, gapSum, gapSum_append]
      omega
    | succ j =>
      simp only [gapSize?] at h
      have := ih h
      simp only [subst, gapSum]
      omega

theorem size_subst (s : Program) {i k : Nat} {q : Program} :
    gapSize? i q = some k → (subst i s q).size + k = q.size + s.size := by
  intro h
  induction q generalizing i with
  | nil => simp [gapSize?] at h
  | left p ih | right p ih | flip p ih =>
    simp only [gapSize?] at h
    have := ih h
    simp only [subst, size]
    omega
  | loop b p ihb ihp =>
    simp only [gapSize?] at h
    split at h
    · next hi =>
      have := ihb h
      simp only [subst, hi, ↓reduceIte, size]
      omega
    · next hi =>
      have := ihp h
      simp only [subst, hi, ↓reduceIte, size]
      omega
  | gap m _ p ih =>
    cases i with
    | zero =>
      simp only [gapSize?, Option.some.injEq] at h
      subst h
      simp only [subst, size, size_append]
      omega
    | succ j =>
      simp only [gapSize?] at h
      have := ih h
      simp only [subst, size]
      omega

/-- A gap of size `k`, or nothing at all when `k = 0`: gaps are never empty. -/
def gap? : Nat → Program
  | 0     => ε
  | k + 1 => gap (k + 1) (Nat.succ_pos k) ε

/-- A gap of size `k`. -/
scoped prefix:max "ω" => Program.gap?

@[simp] theorem gapSum_gap? (k : Nat) : ‖ω k‖° = k := by
  cases k <;> simp [gap?, gapSum]

@[simp] theorem size_gap? (k : Nat) : ‖ω k‖ = k := by
  cases k <;> simp [gap?, size]

def Closed : Program → Prop
  | ε        => True
  | left p   => p.Closed
  | right p  => p.Closed
  | flip p   => p.Closed
  | loop b p => b.Closed ∧ p.Closed
  | gap _ _ _ => False

scoped postfix:max "°" => Closed

theorem closed_iff {p : Program} : p° ↔ ‖p‖° = 0 := by
  induction p with
  | nil => exact ⟨fun _ => rfl, fun _ => trivial⟩
  | left _ ih | right _ ih | flip _ ih => exact ih
  | loop _ _ ihb ihp => simp only [Closed, gapSum, ihb, ihp]; omega
  | gap _ h _ _ => simp only [Closed, gapSum, false_iff]; omega

def alive : Program → Bool
  | ε       => false
  | gap _ _ _ => false
  | _         => true

def mirror : Program → Program
  | ε        => ε
  | left p   => right p.mirror
  | right p  => left p.mirror
  | flip p   => flip p.mirror
  | loop b p => loop b.mirror p.mirror
  | gap k h p => gap k h p.mirror

@[simp] theorem mirror_append (p q : Program) : (p ++ q).mirror = p.mirror ++ q.mirror := by
  induction p with
  | nil => rfl
  | left _ ih | right _ ih | flip _ ih | loop _ _ _ ih | gap _ _ _ ih => simp [mirror, ih]

@[simp] theorem mirror_mirror (p : Program) : p.mirror.mirror = p := by
  induction p with
  | nil => rfl
  | left _ ih | right _ ih | flip _ ih | gap _ _ _ ih => simp [mirror, ih]
  | loop _ _ ihb ihp => simp [mirror, ihb, ihp]

@[simp] theorem size_mirror (p : Program) : p.mirror.size = p.size := by
  induction p with
  | nil => rfl
  | left _ ih | right _ ih | flip _ ih | gap _ _ _ ih => simp [mirror, size, ih]
  | loop _ _ ihb ihp => simp [mirror, size, ihb, ihp]

theorem closed_mirror {p : Program} : p.Closed → p.mirror.Closed := by
  intro hp
  induction p with
  | nil => trivial
  | left _ ih | right _ ih | flip _ ih => exact ih hp
  | loop _ _ ihb ihp => exact ⟨ihb hp.1, ihp hp.2⟩
  | gap => exact absurd hp id

@[simp] theorem numGaps_mirror (p : Program) : p.mirror.numGaps = p.numGaps := by
  induction p with
  | nil => rfl
  | left _ ih | right _ ih | flip _ ih | gap _ _ _ ih => simp [mirror, numGaps, ih]
  | loop _ _ ihb ihp => simp [mirror, numGaps, ihb, ihp]

def noShift : Program → Bool
  | ε        => true
  | left _   => false
  | right _  => false
  | flip p   => p.noShift
  | loop b p => b.noShift && p.noShift
  | gap _ _ p => p.noShift

theorem mirror_eq_self {p : Program} : p.noShift = true → p.mirror = p := by
  intro h
  induction p with
  | nil => rfl
  | left | right => cases h
  | flip _ ih | gap _ _ _ ih => simp [mirror, ih h]
  | loop _ _ ihb ihp =>
    simp only [noShift, Bool.and_eq_true] at h
    simp [mirror, ihb h.1, ihp h.2]

theorem closed_append {p q : Program} : p° → q° → (p ++ q)° := by
  intro hp hq
  induction p with
  | nil => exact hq
  | left _ ih | right _ ih | flip _ ih => exact ih hp
  | loop _ _ _ ihp => exact ⟨hp.1, ihp hp.2⟩
  | gap => exact absurd hp id

theorem closed_of_append {p q : Program} : (p ++ q)° → p° ∧ q° := by
  induction p with
  | nil => exact fun h => ⟨trivial, h⟩
  | left _ ih | right _ ih | flip _ ih => exact ih
  | loop _ _ _ ihp => exact fun ⟨hb, hq⟩ => ⟨⟨hb, (ihp hq).1⟩, (ihp hq).2⟩
  | gap => exact fun h => absurd h id

theorem size_eq_zero_of_closed {p : Program} : p° → ‖p‖ = 0 → p = ε := by
  intro hp hs
  cases p with
  | nil => rfl
  | gap => exact absurd hp id
  | _ => simp [size] at hs

def rep (f : Program → Program) : Nat → Program → Program
  | 0,     r => r
  | n + 1, r => f (rep f n r)

theorem rep_append (f : Program → Program) (hf : ∀ p q, f p ++ q = f (p ++ q)) :
    ∀ n p q, rep f n p ++ q = rep f n (p ++ q)
  | 0,     _, _ => rfl
  | n + 1, p, q => by simp [rep, hf, rep_append f hf n]

theorem size_rep (f : Program → Program) (hf : ∀ p, ‖f p‖ = ‖p‖ + 1) :
    ∀ n r, ‖rep f n r‖ = n + ‖r‖
  | 0,     _ => by simp [rep]
  | n + 1, r => by simp [rep, hf, size_rep f hf n]; omega

theorem closed_rep (f : Program → Program) (hf : ∀ p, p° → (f p)°) :
    ∀ {n r}, r° → (rep f n r)°
  | 0,     _, hr => hr
  | _ + 1, _, hr => hf _ (closed_rep f hf hr)

theorem mirror_rep_right : ∀ n r, (rep .right n r).mirror = rep .left n r.mirror
  | 0,     _ => rfl
  | n + 1, r => by simp [rep, mirror, mirror_rep_right n]

end Program

end Bf
