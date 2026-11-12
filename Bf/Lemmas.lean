import Bf.Basic

theorem Machine.run_add (a b : Nat) (m : Machine) : m.run (a + b) = (m.run a).run b := by
  induction a generalizing m with
  | zero => simp [run]
  | succ a ih => rw [Nat.succ_add]; exact ih m.step

theorem Machine.step_of_halted (m : Machine) (h : m.halted) : m.step = m := by
  obtain ⟨t, p⟩ := m
  simp only [halted] at h
  subst h
  rfl

theorem Machine.run_of_halted (m : Machine) (h : m.halted) (n : Nat) : m.run n = m := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [run, step_of_halted m h, ih]

theorem Machine.halted_run_add (m : Machine) (j i : Nat) (h : (m.run j).halted) :
    (m.run (j + i)).halted := by
  rw [run_add, run_of_halted _ h]
  exact h

theorem Machine.halts_run (m : Machine) (a : Nat) (h : m.halts) : (m.run a).halts := by
  obtain ⟨j, hj⟩ := h
  refine ⟨j, ?_⟩
  have := m.halted_run_add j a hj
  rwa [Nat.add_comm, run_add] at this

theorem Machine.run_mul_of_cycle (m : Machine) (n : Nat) (hc : m.run n = m) (k : Nat) :
    m.run (n * k) = m := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Nat.mul_succ, run_add, ih, hc]

theorem Machine.not_halts_of_cycle (m : Machine) (n : Nat)
    (hn : 0 < n) (hm : ¬ m.halted) (hc : m.run n = m) : ¬ m.halts := by
  intro ⟨j, hj⟩
  have hle : j ≤ n * j := Nat.le_mul_of_pos_left j hn
  have := m.halted_run_add j (n * j - j) hj
  rw [Nat.add_sub_cancel' hle, run_mul_of_cycle m n hc] at this
  exact hm this

theorem Machine.not_halts_of_invariant (S : Machine → Prop) (k : Nat) (hk : 0 < k)
    (hS : ∀ m, S m → ¬ m.halted) (hstep : ∀ m, S m → S (m.run k))
    (m : Machine) (hm : S m) : ¬ m.halts := by
  have hall : ∀ i, S (m.run (k * i)) := by
    intro i
    induction i with
    | zero => exact hm
    | succ i ih => rw [Nat.mul_succ, run_add]; exact hstep _ ih
  intro ⟨j, hj⟩
  have hle : j ≤ k * j := Nat.le_mul_of_pos_left j hk
  have := m.halted_run_add j (k * j - j) hj
  rw [Nat.add_sub_cancel' hle] at this
  exact hS _ (hall j) this

def Tape.ZeroBeyond (t : Tape) (r : Nat) : Prop :=
  ∀ i : Int, (r : Int) < i ∨ i < -(r : Int) → t.cells i = false

theorem Tape.zeroBeyond_blank : Tape.blank.ZeroBeyond 0 := fun _ _ => rfl

theorem Tape.ZeroBeyond.mono {t : Tape} {r r' : Nat} (h : t.ZeroBeyond r) (hr : r ≤ r') :
    t.ZeroBeyond r' :=
  fun i hi => h i (by omega)

theorem Machine.zeroBeyond_step (m : Machine) (r : Nat) (h : m.tape.ZeroBeyond r) :
    m.step.tape.ZeroBeyond (r + 1) := by
  obtain ⟨t, p⟩ := m
  cases p with
  | nil => exact h.mono (by omega)
  | left p => intro i hi; exact h (i - 1) (by omega)
  | right p => intro i hi; exact h (i + 1) (by omega)
  | flip p =>
    intro i hi
    show (if i = 0 then !t.cells 0 else t.cells i) = false
    split
    · exfalso; omega
    · exact h i (by omega)
  | loop body p =>
    simp only [step]
    split <;> exact h.mono (by omega)

theorem Machine.zeroBeyond_run (m : Machine) (r k : Nat) (h : m.tape.ZeroBeyond r) :
    (m.run k).tape.ZeroBeyond (r + k) := by
  induction k generalizing m r with
  | zero => exact h
  | succ k ih =>
    have := ih m.step (r + 1) (m.zeroBeyond_step r h)
    rwa [Nat.add_right_comm, Nat.add_assoc] at this

def Tape.AgreeOn (W : Nat) (t u : Tape) : Prop :=
  ∀ j, j < W + 1 → t.cells j = u.cells j ∧ t.cells (-(j : Int)) = u.cells (-(j : Int))

instance (W : Nat) (t u : Tape) : Decidable (t.AgreeOn W u) := by
  unfold Tape.AgreeOn; infer_instance

theorem Tape.eq_of_agreeOn {t u : Tape} {W : Nat} (h : t.AgreeOn W u)
    (ht : t.ZeroBeyond W) (hu : u.ZeroBeyond W) : t = u := by
  ext i
  by_cases hi : (W : Int) < i ∨ i < -(W : Int)
  · rw [ht i hi, hu i hi]
  · by_cases hs : 0 ≤ i
    · have e : i = (i.toNat : Int) := by omega
      rw [e]; exact (h i.toNat (by omega)).1
    · have e : i = -((-i).toNat : Int) := by omega
      rw [e]; exact (h (-i).toNat (by omega)).2

def Program.mirror : Program → Program
  | .nil         => .nil
  | .left p      => .right p.mirror
  | .right p     => .left p.mirror
  | .flip p      => .flip p.mirror
  | .loop body p => .loop body.mirror p.mirror

theorem Program.mirror_append (a b : Program) : (a ++ b).mirror = a.mirror ++ b.mirror := by
  induction a with
  | nil => rfl
  | left p ih =>
    show Program.right (p ++ b).mirror = Program.right (p.mirror ++ b.mirror); rw [ih]
  | right p ih =>
    show Program.left (p ++ b).mirror = Program.left (p.mirror ++ b.mirror); rw [ih]
  | flip p ih =>
    show Program.flip (p ++ b).mirror = Program.flip (p.mirror ++ b.mirror); rw [ih]
  | loop body p _ ih =>
    show Program.loop body.mirror (p ++ b).mirror = Program.loop body.mirror (p.mirror ++ b.mirror)
    rw [ih]

def Tape.mirror (t : Tape) : Tape := ⟨fun i => t.cells (-i)⟩

def Machine.mirror (m : Machine) : Machine := ⟨m.tape.mirror, m.program.mirror⟩

theorem Machine.mirror_step (m : Machine) : m.mirror.step = m.step.mirror := by
  obtain ⟨t, p⟩ := m
  cases p with
  | nil => rfl
  | left q =>
    refine Machine.ext (Tape.ext (funext fun i => ?_)) rfl
    show t.cells (-(i + 1)) = t.cells (-i - 1)
    congr 1; omega
  | right q =>
    refine Machine.ext (Tape.ext (funext fun i => ?_)) rfl
    show t.cells (-(i - 1)) = t.cells (-i + 1)
    congr 1; omega
  | flip q =>
    refine Machine.ext (Tape.ext (funext fun i => ?_)) rfl
    show (if i = 0 then !t.cells (-0) else t.cells (-i)) =
      (if -i = 0 then !t.cells 0 else t.cells (-i))
    by_cases hi : i = 0
    · subst hi; rfl
    · simp [hi]
  | loop body q =>
    show (if t.cells (-0) = true then _ else _) = Machine.mirror (if t.cells 0 = true then _ else _)
    rw [Int.neg_zero]
    split
    · show Machine.mk t.mirror (body.mirror ++ .loop body.mirror q.mirror) =
        Machine.mk t.mirror (body ++ .loop body q).mirror
      rw [Program.mirror_append]; rfl
    · rfl

theorem Machine.mirror_run (m : Machine) (n : Nat) : m.mirror.run n = (m.run n).mirror := by
  induction n generalizing m with
  | zero => rfl
  | succ n ih => show m.mirror.step.run n = _; rw [mirror_step]; exact ih m.step

theorem Machine.halted_mirror (m : Machine) : m.mirror.halted ↔ m.halted := by
  obtain ⟨t, p⟩ := m
  cases p <;> simp [halted, mirror, Program.mirror]

theorem Machine.halts_mirror (m : Machine) : m.mirror.halts ↔ m.halts := by
  simp only [halts, mirror_run, halted_mirror]

theorem Program.toMachine_mirror (p : Program) : p.mirror.toMachine = p.toMachine.mirror := rfl
