import Bf.Lemmas
import Bf.Decider

def Machine.stepDisp (m : Machine) : Int :=
  match m.program with
  | .left _  => -1
  | .right _ => 1
  | _        => 0

def Machine.disp : Nat → Machine → Int
  | 0,     _ => 0
  | n + 1, m => m.stepDisp + disp n m.step

theorem Machine.stepDisp_bound (m : Machine) : -1 ≤ m.stepDisp ∧ m.stepDisp ≤ 1 := by
  unfold stepDisp; split <;> omega

def Machine.AgreeFrom (lo : Int) (m m' : Machine) : Prop :=
  m.program = m'.program ∧ ∀ i, lo ≤ i → m.tape.cells i = m'.tape.cells i

theorem Machine.AgreeFrom.mono {lo lo' : Int} {m m' : Machine}
    (h : m.AgreeFrom lo m') (hl : lo ≤ lo') : m.AgreeFrom lo' m' :=
  ⟨h.1, fun i hi => h.2 i (by omega)⟩

theorem Machine.AgreeFrom.step {lo : Int} {m m' : Machine} (h : m.AgreeFrom lo m') (hlo : lo ≤ 0) :
    m.step.AgreeFrom (lo - m.stepDisp) m'.step ∧ m.stepDisp = m'.stepDisp := by
  obtain ⟨t, p⟩ := m
  obtain ⟨t', p'⟩ := m'
  obtain ⟨hp, hc⟩ := h
  simp only at hp hc
  subst hp
  cases p with
  | nil => exact ⟨⟨rfl, fun i hi => hc i (by simp [stepDisp] at hi; omega)⟩, rfl⟩
  | left q =>
    refine ⟨⟨rfl, fun i hi => ?_⟩, rfl⟩
    simp only [stepDisp] at hi
    exact hc (i - 1) (by omega)
  | right q =>
    refine ⟨⟨rfl, fun i hi => ?_⟩, rfl⟩
    simp only [stepDisp] at hi
    exact hc (i + 1) (by omega)
  | flip q =>
    refine ⟨⟨rfl, fun i hi => ?_⟩, rfl⟩
    simp only [stepDisp] at hi
    show (if i = 0 then !t.cells 0 else t.cells i) = (if i = 0 then !t'.cells 0 else t'.cells i)
    rw [hc 0 hlo, hc i (by omega)]
  | loop body q =>
    have h0 : t.head = t'.head := hc 0 hlo
    refine ⟨?_, rfl⟩
    show AgreeFrom (lo - 0)
      (if t.head then ⟨t, body ++ .loop body q⟩ else ⟨t, q⟩)
      (if t'.head then ⟨t', body ++ .loop body q⟩ else ⟨t', q⟩)
    rw [← h0]
    split
    · exact ⟨rfl, fun i hi => hc i (by omega)⟩
    · exact ⟨rfl, fun i hi => hc i (by omega)⟩

theorem Machine.AgreeFrom.run {lo : Int} {m m' : Machine} (s : Nat)
    (h : m.AgreeFrom lo m') (hlo : lo + s ≤ 0) :
    (m.run s).AgreeFrom (lo - m.disp s) (m'.run s) ∧ m.disp s = m'.disp s := by
  induction s generalizing lo m m' with
  | zero =>
    refine ⟨?_, rfl⟩
    simp only [disp, Int.sub_zero]
    exact h
  | succ s ih =>
    obtain ⟨h1, hd1⟩ := h.step (by omega)
    have hb := m.stepDisp_bound
    obtain ⟨h2, hd2⟩ := ih h1 (by omega)
    refine ⟨?_, by simp only [disp, hd1, hd2]⟩
    have e : lo - m.disp (s + 1) = lo - m.stepDisp - m.step.disp s := by
      simp only [disp]; omega
    rw [e]
    exact h2

theorem Machine.not_halts_of_translated (m : Machine) (L : Nat) (hL : 0 < L)
    (hm : ¬ m.halted) (hd : 0 ≤ m.disp L) (ha : m.AgreeFrom (-L) (m.run L)) : ¬ m.halts := by
  apply not_halts_of_invariant
    (fun x => ¬ x.halted ∧ 0 ≤ x.disp L ∧ x.AgreeFrom (-L) (x.run L)) L hL
  · exact fun _ h => h.1
  · intro x ⟨hx, hdx, hax⟩
    obtain ⟨hr, hdr⟩ := hax.run L (by omega)
    refine ⟨?_, by omega, hr.mono (by omega)⟩
    intro hh
    apply hx
    unfold halted at hh ⊢
    rw [hax.1, hh]
  · exact ⟨hm, hd, ha⟩

def translatedRight (k L : Nat) : Decider where
  run p :=
    let m₁ := p.toMachine.run k
    let m₂ := m₁.run L
    if 0 < L ∧ ¬ m₁.halted ∧ 0 ≤ m₁.disp L ∧ m₁.program = m₂.program ∧
        ∀ j, j < k + 2 * L + 1 → m₁.tape.cells ((j : Int) - L) = m₂.tape.cells ((j : Int) - L)
    then .nonhalts else .unknown
  sound_h p h := by
    simp only at h
    split at h <;> simp at h
  sound_nh p h hp := by
    simp only at h
    split at h
    · rename_i hc
      obtain ⟨hL, hm, hd, hprog, hw⟩ := hc
      have z₁ := p.toMachine.zeroBeyond_run 0 k Tape.zeroBeyond_blank
      have z₂ := (p.toMachine.run k).zeroBeyond_run (0 + k) L z₁
      have ha : (p.toMachine.run k).AgreeFrom (-L) ((p.toMachine.run k).run L) := by
        refine ⟨hprog, fun i hi => ?_⟩
        by_cases hik : i ≤ (k : Int) + L
        · have e : i = ((i + L).toNat : Int) - L := by omega
          rw [e]
          exact hw _ (by omega)
        · rw [z₁ i (by omega), z₂ i (by omega)]
      exact (p.toMachine.run k).not_halts_of_translated L hL hm hd ha
        (p.toMachine.halts_run k hp)
    · simp at h

def translatedLeft (k L : Nat) : Decider where
  run p := (translatedRight k L).run p.mirror
  sound_h p h := by
    have := (translatedRight k L).sound_h p.mirror h
    rwa [Program.toMachine_mirror, Machine.halts_mirror] at this
  sound_nh p h := by
    have := (translatedRight k L).sound_nh p.mirror h
    rwa [Program.toMachine_mirror, Machine.halts_mirror] at this

def translatedDecider (k L : Nat) : Decider :=
  translatedRight k L <|> translatedLeft k L
