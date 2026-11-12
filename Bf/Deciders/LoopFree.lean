import Bf.Decider

inductive Program.LoopFree : Program → Prop
  | nil   : LoopFree .nil
  | left  : LoopFree p → LoopFree (.left p)
  | right : LoopFree p → LoopFree (.right p)
  | flip  : LoopFree p → LoopFree (.flip p)

def Program.decLoopFree : (p : Program) → Decidable p.LoopFree
  | .nil      => isTrue .nil
  | .left p   => match decLoopFree p with
    | isTrue h  => isTrue (.left h)
    | isFalse h => isFalse fun | .left h' => h h'
  | .right p  => match decLoopFree p with
    | isTrue h  => isTrue (.right h)
    | isFalse h => isFalse fun | .right h' => h h'
  | .flip p   => match decLoopFree p with
    | isTrue h  => isTrue (.flip h)
    | isFalse h => isFalse fun | .flip h' => h h'
  | .loop _ _ => isFalse nofun

instance : DecidablePred Program.LoopFree := Program.decLoopFree

theorem Program.halts_of_loopFree (p : Program) (t : Tape) (h : p.LoopFree) :
    (Machine.mk t p).halts := by
  induction h generalizing t with
  | nil => exists 0
  | left _ ih =>
    obtain ⟨n, hn⟩ := ih t.moveL
    exact ⟨n + 1, hn⟩
  | right _ ih =>
    obtain ⟨n, hn⟩ := ih t.moveR
    exact ⟨n + 1, hn⟩
  | flip _ ih =>
    obtain ⟨n, hn⟩ := ih t.flip
    exact ⟨n + 1, hn⟩

def loopFreeDecider : Decider where
  run p := if p.LoopFree then .halts else .unknown
  sound_h p h := by
    by_cases hl : p.LoopFree
    · exact Program.halts_of_loopFree p .blank hl
    · simp [hl] at h
  sound_nh p h := by
    by_cases hl : p.LoopFree <;> simp [hl] at h
