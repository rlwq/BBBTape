import Bf
open Bf

/-! Profiling harness (experiment, not part of the proof). `base` runs `fullChain`'s
deciders one by one; `shared` replaces each translated-cycler stage by a draft that
simulates the machine once and checks every period `L` against the stored history. -/

inductive Tag where
  | halts (t : Nat) | diverges | stuck (i : Nat) | unknown

def ofVerdict {q : Program} : Verdict q → Tag
  | .halts t _  => .halts t
  | .diverges _ => .diverges
  | .stuck i    => .stuck i.val
  | .unknown    => .unknown

def real (d : Decider) : Program → Tag := fun q => ofVerdict (d q)

instance : Inhabited (Machine Zipper) := ⟨⟨Zipper.blank, .nil⟩⟩

open Machine in
/-- `k` steps from `m`, tracking the head's absolute position. -/
def simTo : Machine Zipper → Nat → Int → Option (Machine Zipper × Int)
  | m, 0,     pos => some (m, pos)
  | m, n + 1, pos =>
    match m⇒ with
    | none    => none
    | some m' => simTo m' n (pos + m.δ)

open Machine in
/-- The next `L` machines after `m` (index 0 is `m` itself), stopping early if it halts. -/
def collect (m : Machine Zipper) (pos : Int) : Nat → Array (Machine Zipper × Int) → Array (Machine Zipper × Int)
  | 0,     acc => acc.push (m, pos)
  | L + 1, acc =>
    match m⇒ with
    | none    => acc.push (m, pos)
    | some m' => collect m' (pos + m.δ) L (acc.push (m, pos))

/-- Same predicate as `isTranslated k L`, for every `L ∈ Ls`, from a single run. -/
def translatedShared (k : Nat) (Ls : List Nat) (q : Program) : Bool :=
  match simTo (q.init Zipper) k 0 with
  | none => false
  | some (c₁, p₁) =>
    let hist := collect c₁ p₁ (Ls.foldl max 0) #[]
    Ls.any fun L =>
      0 < L && L < hist.size &&
        let ((c₂ : Machine Zipper), (p₂ : Int)) := hist[L]!
        decide (0 ≤ p₂ - p₁) && c₁.prog == c₂.prog &&
          (List.range (k + 2 * L + 1)).all fun (j : Nat) =>
            Tape.cells c₁.tape ((j : Int) - L) == Tape.cells c₂.tape ((j : Int) - L)

def shared (k : Nat) (Ls : List Nat) : Program → Tag := fun q =>
  if translatedShared k Ls q || translatedShared k Ls q.mirror then .diverges else .unknown

def baseStages : Array (String × (Program → Tag)) := #[
  ("simulator 300",         real (Decider.simulator Zipper 300)),
  ("translatedUpTo 50 24",  real (.translatedUpTo 50 24)),
  ("windows 1 200",         real (.windows 1 200)),
  ("translated 300 24",     real (.translated 300 24)),
  ("translatedUpTo 500 50", real (.translatedUpTo 500 50)),
  ("windows 2 200",         real (.windows 2 200)),
  ("blocksUpTo 2000",       real (.blocksUpTo 2000)),
  ("translated 2000 132",   real (.translated 2000 132)),
  ("translated 2000 144",   real (.translated 2000 144))]

def range1 (n : Nat) : List Nat := (List.range n).map (· + 1)

def sharedStages : Array (String × (Program → Tag)) := #[
  ("simulator 300",         real (Decider.simulator Zipper 300)),
  ("shared 50 [1..24]",     shared 50 (range1 24)),
  ("windows 1 200",         real (.windows 1 200)),
  ("shared 300 [24]",       shared 300 [24]),
  ("shared 500 [1..50]",    shared 500 (range1 50)),
  ("windows 2 200",         real (.windows 2 200)),
  ("blocksUpTo 2000",       real (.blocksUpTo 2000)),
  ("shared 2000 [132]",     shared 2000 [132]),
  ("shared 2000 [144]",     shared 2000 [144])]


/-! Draft of `windows` on hash sets: the same round-by-round fixpoint as `Windows.grow`,
so it should settle exactly the same programs, without the quadratic list operations. -/

instance : Hashable Windows.Loc :=
  ⟨fun s => mixHash (hash s.prog) (mixHash (hash s.left) (mixHash (hash s.head) (hash s.right)))⟩

open Windows in
def succsH (LS RS : Std.HashSet (List Bool)) (s : Loc) : List Loc :=
  match s.prog with
  | .nil        => []
  | .gap _ _ _ => []
  | .flip p    => [⟨p, s.left, !s.head, s.right⟩]
  | .loop b q  => [⟨if s.head then b ++ .loop b q else q, s.left, s.head, s.right⟩]
  | .right p   =>
    ([false, true].filter fun (x : Bool) => RS.contains (s.right.tail ++ [x])).map fun (x : Bool) =>
      ⟨p, s.head :: s.left.dropLast, s.right.headD false, s.right.tail ++ [x]⟩
  | .left p    =>
    ([false, true].filter fun (x : Bool) => LS.contains (s.left.tail ++ [x])).map fun (x : Bool) =>
      ⟨p, s.left.tail ++ [x], s.left.headD false, s.head :: s.right.dropLast⟩

open Windows in
def gramOKH (LS RS : Std.HashSet (List Bool)) (s : Loc) : Bool :=
  match s.prog with
  | .right _ => LS.contains (s.head :: s.left.dropLast)
  | .left _  => RS.contains (s.head :: s.right.dropLast)
  | _        => true

open Windows in
def checkFast (m fuel : Nat) (q : Program) : Bool := Id.run do
  let z := zeros m
  let mut S  : Std.HashSet Loc := (∅ : Std.HashSet Loc).insert ⟨q, z, false, z⟩
  let mut LS : Std.HashSet (List Bool) := (∅ : Std.HashSet (List Bool)).insert z
  let mut RS : Std.HashSet (List Bool) := (∅ : Std.HashSet (List Bool)).insert z
  for _ in [0:fuel] do
    let mut S' := S
    let mut LS' := LS
    let mut RS' := RS
    for s in S do
      for x in succsH LS RS s do S' := S'.insert x
      match s.prog with
      | .right _ => LS' := LS'.insert (s.head :: s.left.dropLast)
      | .left _  => RS' := RS'.insert (s.head :: s.right.dropLast)
      | _        => pure ()
    let stop := (S'.size == S.size && LS'.size == LS.size && RS'.size == RS.size) ||
      S'.toList.any (fun s => !s.prog.alive) || 5000 < S'.size
    S := S'; LS := LS'; RS := RS'
    if stop then break
  return S.toList.all fun s => s.prog.alive && (succsH LS RS s).all S.contains && gramOKH LS RS s

def fastWindows (m fuel : Nat) : Program → Tag := fun q =>
  if checkFast m fuel q then .diverges else .unknown

def fastStages : Array (String × (Program → Tag)) := #[
  ("simulator 300",         real (Decider.simulator Zipper 300)),
  ("shared 50 [1..24]",     shared 50 (range1 24)),
  ("fast windows 1 200",    fastWindows 1 200),
  ("shared 300 [24]",       shared 300 [24]),
  ("shared 500 [1..50]",    shared 500 (range1 50)),
  ("fast windows 2 200",    fastWindows 2 200),
  ("blocksUpTo 2000",       real (.blocksUpTo 2000)),
  ("shared 2000 [132]",     shared 2000 [132]),
  ("shared 2000 [144]",     shared 2000 [144])]


open Windows in
/-- Semi-naive version of `checkFast`: each round only expands states that are new, plus the
moving states whose successors depend on a window set that has just grown. Same rounds,
so the same fixpoint. -/
def checkSemi (m fuel : Nat) (q : Program) : Bool := Id.run do
  let z := zeros m
  let init : Loc := ⟨q, z, false, z⟩
  let mut S  : Std.HashSet Loc := (∅ : Std.HashSet Loc).insert init
  let mut LS : Std.HashSet (List Bool) := (∅ : Std.HashSet (List Bool)).insert z
  let mut RS : Std.HashSet (List Bool) := (∅ : Std.HashSet (List Bool)).insert z
  let mut new : Array Loc := #[init]
  let mut lefts : Array Loc := #[]
  let mut rights : Array Loc := #[]
  let mut lsGrew := false
  let mut rsGrew := false
  for _ in [0:fuel] do
    let mut frontier := new
    if lsGrew then frontier := frontier ++ lefts
    if rsGrew then frontier := frontier ++ rights
    let mut S' := S
    let mut added : Array Loc := #[]
    for s in frontier do
      for x in succsH LS RS s do
        if !S'.contains x then
          S' := S'.insert x
          added := added.push x
    let mut LS' := LS
    let mut RS' := RS
    for s in new do
      match s.prog with
      | .right _ => LS' := LS'.insert (s.head :: s.left.dropLast); rights := rights.push s
      | .left _  => RS' := RS'.insert (s.head :: s.right.dropLast); lefts := lefts.push s
      | _        => pure ()
    lsGrew := LS'.size != LS.size
    rsGrew := RS'.size != RS.size
    let stop := (added.isEmpty && !lsGrew && !rsGrew) ||
      added.any (fun s => !s.prog.alive) || 5000 < S'.size
    S := S'; LS := LS'; RS := RS'; new := added
    if stop then break
  return S.toList.all fun s => s.prog.alive && (succsH LS RS s).all S.contains && gramOKH LS RS s

def semiWindows (m fuel : Nat) : Program → Tag := fun q =>
  if checkSemi m fuel q then .diverges else .unknown

def semiStages : Array (String × (Program → Tag)) :=
  fastStages.map fun (nm, f) =>
    if nm == "fast windows 1 200" then ("semi windows 1 200", semiWindows 1 200)
    else if nm == "fast windows 2 200" then ("semi windows 2 200", semiWindows 2 200)
    else (nm, f)

structure Stat where
  calls : Nat := 0
  ns    : Nat := 0
  halts : Nat := 0
  div   : Nat := 0
  stuck : Nat := 0
  deriving Inhabited

instance : Inhabited (Program → Tag) := ⟨fun _ => .unknown⟩

@[noinline] def runStage (f : Program → Tag) (q : Program) : IO Tag := pure (f q)

def gapAt (q : Program) (i : Nat) : Option (Fin q.numGaps) :=
  if h : i < q.numGaps then some ⟨i, h⟩ else none

partial def loop (stages : Array (String × (Program → Tag))) (B : Nat) (todo : List Program)
    (stats : Array Stat) (nodes left : Nat) : IO (Array Stat × Nat × Nat) := do
  match todo with
  | [] => return (stats, nodes, left)
  | q :: rest =>
    let mut stats := stats
    let mut next := rest
    let mut left := left
    let mut decided := false
    for j in [0:stages.size] do
      if decided then break
      let s ← IO.monoNanosNow
      let v ← runStage stages[j]!.2 q
      let e ← IO.monoNanosNow
      let st := stats[j]!
      let st := { st with calls := st.calls + 1, ns := st.ns + (e - s) }
      match v with
      | .halts t =>
        stats := stats.set! j { st with halts := st.halts + 1 }
        if t > B then left := left + 1
        decided := true
      | .diverges =>
        stats := stats.set! j { st with div := st.div + 1 }
        decided := true
      | .stuck i =>
        stats := stats.set! j { st with stuck := st.stuck + 1 }
        match gapAt q i with
        | some g => next := Expander.tnf.expand q g ++ next
        | none   => left := left + 1
        decided := true
      | .unknown =>
        stats := stats.set! j st
    if !decided then left := left + 1
    loop stages B next stats (nodes + 1) left

/-- How many simulator steps are spent per node, and how many of them repeat the parent's prefix. -/
partial def prefixLoop (todo : List (Program × Nat)) (total pre nodes : Nat) : Nat × Nat × Nat :=
  match todo with
  | [] => (total, pre, nodes)
  | (q, parent) :: rest =>
    let (m, k) := Machine.run 300 (q.init Zipper) 0
    let total := total + k
    let pre := pre + parent
    match fullChain q with
    | .stuck i => prefixLoop ((Expander.tnf.expand q i).map (·, k) ++ rest) total pre (nodes + 1)
    | _        => let _ := m; prefixLoop rest total pre (nodes + 1)

@[noinline] def runPrefix (n : Nat) : IO (Nat × Nat × Nat) := pure (prefixLoop [(Program.gap? n, 0)] 0 0 0)


/-! Draft of resuming children from the parent's run (no proofs). A node carries the
machine its parent was stuck in; a child fills every copy of the stuck gap with its shape
and keeps simulating from the same step. -/

/-- Fill every gap whose id is `i` with `s`, renumbering ids for the child `q[i ↦ s]`
(`g` = number of gaps in `s`). The state is (ids still to consume, ids of the new program). -/
partial def fillIds (i g : Nat) (s : Program) : Program → StateM (List Nat × Array Nat) Program
  | .nil       => pure .nil
  | .left p    => .left <$> fillIds i g s p
  | .right p   => .right <$> fillIds i g s p
  | .flip p    => .flip <$> fillIds i g s p
  | .loop b p  => do
    let b' ← fillIds i g s b
    let p' ← fillIds i g s p
    pure (.loop b' p')
  | .gap k h p => do
    let (ids, out) ← get
    let id := ids.headD 0
    if id == i then
      set (ids.tail, out ++ ((List.range g).map (· + i)).toArray)
      let p' ← fillIds i g s p
      pure (s ++ p')
    else
      set (ids.tail, out.push (if id < i then id else id + g - 1))
      let p' ← fillIds i g s p
      pure (.gap k h p')

structure Run where
  m   : Machine Zipper
  j   : Nat
  ids : List Nat
  deriving Inhabited

inductive SimRes where
  | halts (t : Nat) | stuck (i : Nat) (r : Run) | unknown
  deriving Inhabited

/-- Continue the simulator from `r` until `limit` total steps. -/
partial def simFrom (limit : Nat) (r : Run) : SimRes :=
  match r.m.prog with
  | .nil       => .halts r.j
  | .gap _ _ _ => .stuck (r.ids.headD 0) r
  | _ =>
    if r.j ≥ limit then .unknown else
    match Machine.step r.m with
    | none    => .unknown
    | some m' => simFrom limit ⟨m', r.j + 1, Machine.nextIds r.m r.ids⟩

/-- Fast path: no id bookkeeping. Returns the last machine and step count. -/
partial def runFast (limit : Nat) (m : Machine Zipper) (j : Nat) : Machine Zipper × Nat :=
  if j ≥ limit then (m, j) else
  match Machine.step m with
  | none    => (m, j)
  | some m' => runFast limit m' (j + 1)

/-- Like the real simulator: run fast, and only if a gap is hit, rerun from `r` tracking ids. -/
def simFrom2 (limit : Nat) (r : Run) : SimRes :=
  let (m, j) := runFast limit r.m r.j
  match m.prog with
  | .nil       => .halts j
  | .gap _ _ _ => simFrom limit r
  | _          => .unknown

@[noinline] def runSim (limit : Nat) (r : Run) : IO SimRes := pure (simFrom2 limit r)

partial def resumeLoop (rest : Array (String × (Program → Tag))) (B : Nat)
    (todo : List (Program × Run)) (simNs : Nat) (stats : Array Stat) (nodes left h st : Nat)
    (maxT : Nat := 0) : IO (Nat × Array Stat × Nat × Nat × Nat × Nat × Nat) := do
  match todo with
  | [] => return (simNs, stats, nodes, left, h, st, maxT)
  | (q, r) :: more =>
    let s0 ← IO.monoNanosNow
    let res ← runSim 300 r
    let s1 ← IO.monoNanosNow
    let simNs := simNs + (s1 - s0)
    match res with
    | .halts t =>
      resumeLoop rest B more simNs stats (nodes + 1) (if t > B then left + 1 else left) (h + 1) st (max maxT t)
    | .stuck i r' =>
      match gapAt q i with
      | none => resumeLoop rest B more simNs stats (nodes + 1) (left + 1) h (st + 1) maxT
      | some gi =>
        let shapes := Program.shapes q.noShift (Program.gapSize q gi)
        let kids := shapes.map fun (sh : Program) =>
          let (p', (_, ids')) := (fillIds i sh.numGaps sh r'.m.prog).run (r'.ids, #[])
          (Program.subst i sh q, ({ m := ⟨r'.m.tape, p'⟩, j := r'.j, ids := ids'.toList } : Run))
        resumeLoop rest B (kids ++ more) simNs stats (nodes + 1) left h (st + 1) maxT
    | .unknown =>
      let mut stats := stats
      let mut decided := false
      let mut left := left
      for jx in [0:rest.size] do
        if decided then break
        let a ← IO.monoNanosNow
        let v ← runStage rest[jx]!.2 q
        let b ← IO.monoNanosNow
        let sj := stats[jx]!
        let sj := { sj with calls := sj.calls + 1, ns := sj.ns + (b - a) }
        match v with
        | .diverges => stats := stats.set! jx { sj with div := sj.div + 1 }; decided := true
        | _         => stats := stats.set! jx sj
      if !decided then left := left + 1
      resumeLoop rest B more simNs stats (nodes + 1) left h st maxT

def main (args : List String) : IO Unit := do
  let mode := args.headD "base"
  let n := (args.getD 1 "14").toNat!
  let B := match n with | 12 => 72 | 13 => 120 | 14 => 158 | 15 => 276 | _ => 1000
  if mode == "resume" then
    let rest := semiStages.extract 1 semiStages.size
    let q0 := Program.gap? n
    let r0 : Run := { m := q0.init Zipper, j := 0, ids := List.range q0.numGaps }
    let t0 ← IO.monoMsNow
    let (simNs, stats, nodes, left, h, st, maxT) ← resumeLoop rest B [(q0, r0)] 0 (rest.map fun _ => {}) 0 0 0 0
    let t1 ← IO.monoMsNow
    IO.println s!"resume BB({n}): {t1 - t0} ms, nodes {nodes}, unresolved {left}, longest halt {maxT} (bound {B})"
    IO.println s!"  simulator (resumed)      {simNs / 1000000} ms  h={h} s={st}"
    for j in [0:rest.size] do
      let x := stats[j]!
      let nm := rest[j]!.1
      IO.println s!"  {nm.pushn ' ' (24 - nm.length)} calls={x.calls} {x.ns / 1000000} ms  d={x.div}"
    return
  if mode == "prefix" then
    let (total, pre, nodes) ← runPrefix n
    IO.println s!"nodes {nodes}, simulator steps {total}, of them repeating the parent's prefix {pre} ({pre * 100 / total}%)"
    return
  let stages := if mode == "shared" then sharedStages else if mode == "fast" then fastStages else if mode == "semi" then semiStages else baseStages
  let t0 ← IO.monoMsNow
  let (stats, nodes, left) ← loop stages B [Program.gap? n] (stages.map fun _ => {}) 0 0
  let t1 ← IO.monoMsNow
  IO.println s!"{mode} BB({n}): {t1 - t0} ms, nodes {nodes}, unresolved {left}"
  for j in [0:stages.size] do
    let st := stats[j]!
    let nm := stages[j]!.1
    IO.println s!"  {nm.pushn ' ' (24 - nm.length)} calls={st.calls} {st.ns / 1000000} ms  h={st.halts} d={st.div} s={st.stuck}"
