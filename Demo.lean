import Bf

def report (d : Decider) (n : Nat) (showUnknown : Bool := true) : IO Unit := do
  let labeled := d.label (Program.enumerate n)
  let count (v : Verdict) := (labeled.filter (·.2 == v)).length
  IO.println s!"length {n}: {labeled.length} programs"
  IO.println s!"  halts {count .halts}, nonhalts {count .nonhalts}, unknown {count .unknown}"
  if showUnknown then
    for (p, v) in labeled do
      if v == .unknown then IO.println s!"  ? {p}"

def cyclers (k maxPeriod : Nat) : Decider :=
  .any ((List.range maxPeriod).map fun n => cyclerDecider k (n + 1))

def translated (k maxPeriod : Nat) : Decider :=
  .any ((List.range maxPeriod).map fun n => translatedDecider k (n + 1))

#eval report (Decider.unknown <|> loopFreeDecider <|> simulator 10 <|> cyclers 100 30) 5

#eval report (Decider.unknown) 8
#eval report (Decider.unknown <|> loopFreeDecider) 8
#eval report (Decider.unknown <|> loopFreeDecider <|> simulator 14) 8
#eval report (Decider.unknown <|> loopFreeDecider <|> simulator 14 <|> cyclers 16 16) 8
#eval report (Decider.unknown <|> loopFreeDecider <|> simulator 14 <|> cyclers 16 16 <|> translated 60 60) 8

#eval report (Decider.unknown <|> loopFreeDecider <|> simulator 20 <|> cyclers 16 16 <|> translated 60 60) 9
