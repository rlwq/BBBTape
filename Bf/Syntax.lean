import Lean
import Bf.Program

namespace Bf

open Lean Elab Term Meta

deriving instance ToExpr for Program

partial def Program.parse : List Char → Option (Program × List Char)
  | []        => some (.nil, [])
  | ']' :: cs => some (.nil, ']' :: cs)
  | '<' :: cs => (parse cs).map fun (r : Program × List Char) => (.left r.1, r.2)
  | '>' :: cs => (parse cs).map fun (r : Program × List Char) => (.right r.1, r.2)
  | '*' :: cs => (parse cs).map fun (r : Program × List Char) => (.flip r.1, r.2)
  | '[' :: cs =>
    match parse cs with
    | some (b, ']' :: rest) => (parse rest).map fun (r : Program × List Char) => (.loop b r.1, r.2)
    | _ => none
  | _ => none

elab "bf!" s:str : term => do
  match Program.parse s.getString.toList with
  | some (p, []) => return toExpr p
  | _ => throwErrorAt s "not a program over <>*[]"

end Bf
