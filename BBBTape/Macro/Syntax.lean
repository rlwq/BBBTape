import Lean
import BBBTape.Core.Program

namespace BBBTape

open Lean Elab Term Meta
open scoped Program

/-- `ToExpr` cannot be derived because of the proof inside `gap`, so it is written by hand. -/
def Program.toExprImpl : Program → Expr
  | ε           => mkConst ``Program.nil
  | .left p     => mkApp (mkConst ``Program.left) p.toExprImpl
  | .right p    => mkApp (mkConst ``Program.right) p.toExprImpl
  | .flip p     => mkApp (mkConst ``Program.flip) p.toExprImpl
  | .loop b p   => mkApp2 (mkConst ``Program.loop) b.toExprImpl p.toExprImpl
  | .gap 0 h _  => absurd h (Nat.lt_irrefl 0)
  | .gap (k + 1) _ p =>
    mkApp3 (mkConst ``Program.gap) (toExpr (k + 1)) (mkApp (mkConst ``Nat.succ_pos) (toExpr k))
      p.toExprImpl

instance : ToExpr Program where
  toExpr     := Program.toExprImpl
  toTypeExpr := mkConst ``Program

partial def Program.parse : List Char → Option (Program × List Char)
  | []        => some (ε, [])
  | ']' :: cs => some (ε, ']' :: cs)
  | '<' :: cs => (parse cs).map fun (r : Program × List Char) => (.left r.1, r.2)
  | '>' :: cs => (parse cs).map fun (r : Program × List Char) => (.right r.1, r.2)
  | '*' :: cs => (parse cs).map fun (r : Program × List Char) => (.flip r.1, r.2)
  | '[' :: cs =>
    match parse cs with
    | some (b, ']' :: rest) => (parse rest).map fun (r : Program × List Char) => (.loop b r.1, r.2)
    | _ => none
  | _ => none

elab "bf" noWs s:str : term => do
  match Program.parse s.getString.toList with
  | some (p, []) => return toExpr p
  | _ => throwErrorAt s "not a program over <>*[]"

end BBBTape
