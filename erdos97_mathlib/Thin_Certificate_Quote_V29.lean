import Thin_Checker_V29
import Lean
set_option autoImplicit false
namespace T29WalkQuote
open Lean

private def listExpr (ty : Expr) (xs : Array Expr) : Expr :=
  xs.foldr (fun x rest => mkAppN (mkConst ``List.cons [Level.zero]) #[ty,x,rest])
    (mkApp (mkConst ``List.nil [Level.zero]) ty)
private def prodType (a b : Expr) : Expr := mkAppN (mkConst ``Prod [Level.zero,Level.zero]) #[a,b]
private def prodExpr (a b x y : Expr) : Expr := mkAppN (mkConst ``Prod.mk [Level.zero,Level.zero]) #[a,b,x,y]
private def token (bytes : ByteArray) (i : Nat) : Except String Nat :=
  if 3*i+2 < bytes.size then
    .ok (bytes[3*i]!.toNat + 256*bytes[3*i+1]!.toNat + 65536*bytes[3*i+2]!.toNat)
  else .error s!"token index {i} outside file"

/-- This elaboration helper produces constructor expressions from untrusted
data. Only the resulting expressions and checker proofs enter the kernel. -/
private partial def quoteNode (bytes : ByteArray) (fuel start : Nat) : Except String (Expr × Nat) := do
  if fuel = 0 then throw "certificate depth exceeded"
  let natTy := mkConst ``Nat
  let certTy := mkConst ``T29E97WalkChecker22.Certificate
  let pairTy := prodType natTy natTy
  let tag ← token bytes start
  let expectedEnd ← token bytes (start+1)
  let mut pos := start+2
  let result ← match tag with
    | 0 => do
      let count ← token bytes pos
      pos := pos+1
      if count > 1000 then throw "term count exceeded"
      let mut terms : Array Expr := #[]
      for _ in [:count] do
        let q ← token bytes pos
        let w ← token bytes (pos+1)
        pos := pos+2
        terms := terms.push (prodExpr natTy natTy (mkNatLit q) (mkNatLit w))
      let countReceipts ← token bytes pos
      pos := pos+1
      if countReceipts > 20000 then throw "receipt count exceeded"
      let receiptTy := prodType natTy (mkApp (mkConst ``List [Level.zero]) pairTy)
      let mut receipts : Array Expr := #[]
      for _ in [:countReceipts] do
        let finish ← token bytes pos
        let countSteps ← token bytes (pos+1)
        pos := pos+2
        if countSteps > 55 then throw "walk length exceeded"
        let mut steps : Array Expr := #[]
        for _ in [:countSteps] do
          let row ← token bytes pos
          let next ← token bytes (pos+1)
          pos := pos+2
          steps := steps.push (prodExpr natTy natTy (mkNatLit row) (mkNatLit next))
        receipts := receipts.push (prodExpr natTy (mkApp (mkConst ``List [Level.zero]) pairTy)
          (mkNatLit finish) (listExpr pairTy steps))
      pure (mkAppN (mkConst ``T29E97WalkChecker22.Certificate.flow)
        #[listExpr pairTy terms,listExpr receiptTy receipts])
    | 1 => do
      let center ← token bytes pos
      pos := pos+1
      pure (mkApp (mkConst ``T29E97WalkChecker22.Certificate.empty) (mkNatLit center))
    | 2 => do
      let center ← token bytes pos
      let count ← token bytes (pos+1)
      pos := pos+2
      if count > 210 then throw "child count exceeded"
      let mut children : Array Expr := #[]
      for _ in [:count] do
        let row ← token bytes pos
        let (child,finish) ← quoteNode bytes (fuel-1) (pos+1)
        pos := finish
        children := children.push (prodExpr natTy certTy (mkNatLit row) child)
      pure (mkAppN (mkConst ``T29E97WalkChecker22.Certificate.branch)
        #[mkNatLit center,listExpr (prodType natTy certTy) children])
    | _ => throw s!"unknown node tag {tag}"
  if pos ≠ expectedEnd then throw s!"node end mismatch at {start}: {pos} versus {expectedEnd}"
  return (result,pos)

open Lean Elab Term in
elab "e97WalkCertificate " file:str " at " start:num : term => do
  let bytes ← IO.FS.readBinFile file.getString
  match quoteNode bytes 12 start.getNat with
  | .ok (result,_) => pure result
  | .error message => throwError "{message}"

end T29WalkQuote
