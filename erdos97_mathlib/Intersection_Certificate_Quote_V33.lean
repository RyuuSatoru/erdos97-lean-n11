import Mask_Intersection_Checker_V33
import Lean
set_option autoImplicit false
namespace T33WalkQuote
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
private def readMask (bytes : ByteArray) (start : Nat) : Except String Nat := do
  let mut mask := 0
  for i in [:9] do
    let part ← token bytes (start+i)
    mask := mask + part * 2^(24*i)
  return mask

private partial def quoteNode (bytes : ByteArray) (fuel start : Nat) : Except String (Expr × Nat) := do
  if fuel = 0 then throw "certificate depth exceeded"
  let natTy := mkConst ``Nat
  let certTy := mkConst ``T33Checker.Certificate
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
      pure (mkAppN (mkConst ``T33Checker.Certificate.flow)
        #[listExpr pairTy terms,listExpr receiptTy receipts])
    | 1 => do
      let center ← token bytes pos
      pos := pos+1
      let mask ← readMask bytes pos
      pos := pos+9
      pure (mkAppN (mkConst ``T33Checker.Certificate.empty) #[mkNatLit center,mkNatLit mask])
    | 2 => do
      let center ← token bytes pos
      let count ← token bytes (pos+1)
      pos := pos+2
      let mask ← readMask bytes pos
      pos := pos+9
      if count > 210 then throw "child count exceeded"
      let mut children : Array Expr := #[]
      for _ in [:count] do
        let row ← token bytes pos
        let (child,finish) ← quoteNode bytes (fuel-1) (pos+1)
        pos := finish
        children := children.push (prodExpr natTy certTy (mkNatLit row) child)
      pure (mkAppN (mkConst ``T33Checker.Certificate.branch)
        #[mkNatLit center,mkNatLit mask,listExpr (prodType natTy certTy) children])
    | _ => throw s!"unknown node tag {tag}"
  if pos ≠ expectedEnd then throw s!"node end mismatch at {start}: {pos} versus {expectedEnd}"
  return (result,pos)

private initialize fileCache : IO.Ref (Option (String × ByteArray)) ← IO.mkRef none

open Lean Elab Term in
elab "e97IntersectionCertificate " file:str " at " start:num : term => do
  let cached ← fileCache.get
  let bytes ← match cached with
    | some (name,bytes) =>
      if name == file.getString then pure bytes else do
        let bytes ← IO.FS.readBinFile file.getString
        fileCache.set (some (file.getString,bytes))
        pure bytes
    | none => do
      let bytes ← IO.FS.readBinFile file.getString
      fileCache.set (some (file.getString,bytes))
      pure bytes
  match quoteNode bytes 12 start.getNat with
  | .ok (result,_) => pure result
  | .error message => throwError "{message}"

end T33WalkQuote
