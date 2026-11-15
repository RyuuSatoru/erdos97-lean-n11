import Walk_TypedChecker_V22
import Thin_Checker_V29
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace E97ThinBridge29

def pairToOld (h : T29E97PairGuard15.PairHint) : E97PairGuard15.PairHint := ⟨h.slot,h.code⟩
def a2ToOld (h : T29E97A2Guard14.A2Hint) : E97A2Guard14.A2Hint :=
  ⟨h.rowA,h.rowB,h.rowC,h.witnessU,h.witnessV⟩
def hintsToOld (h : T29E97TypedChecker15.CandidateHints) : E97TypedChecker15.CandidateHints :=
  ⟨h.a2.map a2ToOld,h.pair.map pairToOld⟩
def providerToOld (hints : T29E97TypedChecker15.HintProvider) : E97TypedChecker15.HintProvider :=
  fun path r => hintsToOld (hints path r)

theorem rowAt_eq (r : Nat) : T29E97Packed18.rowAt r = E97Packed18.rowAt r := by rfl
theorem quadAt_eq (q : Nat) : T29E97Packed18.quadAt q = E97Packed18.quadAt q := by rfl
theorem fastPair_scan : (List.range 55).all (fun i => decide
    (T29E97FastLookup17.fastPairAt i = E97FastLookup17.fastPairAt i)) = true := by decide +kernel
theorem fastPairAt_eq (i : Nat) : T29E97FastLookup17.fastPairAt i = E97FastLookup17.fastPairAt i := by
  by_cases hi : i < 55
  · exact decide_eq_true_eq.mp ((List.all_eq_true.mp fastPair_scan) i (List.mem_range.mpr hi))
  · simp only [T29E97FastLookup17.fastPairAt,hi,ite_false]
    rfl
theorem chooseK_eq (k : Nat) (vs : List Nat) :
    T29E97AllowFinite.chooseK k vs = E97AllowFinite.chooseK k vs := by
  induction vs generalizing k with
  | nil => cases k <;> rfl
  | cons x xs ih =>
    cases k <;> simp only [T29E97AllowFinite.chooseK,E97AllowFinite.chooseK,ih]
theorem witnessFour_eq (c k : Nat) :
    T29E97AllowFinite.witnessFour c k = E97AllowFinite.witnessFour c k := by
  simp only [T29E97AllowFinite.witnessFour,E97AllowFinite.witnessFour,chooseK_eq]
theorem fastWitnessFour_eq (c k : Nat) :
    T29E97FastLookup17.fastWitnessFour c k = E97FastLookup17.fastWitnessFour c k := by
  simp only [T29E97FastLookup17.fastWitnessFour,E97FastLookup17.fastWitnessFour,witnessFour_eq]
  rfl
theorem fastRowMask_eq (c k : Nat) :
    T29E97FastLookup17.fastRowMask c k = E97FastLookup17.fastRowMask c k := by
  simp only [T29E97FastLookup17.fastRowMask,E97FastLookup17.fastRowMask,fastWitnessFour_eq]
theorem rowMask_eq (c k : Nat) :
    T29E97FastTables19.rowMask c k = E97FastTables19.rowMask c k := by
  simp only [T29E97FastTables19.rowMask,E97FastTables19.rowMask,fastRowMask_eq]
  rfl
theorem fastCellData_eq (i : Nat) : T29E97FastTables19.fastCellData i = E97FastTables19.fastCellData i := by
  simp only [T29E97FastTables19.fastCellData,E97FastTables19.fastCellData,fastPairAt_eq,rowMask_eq]

theorem pattern_fields_eq (id : Nat) :
    ((T29E97FastTables19.fastPatternAt id).c,(T29E97FastTables19.fastPatternAt id).d,
      (T29E97FastTables19.fastPatternAt id).mc,(T29E97FastTables19.fastPatternAt id).md) =
    ((E97FastTables19.fastPatternAt id).c,(E97FastTables19.fastPatternAt id).d,
      (E97FastTables19.fastPatternAt id).mc,(E97FastTables19.fastPatternAt id).md) := by
  by_cases h : id % 2 = 0 <;>
    simp only [T29E97FastTables19.fastPatternAt,E97FastTables19.fastPatternAt,h,ite_true,ite_false] <;> rfl
theorem pattern_c_eq (id : Nat) :
    (T29E97FastTables19.fastPatternAt id).c = (E97FastTables19.fastPatternAt id).c :=
  congrArg Prod.fst (pattern_fields_eq id)
theorem pattern_d_eq (id : Nat) :
    (T29E97FastTables19.fastPatternAt id).d = (E97FastTables19.fastPatternAt id).d :=
  congrArg (fun x => x.2.1) (pattern_fields_eq id)
theorem pattern_mc_eq (id : Nat) :
    (T29E97FastTables19.fastPatternAt id).mc = (E97FastTables19.fastPatternAt id).mc :=
  congrArg (fun x => x.2.2.1) (pattern_fields_eq id)
theorem pattern_md_eq (id : Nat) :
    (T29E97FastTables19.fastPatternAt id).md = (E97FastTables19.fastPatternAt id).md :=
  congrArg (fun x => x.2.2.2) (pattern_fields_eq id)

theorem fastCheckReason_eq (slot code : Nat) :
    T29E97FastTables19.fastCheckReason slot code = E97FastTables19.fastCheckReason slot code := by
  simp only [T29E97FastTables19.fastCheckReason,E97FastTables19.fastCheckReason,
    fastCellData_eq,fastPairAt_eq,pattern_c_eq,pattern_d_eq,pattern_mc_eq,pattern_md_eq]
  rfl

theorem fastCenterA_eq (slot : Nat) :
    T29E97FastTables19.fastCenterA slot = E97FastTables19.fastCenterA slot := by
  simp only [T29E97FastTables19.fastCenterA,E97FastTables19.fastCenterA,fastPairAt_eq]
theorem fastCenterB_eq (slot : Nat) :
    T29E97FastTables19.fastCenterB slot = E97FastTables19.fastCenterB slot := by
  simp only [T29E97FastTables19.fastCenterB,E97FastTables19.fastCenterB,fastPairAt_eq]

theorem checkedPair_eq (path : List Nat) (r : Nat) (h : T29E97PairGuard15.PairHint) :
    T29E97FastTables19.fastCheckedPair path r h =
      E97FastTables19.fastCheckedPair path r (pairToOld h) := by
  cases h
  simp only [T29E97FastTables19.fastCheckedPair,E97FastTables19.fastCheckedPair,pairToOld,
    fastCheckReason_eq,fastCenterA_eq,fastCenterB_eq]
  rfl

theorem checkedA2_eq (path : List Nat) (h : T29E97A2Guard14.A2Hint) :
    T29E97FastChecker19.checkedA2 path h = E97FastChecker19.checkedA2 path (a2ToOld h) := by
  cases h
  rfl

theorem guardedAllows_eq (path : List Nat) (r : Nat) (h : T29E97TypedChecker15.CandidateHints) :
    T29E97FastChecker19.guardedAllows path r h =
      E97FastChecker19.guardedAllows path r (hintsToOld h) := by
  cases h with
  | mk a2 pair =>
    cases a2 <;> cases pair <;>
      simp only [T29E97FastChecker19.guardedAllows,E97FastChecker19.guardedAllows,hintsToOld,
        T29E97FastChecker19.guardedA2Allows,E97FastChecker19.guardedA2Allows,
        Option.map_none,Option.map_some,checkedPair_eq,checkedA2_eq]

theorem candidateRows_eq (hints : T29E97TypedChecker15.HintProvider) (path : List Nat) (c : Nat) :
    T29E97FastChecker19.candidateRows hints path c =
      E97FastChecker19.candidateRows (providerToOld hints) path c := by
  simp only [T29E97FastChecker19.candidateRows,E97FastChecker19.candidateRows,guardedAllows_eq,providerToOld]

theorem rowContains_eq (r e : Nat) :
    T29E97EdgeWalk22.rowContains r e = E97EdgeWalk22.rowContains r e := by rfl
theorem checkWalk_eq (path : List Nat) (start finish : Nat) (steps : List (Nat × Nat)) :
    T29E97EdgeWalk22.checkWalk path start finish steps = E97EdgeWalk22.checkWalk path start finish steps := by
  induction steps generalizing start with
  | nil => rfl
  | cons step rest ih =>
    rcases step with ⟨r,next⟩
    simp only [T29E97EdgeWalk22.checkWalk,E97EdgeWalk22.checkWalk,rowContains_eq,ih]
theorem checkPairings_eq (path : List Nat) (es : List Nat) (rs : List T29E97EdgeWalk22.Receipt) :
    T29E97EdgeWalk22.checkPairings path es rs = E97EdgeWalk22.checkPairings path es rs := by
  induction es generalizing rs with
  | nil => cases rs <;> rfl
  | cons e es ih =>
    cases rs with
    | nil => rfl
    | cons r rs =>
      rcases r with ⟨finish,steps⟩
      simp only [T29E97EdgeWalk22.checkPairings,E97EdgeWalk22.checkPairings,checkWalk_eq,ih]
theorem positiveEdges_eq (ts : List (Nat × Nat)) :
    T29E97EdgeWalk22.positiveEdges ts = E97EdgeWalk22.positiveEdges ts := by
  induction ts with
  | nil => rfl
  | cons qw ts ih =>
    rcases qw with ⟨q,w⟩
    simp only [T29E97EdgeWalk22.positiveEdges,E97EdgeWalk22.positiveEdges,quadAt_eq,ih]
theorem negativeEdges_eq (ts : List (Nat × Nat)) :
    T29E97EdgeWalk22.negativeEdges ts = E97EdgeWalk22.negativeEdges ts := by
  induction ts with
  | nil => rfl
  | cons qw ts ih =>
    rcases qw with ⟨q,w⟩
    simp only [T29E97EdgeWalk22.negativeEdges,E97EdgeWalk22.negativeEdges,quadAt_eq,ih]
theorem insertEdge_eq (x : Nat) (xs : List Nat) :
    T29E97Sparse20.insertEdge x xs = E97Sparse20.insertEdge x xs := by
  induction xs with
  | nil => rfl
  | cons y ys ih => simp only [T29E97Sparse20.insertEdge,E97Sparse20.insertEdge,ih]
theorem sortEdges_eq (xs : List Nat) :
    T29E97Sparse20.sortEdges xs = E97Sparse20.sortEdges xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [T29E97Sparse20.sortEdges,E97Sparse20.sortEdges,insertEdge_eq,ih]
theorem checkedFlow_eq (path : List Nat) (ts : List (Nat × Nat))
    (receipts : List T29E97EdgeWalk22.Receipt) :
    T29E97EdgeWalk22.checkedFlow path ts receipts = E97EdgeWalk22.checkedFlow path ts receipts := by
  simp only [T29E97EdgeWalk22.checkedFlow,E97EdgeWalk22.checkedFlow,positiveEdges_eq,
    negativeEdges_eq,checkPairings_eq,sortEdges_eq]

def certificateToOld (fuel : Nat) (cert : T29E97WalkChecker22.Certificate) : E97WalkChecker22.Certificate :=
  match fuel with
  | 0 => .flow [] []
  | n+1 => match cert with
    | .flow ts rs => .flow ts rs
    | .empty c => .empty c
    | .branch c children => .branch c (children.map (fun ch => (ch.1,certificateToOld n ch.2)))

theorem checkTree_eq (fuel : Nat) (hints : T29E97TypedChecker15.HintProvider) (path : List Nat)
    (cert : T29E97WalkChecker22.Certificate) :
    T29E97WalkChecker22.checkTree fuel hints path cert =
      E97WalkChecker22.checkTree fuel (providerToOld hints) path (certificateToOld fuel cert) := by
  induction fuel generalizing path cert with
  | zero => rfl
  | succ n ih =>
    cases cert <;>
      simp only [T29E97WalkChecker22.checkTree,E97WalkChecker22.checkTree,certificateToOld,
        T29E97WalkChecker22.candidateRows,E97WalkChecker22.candidateRows,
        candidateRows_eq,checkedFlow_eq,List.map_map,List.all_map,Function.comp_def,ih]

theorem accepted_to_old (fuel : Nat) (hints : T29E97TypedChecker15.HintProvider) (path : List Nat)
    (cert : T29E97WalkChecker22.Certificate)
    (hcheck : T29E97WalkChecker22.checkTree fuel hints path cert = true) :
    E97WalkChecker22.checkTree fuel (providerToOld hints) path (certificateToOld fuel cert) = true :=
  (checkTree_eq fuel hints path cert).symm.trans hcheck

theorem checked_tree_forbids_assignment (P : Fin 11 → E97BlockB.XY)
    (hccw : E97A1Index.StrictCCW11 P) (assignment : Nat → Nat)
    (hworld : E97TypedChecker15.AssignmentRealized P assignment)
    (hints : T29E97TypedChecker15.HintProvider) (fuel : Nat) (path : List Nat)
    (cert : T29E97WalkChecker22.Certificate) (hp : E97TypedChecker15.PrefixRealized P path)
    (hcheck : T29E97WalkChecker22.checkTree fuel hints path cert = true) : False := by
  exact E97WalkChecker22.checked_tree_forbids_assignment P hccw assignment hworld
    (providerToOld hints) fuel path (certificateToOld fuel cert) hp
    (accepted_to_old fuel hints path cert hcheck)

#print axioms E97ThinBridge29.rowAt_eq
#print axioms E97ThinBridge29.quadAt_eq
#print axioms E97ThinBridge29.fastCheckReason_eq
#print axioms E97ThinBridge29.checkedPair_eq
#print axioms E97ThinBridge29.checkedA2_eq
#print axioms E97ThinBridge29.checkedFlow_eq
#print axioms E97ThinBridge29.checkTree_eq
#print axioms E97ThinBridge29.checked_tree_forbids_assignment
end E97ThinBridge29
