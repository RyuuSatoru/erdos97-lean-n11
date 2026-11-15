import Fast_TypedChecker_V19
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace E97Sparse20
open E97Packed18

def insertEdge (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insertEdge x ys
def sortEdges : List Nat → List Nat
  | [] => []
  | x :: xs => insertEdge x (sortEdges xs)
theorem insertEdge_perm (x : Nat) (xs : List Nat) : (insertEdge x xs).Perm (x :: xs) := by
  induction xs with
  | nil => exact List.Perm.refl _
  | cons y ys ih =>
    unfold insertEdge
    split
    · exact List.Perm.refl _
    · exact (List.Perm.cons y ih).trans (List.Perm.swap x y ys)
theorem sortEdges_perm (xs : List Nat) : (sortEdges xs).Perm xs := by
  induction xs with
  | nil => exact List.Perm.refl _
  | cons x xs ih =>
    exact (insertEdge_perm x (sortEdges xs)).trans (List.Perm.cons x ih)

def positiveEdges (cs : Array Nat) : List (Nat × Nat) → List Nat
  | [] => []
  | (q,w) :: rest =>
    let (a,b,_,_) := quadAt q
    List.replicate w ((cs[a]?).getD a) ++
      List.replicate w ((cs[b]?).getD b) ++ positiveEdges cs rest
def negativeEdges (cs : Array Nat) : List (Nat × Nat) → List Nat
  | [] => []
  | (q,w) :: rest =>
    let (_,_,c,d) := quadAt q
    List.replicate w ((cs[c]?).getD c) ++
      List.replicate w ((cs[d]?).getD d) ++ negativeEdges cs rest

theorem count_balance (cs : Array Nat) (ts : List (Nat × Nat)) (e : Nat) (acc : Int) :
    ts.foldl (fun a qw => a + (qw.2 : Int) * reducedCoeff cs qw.1 e) acc =
      acc + ((positiveEdges cs ts).count e : Int) - ((negativeEdges cs ts).count e : Int) := by
  induction ts generalizing acc with
  | nil => simp [positiveEdges,negativeEdges]
  | cons qw ts ih =>
    rcases qw with ⟨q,w⟩
    simp only [List.foldl_cons]
    rw [ih]
    rcases hq : quadAt q with ⟨a,b,c,d⟩
    simp only [positiveEdges,negativeEdges,hq,List.count_append,List.count_replicate,
      Nat.cast_add,reducedCoeff]
    split_ifs <;> ring

def checkedF (cs : Array Nat) (ts : List (Nat × Nat)) : Bool :=
  (!ts.isEmpty) &&
  ts.all (fun qw => decide (qw.1 < 660 ∧ 0 < qw.2 ∧ qw.2 ≤ 1000000)) &&
  decide (sortEdges (positiveEdges cs ts) = sortEdges (negativeEdges cs ts))

theorem checkedF_sound (cs : Array Nat) (ts : List (Nat × Nat))
    (h : checkedF cs ts = true) : E97TreeKF4.checkedF cs ts = true := by
  have hh := h
  simp only [checkedF,Bool.and_eq_true,decide_eq_true_eq] at hh
  have hp := (sortEdges_perm (positiveEdges cs ts)).symm
  have hn := sortEdges_perm (negativeEdges cs ts)
  have hperm : (positiveEdges cs ts).Perm (negativeEdges cs ts) := by
    apply hp.trans
    rw [hh.2]
    exact hn
  simp only [E97TreeKF4.checkedF,Bool.and_eq_true]
  refine ⟨hh.1, List.all_eq_true.mpr ?_⟩
  intro e _
  apply decide_eq_true_eq.mpr
  have hb := count_balance cs ts e 0
  rw [hperm.count_eq e] at hb
  simpa only [E97Packed18.reducedCoeff_eq,Int.ofNat_eq_natCast,zero_add,sub_self] using hb

#print axioms E97Sparse20.count_balance
#print axioms E97Sparse20.checkedF_sound
end E97Sparse20
