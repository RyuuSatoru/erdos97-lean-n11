import Tree_FirstF_RowGeometry_V10_CANDIDATE

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace E97AllRow13
open E97BlockB E97FirstFGeometry10 E97FirstF10

def SpokeShape (p e : Nat) : Prop :=
  let (u,v) := (E97A2Rows.edgeEndpoints[e]?).getD (0,0)
  (u = p / 210 ∧ v ∈ E97A2Prefix.rowWitnessSet p) ∨
    (v = p / 210 ∧ u ∈ E97A2Prefix.rowWitnessSet p)

instance (p e : Nat) : Decidable (SpokeShape p e) := by
  unfold SpokeShape
  infer_instance

def RowSpokes (p : Nat) : Prop :=
  let (a,b,c,d) := E97Flow.getRow p
  SpokeShape p a ∧ SpokeShape p b ∧ SpokeShape p c ∧ SpokeShape p d

instance (p : Nat) : Decidable (RowSpokes p) := by
  unfold RowSpokes
  infer_instance

theorem valid_spoke (p e : Nat) (he : e < 55)
    (hv : E97A2Rows.otherEndpoint (p/210) e < 11)
    (hm : E97A2Rows.otherEndpoint (p/210) e ∈ E97A2Prefix.rowWitnessSet p) :
    SpokeShape p e := by
  have hsize : E97A2Rows.edgeEndpoints.size = 55 := by decide +kernel
  have hin : e < E97A2Rows.edgeEndpoints.size := by omega
  cases hh : E97A2Rows.edgeEndpoints[e]? with
  | none =>
    have hs := Array.getElem?_eq_getElem hin
    rw [hh] at hs
    contradiction
  | some uv =>
    rcases uv with ⟨u,v⟩
    simp only [E97A2Rows.otherEndpoint, hh, Option.getD_some] at hv hm
    simp only [SpokeShape, hh, Option.getD_some]
    by_cases hu : u = p/210
    · left
      exact ⟨hu, by simpa [hu] using hm⟩
    · by_cases hv' : v = p/210
      · right
        exact ⟨hv', by simpa [hu,hv'] using hm⟩
      · simp [hu,hv'] at hv

theorem row_spokes (p : Nat) (hp : p < 2310) : RowSpokes p := by
  have h := E97A2Prefix.actual_row_ok_of_lt p hp
  rcases hh : E97Flow.getRow p with ⟨a,b,c,d⟩
  simp only [E97A2Rows.actualRowOK, E97A2Rows.decodedWitnesses, hh,
    decide_eq_true_eq] at h
  obtain ⟨_,_,ha,hb,hc,hd,h01,h12,h23,h3,_⟩ := h
  simp only [RowSpokes, hh]
  refine ⟨valid_spoke p a ha (by omega) ?_,
    valid_spoke p b hb (by omega) ?_,
    valid_spoke p c hc (by omega) ?_,
    valid_spoke p d hd h3 ?_⟩ <;>
    simp [E97A2Prefix.rowWitnessSet, E97A2Rows.decodedWitnesses, hh]

theorem all_rows_spokes :
    (List.range 2310).all (fun p => decide (RowSpokes p)) = true := by
  apply List.all_eq_true.mpr
  intro p hp
  exact decide_eq_true_eq.mpr (row_spokes p (List.mem_range.mp hp))

theorem square_of_spoke (P : Fin 11 → XY) (p e : Nat)
    (hs : SpokeShape p e) :
    ∃ v ∈ E97A2Prefix.rowWitnessSet p,
      edgeSquare P e = sqDist (P (Fin.ofNat 11 (p/210))) (P (Fin.ofNat 11 v)) := by
  rcases hh : (E97A2Rows.edgeEndpoints[e]?).getD (0,0) with ⟨u,v⟩
  simp only [SpokeShape, hh] at hs
  rcases hs with ⟨hu,hv⟩ | ⟨hv,hu⟩
  · refine ⟨v,hv,?_⟩
    simp only [edgeSquare, hh, hu]
  · refine ⟨u,hu,?_⟩
    simp only [edgeSquare, hh, hv]
    exact sqDist_symm _ _

theorem equal_spoke_squares (P : Fin 11 → XY) (p e f : Nat)
    (hrow : E97AllowSound.SelectedRowRealization P p)
    (he : SpokeShape p e) (hf : SpokeShape p f) :
    edgeSquare P e = edgeSquare P f := by
  obtain ⟨u,hu,heu⟩ := square_of_spoke P p e he
  obtain ⟨v,hv,hfv⟩ := square_of_spoke P p f hf
  rw [heu, hfv]
  exact hrow u v hu hv

/-- Every actual realized row, not only four first-F rows, gives edge equalities. -/
theorem realized_row_squares (P : Fin 11 → XY) (p : Nat) (hp : p < 2310)
    (hrow : E97AllowSound.SelectedRowRealization P p) :
    RowFourEqual (edgeSquare P) p := by
  have hs := row_spokes p hp
  rcases hh : E97Flow.getRow p with ⟨a,b,c,d⟩
  simp only [RowSpokes, hh] at hs
  simp only [RowFourEqual, hh]
  exact ⟨equal_spoke_squares P p a b hrow hs.1 hs.2.1,
    equal_spoke_squares P p a c hrow hs.1 hs.2.2.1,
    equal_spoke_squares P p a d hrow hs.1 hs.2.2.2⟩

theorem realized_row_lengths (P : Fin 11 → XY) (p : Nat) (hp : p < 2310)
    (hrow : E97AllowSound.SelectedRowRealization P p) :
    RowFourEqual (edgeLength P) p := by
  exact row_four_sqrt (edgeSquare P) p (realized_row_squares P p hp hrow)

#print axioms E97AllRow13.all_rows_spokes
#print axioms E97AllRow13.valid_spoke
#print axioms E97AllRow13.row_spokes
#print axioms E97AllRow13.square_of_spoke
#print axioms E97AllRow13.equal_spoke_squares
#print axioms E97AllRow13.realized_row_squares
#print axioms E97AllRow13.realized_row_lengths
end E97AllRow13
