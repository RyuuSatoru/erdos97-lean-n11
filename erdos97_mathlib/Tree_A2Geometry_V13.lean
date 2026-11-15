import A1_PointDistinct_CANDIDATE

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace E97A2Geometry13
open E97BlockB E97A1 E97A1Index

/-- Three centers equidistant from two different witnesses are collinear. -/
theorem three_bisector_centers_collinear (a b c u v : XY) (huv : u ≠ v)
    (ha : sqDist a u = sqDist a v)
    (hb : sqDist b u = sqDist b v)
    (hc : sqDist c u = sqDist c v) : orient a b c = 0 := by
  have hba : (b.1-a.1)*(u.1-v.1) + (b.2-a.2)*(u.2-v.2) = 0 := by
    dsimp [sqDist] at ha hb
    nlinarith [ha,hb]
  have hca : (c.1-a.1)*(u.1-v.1) + (c.2-a.2)*(u.2-v.2) = 0 := by
    dsimp [sqDist] at ha hc
    nlinarith [ha,hc]
  have hnorm : (u.1-v.1)*(u.1-v.1) + (u.2-v.2)*(u.2-v.2) ≠ 0 := by
    simpa only [pow_two] using squared_displacement_ne_zero u v huv
  exact planar_orthogonal_parallel _ _ _ _ _ _ hba hca hnorm

theorem ccw_no_three_collinear (P : Fin 11 → XY) (hccw : StrictCCW11 P)
    (a b c : Nat) (ha : a < 11) (hb : b < 11) (hc : c < 11)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    orient (P (Fin.ofNat 11 a)) (P (Fin.ofNat 11 b))
      (P (Fin.ofNat 11 c)) ≠ 0 := by
  intro hz
  have hord : (a < b ∧ b < c) ∨ (a < c ∧ c < b) ∨
      (b < a ∧ a < c) ∨ (b < c ∧ c < a) ∨
      (c < a ∧ a < b) ∨ (c < b ∧ b < a) := by omega
  rcases hord with ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩ |
      ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩
  · have h := hccw a b c h1 h2 hc
    linarith
  · have h := hccw a c b h1 h2 hb
    have heq : orient (P (Fin.ofNat 11 a)) (P (Fin.ofNat 11 c)) (P (Fin.ofNat 11 b)) = 0 := by
      dsimp [orient] at hz ⊢
      nlinarith [hz]
    linarith
  · have h := hccw b a c h1 h2 hc
    have heq : orient (P (Fin.ofNat 11 b)) (P (Fin.ofNat 11 a)) (P (Fin.ofNat 11 c)) = 0 := by
      dsimp [orient] at hz ⊢
      nlinarith [hz]
    linarith
  · have h := hccw b c a h1 h2 ha
    have heq : orient (P (Fin.ofNat 11 b)) (P (Fin.ofNat 11 c)) (P (Fin.ofNat 11 a)) = 0 := by
      dsimp [orient] at hz ⊢
      nlinarith [hz]
    linarith
  · have h := hccw c a b h1 h2 hb
    have heq : orient (P (Fin.ofNat 11 c)) (P (Fin.ofNat 11 a)) (P (Fin.ofNat 11 b)) = 0 := by
      dsimp [orient] at hz ⊢
      nlinarith [hz]
    linarith
  · have h := hccw c b a h1 h2 ha
    have heq : orient (P (Fin.ofNat 11 c)) (P (Fin.ofNat 11 b)) (P (Fin.ofNat 11 a)) = 0 := by
      dsimp [orient] at hz ⊢
      nlinarith [hz]
    linarith

/-- The actual geometric pair budget, with no pre-assumed A2 bound. -/
theorem geometric_pair_budget (P : Fin 11 → XY) (hccw : StrictCCW11 P)
    (u v : Nat) (hu : u < 11) (hv : v < 11) (huv : u ≠ v)
    (centers : Finset Nat) (hbound : ∀ c ∈ centers, c < 11)
    (heq : ∀ c ∈ centers, sqDist (P (Fin.ofNat 11 c)) (P (Fin.ofNat 11 u)) =
      sqDist (P (Fin.ofNat 11 c)) (P (Fin.ofNat 11 v))) : centers.card ≤ 2 := by
  by_contra hnot
  have hlarge : 3 ≤ centers.card := by omega
  obtain ⟨a,ha⟩ := Finset.card_pos.mp (by omega : 0 < centers.card)
  have hbcard : 0 < (centers.erase a).card := by
    rw [Finset.card_erase_of_mem ha]
    omega
  obtain ⟨b,hb⟩ := Finset.card_pos.mp hbcard
  obtain ⟨hba,hb⟩ := Finset.mem_erase.mp hb
  have hccard : 0 < ((centers.erase a).erase b).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hba,hb⟩), Finset.card_erase_of_mem ha]
    omega
  obtain ⟨c,hc⟩ := Finset.card_pos.mp hccard
  obtain ⟨hcb,hc'⟩ := Finset.mem_erase.mp hc
  obtain ⟨hca,hc⟩ := Finset.mem_erase.mp hc'
  have hpoints := ccw11_points_injective P hccw u v hu hv huv
  have hz := three_bisector_centers_collinear
    (P (Fin.ofNat 11 a)) (P (Fin.ofNat 11 b)) (P (Fin.ofNat 11 c))
    (P (Fin.ofNat 11 u)) (P (Fin.ofNat 11 v)) hpoints
    (heq a ha) (heq b hb) (heq c hc)
  exact ccw_no_three_collinear P hccw a b c
    (hbound a ha) (hbound b hb) (hbound c hc) hba.symm hca.symm hcb.symm hz

#print axioms E97A2Geometry13.three_bisector_centers_collinear
#print axioms E97A2Geometry13.ccw_no_three_collinear
#print axioms E97A2Geometry13.geometric_pair_budget
end E97A2Geometry13
