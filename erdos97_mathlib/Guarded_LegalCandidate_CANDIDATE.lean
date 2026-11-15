import Guarded_Reason_Interface_CANDIDATE
/-!
The actual pairwise legalCandidate interface consumes the GUARDED view,
not arbitrary U16 rejections. Thus any physical row survives pairwise
filtering, with no separate full 2,425,500-entry scan assumption.
This does NOT prove A2 budget soundness, full B/E legal-domain equivalence,
or tree replay. The eventual verifier must use this guarded view.
-/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 0
namespace E97Guarded
open E97CertBridge E97LegalPrefix

/-- No CertifiedReasonTable assumption is needed: guard-on-use provides it. -/
theorem realized_candidate_survives_guarded_pairwise
    (rawReasonAt : Nat → Nat)
    (P : Fin 11 → E97BlockB.XY) (hccw : E97A1Index.StrictCCW11 P)
    (chosenRows : List Nat) (nextRow : Nat)
    (hprefix : RealizablePrefix P chosenRows)
    (hnext : E97AllowSound.SelectedRowRealization P nextRow) :
    PairwiseLegalCandidate (guardedReasonAt rawReasonAt) chosenRows nextRow := by
  exact E97LegalPrefix.realized_candidate_survives_pairwise_allow
    (guardedReasonAt rawReasonAt) (guarded_certificate rawReasonAt)
    P hccw chosenRows nextRow hprefix hnext

#print axioms E97Guarded.realized_candidate_survives_guarded_pairwise
end E97Guarded
