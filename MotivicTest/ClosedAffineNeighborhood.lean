/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Intersection.ClosedAffineNeighborhood
public import Motivic.AlgebraicGeometry.Correspondences.IncidenceTor

/-! # Actual non-affine incidence consumers of constructed quotient neighborhoods -/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Motivic.MotivicTest.ClosedAffineNeighborhood

open Intersection

variable {S X Y Z : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S}
  (F : FiniteCorrespondenceGenerator f g) (G : FiniteCorrespondenceGenerator g h)
  [IsSeparated g] (w : F.incidence G)

/-- Original incidence Tor has constructed quotient coordinates without global affineness. -/
theorem actualIncidenceQuotientLengths :
    ∃ R : CommRingCat.{u}, ∃ I J : Ideal R,
    ∃ q : PrimeSpectrum (R ⧸ I), ∃ r : PrimeSpectrum (R ⧸ J),
      q.comap (Ideal.Quotient.mk I) = r.comap (Ideal.Quotient.mk J) ∧
      ∀ n : ℕ,
        Module.length (F.incidenceAmbientStalk G w) (F.incidenceTor G w n) =
        Module.length (Localization.AtPrime (q.comap (Ideal.Quotient.mk I)).asIdeal)
          (quotientLocalizedTor R I J q n) :=
  exists_stalkTorLength_quotientCoordinates
    (correspondenceTripleInclusion f g h) (F.supportProductInclusion G)
    (F.incidenceInclusion G w) (F.incidenceToSupportProduct G w)
    (point_eq _ _ _ _ (F.incidence_ambient_isPullback G) w)

/-- Only genuine original finite-length evidence yields finite quotient-coordinate Tor. -/
theorem actualIncidenceFiniteCoordinates
    (hfin : LengthEuler.FiniteLengthSupport (F.incidenceTor G w)) :
    ∃ R : CommRingCat.{u}, ∃ I J : Ideal R,
    ∃ q : PrimeSpectrum (R ⧸ I),
      LengthEuler.FiniteLengthSupport (quotientLocalizedTor R I J q) := by
  obtain ⟨R, I, J, q, r, hqr, hlen⟩ := actualIncidenceQuotientLengths F G w
  refine ⟨R, I, J, q, ⟨?_, ?_⟩⟩
  · intro n
    rw [← hlen n]
    exact hfin.finite_length n
  · have he := funext hlen
    simpa only [he] using hfin.finite_support

end Motivic.MotivicTest.ClosedAffineNeighborhood
