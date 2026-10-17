/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.OpenSupportNeighborhoods

/-! # Actual affine-neighborhood Tor consumers with restricted closed supports -/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Motivic.MotivicTest.OpenSupportNeighborhoods

open Motivic.OpenProductNeighborhoods Intersection

variable {S X Y Z : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S}
  (F : FiniteCorrespondenceGenerator f g) (G : FiniteCorrespondenceGenerator g h)
  (w : F.incidence G)

/-- Actual incidence Tor admits a genuine affine-factor support-product neighborhood,
with every chart, point lift, scalar square and length comparison constructed. -/
theorem actualAffineSupportNeighborhood :
    ∃ A B C : CommRingCat.{u},
    ∃ uX : Spec A ⟶ X, ∃ uY : Spec B ⟶ Y, ∃ uZ : Spec C ⟶ Z,
      IsOpenImmersion uX ∧ IsOpenImmersion uY ∧ IsOpenImmersion uZ ∧
      ∃ q : correspondenceTripleProduct (uX ≫ f) (uY ≫ g) (uZ ≫ h),
      ∃ t : F.openSupportProduct G uX uY uZ,
      ∃ hp : correspondenceTripleInclusion (uX ≫ f) (uY ≫ g) (uZ ≫ h) q =
        F.openSupportProductInclusion G uX uY uZ t,
      ∀ n : ℕ,
        Module.length (F.incidenceAmbientStalk G w) (F.incidenceTor G w n) =
          Module.length
            (ambientStalk (correspondenceTripleInclusion (uX ≫ f) (uY ≫ g) (uZ ≫ h)) q)
            (F.openIncidenceStalkTor G uX uY uZ q t hp n) := by
  obtain ⟨A, B, C, uX, uY, uZ, hx, hy, hz, q, hq⟩ :=
    exists_affineTripleNeighborhood f g h (F.incidenceInclusion G w)
  let := hx
  let := hy
  let := hz
  obtain ⟨t, ht, hp⟩ := F.exists_openSupportProductPoint G uX uY uZ w q hq
  exact ⟨A, B, C, uX, uY, uZ, hx, hy, hz, q, t, hp,
    F.openIncidenceStalkTor_length G uX uY uZ w q t hq ht hp⟩

/-- Genuine finite degree support passes to the constructed local support product. -/
theorem actualAffineFiniteSupport
    (hfin : LengthEuler.FiniteLengthSupport (F.incidenceTor G w)) :
    ∃ A B C : CommRingCat.{u},
    ∃ uX : Spec A ⟶ X, ∃ uY : Spec B ⟶ Y, ∃ uZ : Spec C ⟶ Z,
      IsOpenImmersion uX ∧ IsOpenImmersion uY ∧ IsOpenImmersion uZ ∧
      ∃ q : correspondenceTripleProduct (uX ≫ f) (uY ≫ g) (uZ ≫ h),
      ∃ t : F.openSupportProduct G uX uY uZ,
      ∃ hp : correspondenceTripleInclusion (uX ≫ f) (uY ≫ g) (uZ ≫ h) q =
        F.openSupportProductInclusion G uX uY uZ t,
        LengthEuler.FiniteLengthSupport (F.openIncidenceStalkTor G uX uY uZ q t hp) := by
  obtain ⟨A, B, C, uX, uY, uZ, hx, hy, hz, q, t, hp, hlen⟩ :=
    actualAffineSupportNeighborhood F G w
  refine ⟨A, B, C, uX, uY, uZ, hx, hy, hz, q, t, hp, ⟨?_, ?_⟩⟩
  · intro n
    rw [← hlen n]
    exact hfin.finite_length n
  · have he := funext hlen
    simpa only [he] using hfin.finite_support

end Motivic.MotivicTest.OpenSupportNeighborhoods
