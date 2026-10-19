/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Diagonal.OpenProductNeighborhoods
public import Motivic.AlgebraicGeometry.Correspondences.Composition.Support.Embedding

/-! # Actual point and scalar-module consumers of product neighborhoods -/

@[expose] public section

noncomputable section

open _root_.Motivic (FiniteCorrespondenceGenerator)
open CategoryTheory AlgebraicGeometry

universe u

namespace Motivic.MotivicTest.OpenProductNeighborhoods
open _root_.AlgebraicGeometry.Scheme.Products

open _root_.AlgebraicGeometry.Scheme.Products.OpenNeighborhoods
open _root_.AlgebraicGeometry.Scheme.Intersection

variable {S X Y Z X' Y' Z' : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)
  (uX : X' ⟶ X) (uY : Y' ⟶ Y) (uZ : Z' ⟶ Z)
  [IsOpenImmersion uX] [IsOpenImmersion uY] [IsOpenImmersion uZ]

/-- The actual source stalk module is transported with the literal ambient scalar square. -/
def actualSourceModuleIso
    (q : correspondenceTripleProduct (uX ≫ f) (uY ≫ g) (uZ ≫ h)) :
    sourceStalkModule (correspondenceTripleInclusion f g h) (tripleMap f g h uX uY uZ q) ≅
      (ModuleCat.restrictScalars
        (neighborhoodAmbientStalkEquiv (correspondenceTripleInclusion f g h)
          (tripleMap f g h uX uY uZ q)
          (correspondenceTripleInclusion (uX ≫ f) (uY ≫ g) (uZ ≫ h)) q
          (tripleMap f g h uX uY uZ) (ambientMap f g h uX uY uZ)
          (tripleMap_inclusion f g h uX uY uZ) rfl).toRingHom).obj
      (sourceStalkModule (correspondenceTripleInclusion (uX ≫ f) (uY ≫ g) (uZ ≫ h)) q) :=
  neighborhoodSourceStalkModuleIso (correspondenceTripleInclusion f g h)
    (tripleMap f g h uX uY uZ q)
    (correspondenceTripleInclusion (uX ≫ f) (uY ≫ g) (uZ ≫ h)) q
    (tripleMap f g h uX uY uZ) (ambientMap f g h uX uY uZ)
    (tripleMap_inclusion f g h uX uY uZ) rfl

/-- The original incidence point obtains compatible affine factor charts on both
sides of the actual middle-diagonal square. -/
theorem actualIncidenceAffineNeighborhood
    (F : FiniteCorrespondenceGenerator f g) (G : FiniteCorrespondenceGenerator g h)
    (w : F.incidence G) :
    ∃ A B C : CommRingCat.{u},
    ∃ uX : Spec A ⟶ X, ∃ uY : Spec B ⟶ Y, ∃ uZ : Spec C ⟶ Z,
      IsOpenImmersion uX ∧ IsOpenImmersion uY ∧ IsOpenImmersion uZ ∧
      ∃ q : correspondenceTripleProduct (uX ≫ f) (uY ≫ g) (uZ ≫ h),
        tripleMap f g h uX uY uZ q = F.incidenceInclusion G w ∧
        ambientMap f g h uX uY uZ
          (correspondenceTripleInclusion (uX ≫ f) (uY ≫ g) (uZ ≫ h) q) =
        correspondenceTripleInclusion f g h (F.incidenceInclusion G w) := by
  obtain ⟨A, B, C, uX, uY, uZ, hx, hy, hz, q, hq⟩ :=
    exists_affineTripleNeighborhood f g h (F.incidenceInclusion G w)
  refine ⟨A, B, C, uX, uY, uZ, hx, hy, hz, q, hq, ?_⟩
  exact (congrArg (fun m ↦ m q) (tripleMap_inclusion f g h uX uY uZ)).symm.trans
    (congrArg (correspondenceTripleInclusion f g h) hq)

end Motivic.MotivicTest.OpenProductNeighborhoods
