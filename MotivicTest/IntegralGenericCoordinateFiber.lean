/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Cycles.Pushforward.Finite.CoordinateFiber
public import MotivicTest.IntegralGenericFiniteImage

/-!
# Original pair generic-coordinate and residue attachment

These consumers attach the complete original pair generic finite algebra to
κ(z), with the original pair-to-image residue map, and identify the genuine
exterior target generic point's projected coordinate prime as zero. The exterior
stalk remains possibly nonreduced. No exterior tensor isomorphism is claimed.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open _root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme
open _root_.AlgebraicGeometry.Scheme.Cycles.Pushforward.GenericCoordinateFiber
open _root_.AlgebraicGeometry.Scheme.GenericFiber.FiniteDomain

universe u

namespace MotivicTest.IntegralGenericCoordinateFiber

open MotivicTest.IntegralGenericFiniteImage

variable {k : Type u} [Field k] {X Y Z W : SmoothSite (Spec (.of k))}
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (H : FiniteCorrespondenceGenerator Z.hom W.hom)
  (z : genericPoints (F.incidence G))
  {U : (imageSupport F G z).val.subscheme.Opens} [Nonempty U] (hU : IsAffineOpen U)

local instance : IsFinite (F.incidenceMap G).toImage := F.incidenceToImage_isFinite G

/-- The whole original finite generic algebra uses the actual pair-to-image
support map and its entire affine inverse image. -/
abbrev pairWholeGenericAlgebra :=
  wholeGenericAlgebra (F.incidenceMap G).toImage z.1 (U := U)

include hU in
/-- No source branch is selected: the entire original generic finite algebra is a field. -/
theorem pairWholeGenericAlgebra_isField : IsField (pairWholeGenericAlgebra F G z (U := U)) :=
  wholeGenericAlgebra_isField (F.incidenceMap G).toImage z.1 hU

/-- The actual whole original generic algebra is identified with the original
pair point's residue field, through its support immersion and affine chart. -/
def pairWholeOriginalResidueIso : CommRingCat.of (pairWholeGenericAlgebra F G z (U := U)) ≅
    (F.incidence G).residueField z.1 :=
  wholeOriginalResidueIso (F.incidenceMap G).toImage z.1 hU

/-- The original pair-to-image residue homomorphism appears literally in the
whole generic algebra's scalar square. -/
theorem pairWholeOriginalResidueIso_base_square :
    let := ((pairMap F G z).app U).hom.toAlgebra
    CommRingCat.ofHom (algebraMap
      (Localization.AtPrime (zeroPrime Γ((imageSupport F G z).val.subscheme, U)).asIdeal)
      (pairWholeGenericAlgebra F G z (U := U))) ≫ (pairWholeOriginalResidueIso F G z hU).hom =
      (Spec.stalkIso Γ((imageSupport F G z).val.subscheme, U)
        (zeroPrime Γ((imageSupport F G z).val.subscheme, U))).inv ≫
      (Spec Γ((imageSupport F G z).val.subscheme, U)).residue
        (zeroPrime Γ((imageSupport F G z).val.subscheme, U)) ≫
      (targetResidueIso (F.incidenceMap G).toImage z.1 hU).inv ≫
      (F.incidenceMap G).toImage.residueFieldMap z.1 :=
  wholeOriginalResidueIso_base_square (F.incidenceMap G).toImage z.1 hU

/-- The complete original pair generic algebra is linear for the original
pair-to-image residue field extension. -/
def pairWholeOriginalResidueAlgEquiv :
    letI := (originalBaseToWhole (F.incidenceMap G).toImage z.1 hU).hom.toAlgebra
    letI := ((F.incidenceMap G).toImage.residueFieldMap z.1).hom.toAlgebra
    pairWholeGenericAlgebra F G z (U := U) ≃ₐ[
      (F.incidenceMap G).image.residueField ((F.incidenceMap G).toImage z.1)]
        (F.incidence G).residueField z.1 :=
  wholeOriginalResidueAlgEquiv (F.incidenceMap G).toImage z.1 hU

/-- A genuine exterior target generic point projects to this actual original
integral target generic point. Exterior reducedness is not assumed. -/
theorem exteriorTargetGeneric_projection
    (v : genericPoints (imageExterior F G H z)) :
    pullback.fst ((imageSupport F G z).val.subschemeι ≫ imageStructure F G)
        (H.projection ≫ Z.hom) v.1 = genericPoint (imageSupport F G z).val.subscheme :=
  (imageSupport F G z).exteriorGeneric_projection (S := Spec (.of k)) (imageStructure F G)
    (H.projection ≫ Z.hom) v

/-- The actual projected exterior generic point has zero prime in the chosen
original integral chart; this supplies the geometric input for later localization. -/
theorem exteriorTargetGeneric_coordinate_zero
    (v : genericPoints (imageExterior F G H z)) :
    hU.primeIdealOf ⟨pullback.fst
      ((imageSupport F G z).val.subschemeι ≫ imageStructure F G)
      (H.projection ≫ Z.hom) v.1,
      by
        rw [exteriorTargetGeneric_projection F G H z v]
        exact generic_mem (F.incidenceMap G).toImage z.1⟩ =
      zeroPrime Γ((imageSupport F G z).val.subscheme, U) := by
  simpa only [exteriorTargetGeneric_projection] using
    targetCoordinate_eq_zero (F.incidenceMap G).toImage z.1 hU

end MotivicTest.IntegralGenericCoordinateFiber
