/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Cycles.IntegralExteriorBranchTransport
public import MotivicTest.IntegralExteriorResidueTensor

/-!
# All actual pair-exterior branches, with their stalk and residue maps

For arbitrary fields and actual SmoothSite correspondence generators, transport
every maximal ideal of the constructed original-residue tensor to the entire
actual pairExteriorMap fiber. Since v is generic in the target SUPPORT exterior,
finite-fiber reflection identifies precisely the source SUPPORT exterior generic
points above it. No statement asserts genericity in the whole ambient products.
The source and target exterior support immersions remain explicit.

Prepared initially as a source-only consumer of the Cartesian and
whole-residue-tensor constructions. Exact prerequisite admission and
this packet's own verification are tracked separately from source preparation.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open scoped TensorProduct
open MotivicTest.IntegralGenericFiniteImage
open MotivicTest.IntegralExteriorResidueTensor

universe u

namespace MotivicTest.IntegralExteriorBranchTransport

variable {k : Type u} [Field k] {X Y Z W : SmoothSite (Spec (.of k))}
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (H : FiniteCorrespondenceGenerator Z.hom W.hom)
  (z : genericPoints (F.incidence G))

local instance : IsFinite (F.incidenceMap G).toImage := F.incidenceToImage_isFinite G

variable {U : (imageSupport F G z).val.subscheme.Opens} [Nonempty U] (hU : IsAffineOpen U)
  {V : (imageExterior F G H z).Opens} (hV : IsAffineOpen V)
  (hVU : V ≤ targetProjection F G H z ⁻¹ᵁ U)
  (v : genericPoints (imageExterior F G H z)) (hv : v.1 ∈ V)

local notation "C" => Motivic.FiniteCartesianAffineAlgebra.baseChangedTargetRing
  (Y' := imageExterior F G H z) (V := V)
local notation "D" => Motivic.FiniteCartesianAffineAlgebra.baseChangedSourceRing
  (f' := pairExteriorMap F G H z) (V := V)
local notation "R" => (TopCat.Presheaf.stalk
  (PresheafedSpace.presheaf (SheafedSpace.toPresheafedSpace
    (LocallyRingedSpace.toSheafedSpace
      (Scheme.toLocallyRingedSpace (imageExterior F G H z))))) (Subtype.val v) : CommRingCat)
local notation "L" => Scheme.residueField (Scheme.Hom.image (F.incidenceMap G))
  (Scheme.Hom.toImage (F.incidenceMap G) (Subtype.val z))
local notation "M" => Scheme.residueField (F.incidence G) (Subtype.val z)
local notation "B" => Motivic.FiniteCartesianAffineAlgebra.sourceRing
  (f := pairMap F G z) (U := U)
local notation "p" => hV.primeIdealOf (Subtype.mk (Subtype.val v) hv : V)

/-- Source coordinates use the actual pair-exterior section pullback. -/
local instance exteriorCoordinateAlgebra : Algebra C D :=
  ((pairExteriorMap F G H z).app V).hom.toAlgebra

/-- The target residue action is the already constructed literal projection action. -/
abbrev exteriorTargetResidueAlgebra : Algebra L R :=
  exteriorResidueAlgebra F G H z hU v

/-- The original source residue action is the actual incidence-to-image residue map. -/
local instance originalSourceResidueAlgebra : Algebra L M :=
  ((F.incidenceMap G).toImage.residueFieldMap z.1).hom.toAlgebra

local notation "T" => R ⊗[L] M
local notation "S" => FiniteFiber.localAlgebra C D p

/-- The actual constructed whole residue tensor is the existing whole local
algebra for the actual pair exterior finite map. -/
def actualTensorToLocalEquiv :
    let := exteriorResidueAlgebra F G H z hU v
    T ≃+* S := by
  let := exteriorResidueAlgebra F G H z hU v
  exact Motivic.IntegralExteriorBranchTransport.residueTensorToLocalEquiv
    (F.incidenceMap G).toImage z.1 hU (pairExteriorMap_isPullback F G H z)
    hV hVU ⟨v.1, hv⟩ (targetProjection_generic F G H z v)

/-- No maximal branch of the actual residue tensor is omitted, and every
actual source fiber point occurs exactly once. -/
def actualAllBranchesEquiv :
    let := exteriorResidueAlgebra F G H z hU v
    MaximalSpectrum T ≃ {w : pairExterior F G H z // pairExteriorMap F G H z w = v.1} := by
  let := exteriorResidueAlgebra F G H z hU v
  exact Motivic.IntegralExteriorBranchTransport.tensorFiberEquiv
    (F.incidenceMap G).toImage z.1 hU (pairExteriorMap_isPullback F G H z)
    hV hVU ⟨v.1, hv⟩ (targetProjection_generic F G H z v)

/-- The entire actual fiber consists of generic points of the source SUPPORT
exterior, using finite reflection at this genuine target SUPPORT generic point. -/
def actualAllGenericBranchesEquiv :
    let := exteriorResidueAlgebra F G H z hU v
    MaximalSpectrum T ≃
      {w : genericPoints (pairExterior F G H z) // pairExteriorMap F G H z w.1 = v.1} := by
  let := exteriorResidueAlgebra F G H z hU v
  exact Motivic.IntegralExteriorBranchTransport.tensorGenericFiberEquiv
    (F.incidenceMap G).toImage z.1 hU (pairExteriorMap_isPullback F G H z)
    hV hVU ⟨v.1, hv⟩ (targetProjection_generic F G H z v) v.2

/-- The generic reindexing keeps the same actual exterior source point. -/
@[simp] theorem actualAllGenericBranchesEquiv_val :
    let := exteriorResidueAlgebra F G H z hU v
    ∀ (q : MaximalSpectrum T),
    ((actualAllGenericBranchesEquiv F G H z hU hV hVU v hv q).1 : pairExterior F G H z) =
      (actualAllBranchesEquiv F G H z hU hV hVU v hv q).1 := by
  let := exteriorResidueAlgebra F G H z hU v
  dsimp only
  intro q
  rfl

/-- In particular every source SUPPORT generic point lying above v is represented. -/
theorem actualAllGenericBranchesEquiv_surjective :
    let := exteriorResidueAlgebra F G H z hU v
    Function.Surjective (actualAllGenericBranchesEquiv F G H z hU hV hVU v hv) := by
  let := exteriorResidueAlgebra F G H z hU v
  exact (actualAllGenericBranchesEquiv F G H z hU hV hVU v hv).surjective

/-- Localizing each tensor branch recovers its actual source SUPPORT stalk,
including all nilpotents of that stalk. -/
def actualBranchStalkEquiv :
    let := exteriorResidueAlgebra F G H z hU v
    ∀ (q : MaximalSpectrum T),
    Localization.AtPrime q.asIdeal ≃+*
      (pairExterior F G H z).presheaf.stalk
        (actualAllBranchesEquiv F G H z hU hV hVU v hv q).1 := by
  let := exteriorResidueAlgebra F G H z hU v
  dsimp only
  intro q
  exact Motivic.IntegralExteriorBranchTransport.tensorBranchStalkEquiv
    (F.incidenceMap G).toImage z.1 hU (pairExteriorMap_isPullback F G H z)
    hV hVU ⟨v.1, hv⟩ (targetProjection_generic F G H z v) q

/-- The branch scalar action is the original target-stalk action in the tensor. -/
def actualBranchBaseMap :
    let := exteriorResidueAlgebra F G H z hU v
    ∀ (q : MaximalSpectrum T),
    R →+* Localization.AtPrime q.asIdeal := by
  let := exteriorResidueAlgebra F G H z hU v
  dsimp only
  intro q
  exact (algebraMap T (Localization.AtPrime q.asIdeal)).comp (algebraMap R T)

/-- Every branch-local target scalar map is the actual pairExteriorMap stalk
map with its target point aligned, not an assumed comparison map. -/
theorem actualBranchStalkScalarSquare :
    let := exteriorResidueAlgebra F G H z hU v
    ∀ (q : MaximalSpectrum T),
    (actualBranchStalkEquiv F G H z hU hV hVU v hv q).toRingHom.comp
        (actualBranchBaseMap F G H z hU v q) =
      (Motivic.IntegralExteriorBranchTransport.actualFiberStalkMap
        (pairExteriorMap F G H z) (⟨v.1, hv⟩ : V)
        (actualAllBranchesEquiv F G H z hU hV hVU v hv q)).hom := by
  let := exteriorResidueAlgebra F G H z hU v
  dsimp only
  intro q
  exact Motivic.IntegralExteriorBranchTransport.tensorBranchStalkEquiv_scalarSquare
    (F.incidenceMap G).toImage z.1 hU (pairExteriorMap_isPullback F G H z)
    hV hVU ⟨v.1, hv⟩ (targetProjection_generic F G H z v) q

/-- The residue action is induced by the full branch-local target-stalk map. -/
def actualBranchResidueMap :
    let := exteriorResidueAlgebra F G H z hU v
    ∀ (q : MaximalSpectrum T),
    (imageExterior F G H z).residueField v.1 →+* q.asIdeal.ResidueField := by
  let := exteriorResidueAlgebra F G H z hU v
  dsimp only
  intro q
  exact Motivic.IntegralExteriorBranchTransport.tensorBranchResidueMap
    (F.incidenceMap G).toImage z.1 hU (pairExteriorMap_isPullback F G H z)
    hV hVU ⟨v.1, hv⟩ (targetProjection_generic F G H z v) q

/-- The branch residue field is the actual source-point residue field through
the constructed stalk comparison. -/
def actualBranchResidueEquiv :
    let := exteriorResidueAlgebra F G H z hU v
    ∀ (q : MaximalSpectrum T),
    q.asIdeal.ResidueField ≃+*
      (pairExterior F G H z).residueField
        (actualAllBranchesEquiv F G H z hU hV hVU v hv q).1 := by
  let := exteriorResidueAlgebra F G H z hU v
  dsimp only
  intro q
  exact Motivic.IntegralExteriorBranchTransport.tensorBranchResidueEquiv
    (F.incidenceMap G).toImage z.1 hU (pairExteriorMap_isPullback F G H z)
    hV hVU ⟨v.1, hv⟩ (targetProjection_generic F G H z v) q

/-- The literal actual pair-exterior residueFieldMap is the scalar action
in the residue comparison at every branch. -/
theorem actualBranchResidueScalarSquare :
    let := exteriorResidueAlgebra F G H z hU v
    ∀ (q : MaximalSpectrum T),
    (actualBranchResidueEquiv F G H z hU hV hVU v hv q).toRingHom.comp
        (actualBranchResidueMap F G H z hU hV hVU v hv q) =
      (Motivic.IntegralExteriorBranchTransport.actualFiberResidueMap
        (pairExteriorMap F G H z) (⟨v.1, hv⟩ : V)
        (actualAllBranchesEquiv F G H z hU hV hVU v hv q)).hom := by
  let := exteriorResidueAlgebra F G H z hU v
  dsimp only
  intro q
  have h := Motivic.IntegralExteriorBranchTransport.tensorBranchResidueEquiv_scalarSquare
    (X := F.incidence G) (Y := (F.incidenceMap G).image) (U := U)
    (X' := pairExterior F G H z) (Y' := imageExterior F G H z)
    (i := pullback.fst ((pairSupport F G z).val.subschemeι ≫ pairStructure F G)
      (H.projection ≫ Z.hom))
    (f' := pairExteriorMap F G H z) (g := targetProjection F G H z) (V := V)
    (F.incidenceMap G).toImage z.1 hU (pairExteriorMap_isPullback F G H z)
    hV hVU (⟨v.1, hv⟩ : V) (targetProjection_generic F G H z v) q
  dsimp only [actualBranchResidueEquiv, actualBranchResidueMap,
    actualAllBranchesEquiv, id]
  exact h

/-- The ORIGINAL ambient target residue field still acts through the literal
projection action of the original whole-residue-tensor construction. -/
theorem actualOriginalResidueScalarSquare :
    let := exteriorResidueAlgebra F G H z hU v
    ∀ (q : MaximalSpectrum T),
    (actualBranchStalkEquiv F G H z hU hV hVU v hv q).toRingHom.comp
        ((actualBranchBaseMap F G H z hU v q).comp
          (Motivic.IntegralExteriorResidueTensor.originalResidueToStalk
            (F.incidenceMap G).toImage z.1 hU (targetProjection F G H z) v.1
            (targetProjection_generic F G H z v))) =
      (Motivic.IntegralExteriorBranchTransport.actualFiberStalkMap
        (pairExteriorMap F G H z) (⟨v.1, hv⟩ : V)
        (actualAllBranchesEquiv F G H z hU hV hVU v hv q)).hom.comp
          (Motivic.IntegralExteriorResidueTensor.originalResidueToStalk
            (F.incidenceMap G).toImage z.1 hU (targetProjection F G H z) v.1
            (targetProjection_generic F G H z v)) := by
  let := exteriorResidueAlgebra F G H z hU v
  dsimp only
  intro q
  exact Motivic.IntegralExteriorBranchTransport.tensorBranchStalkEquiv_originalResidueSquare
    (F.incidenceMap G).toImage z.1 hU (pairExteriorMap_isPullback F G H z)
    hV hVU ⟨v.1, hv⟩ (targetProjection_generic F G H z v) q

/-- The original source numerator retains the actual horizontal source section
map before branch localization; no right-hand field action is substituted. -/
theorem actualSourceNumeratorSquare (b : B) :
    let := exteriorResidueAlgebra F G H z hU v
    actualTensorToLocalEquiv F G H z hU hV hVU v hv
        (1 ⊗ₜ[L] Motivic.IntegralExteriorResidueTensor.originalSourceNumerator
          (F.incidenceMap G).toImage z.1 hU b) =
      (1 : Localization.AtPrime
        (PrimeSpectrum.asIdeal (hV.primeIdealOf (⟨Subtype.val v, hv⟩ : V)))) ⊗ₜ[C]
        Motivic.FiniteCartesianAffineAlgebra.sourceSectionMap
          (pairExteriorMap_isPullback F G H z) hVU b := by
  let := exteriorResidueAlgebra F G H z hU v
  have h := Motivic.IntegralExteriorBranchTransport.residueTensorToLocalEquiv_sourceNumerator
    (X := F.incidence G) (Y := (F.incidenceMap G).image) (U := U)
    (X' := pairExterior F G H z) (Y' := imageExterior F G H z)
    (i := pullback.fst ((pairSupport F G z).val.subschemeι ≫ pairStructure F G)
      (H.projection ≫ Z.hom))
    (f' := pairExteriorMap F G H z) (g := targetProjection F G H z) (V := V)
    (F.incidenceMap G).toImage z.1 hU (pairExteriorMap_isPullback F G H z)
    hV hVU (⟨v.1, hv⟩ : V) (targetProjection_generic F G H z v) b
  dsimp (config := { instances := true }) only
    [actualTensorToLocalEquiv, exteriorResidueAlgebra, exteriorCoordinateAlgebra,
      Motivic.IntegralExteriorBranchTransport.exteriorCoordinates,
      originalSourceResidueAlgebra, Motivic.IntegralExteriorBranchTransport.originalResidue,
      Motivic.IntegralExteriorResidueTensor.originalResidueAlgebra] at h ⊢
  set_option backward.isDefEq.respectTransparency true in
    set_option backward.isDefEq.respectTransparency.types true in
      with_reducible exact h

/-- At every actual branch, the original source residue numerator becomes
exactly the actual germ of its horizontal source-coordinate pullback. -/
theorem actualBranchSourceNumerator :
    let := exteriorResidueAlgebra F G H z hU v
    ∀ (q : MaximalSpectrum T) (b : B),
    actualBranchStalkEquiv F G H z hU hV hVU v hv q
        (algebraMap T (Localization.AtPrime q.asIdeal)
          (1 ⊗ₜ[L] Motivic.IntegralExteriorResidueTensor.originalSourceNumerator
            (F.incidenceMap G).toImage z.1 hU b)) =
      (pairExterior F G H z).presheaf.germ (pairExteriorMap F G H z ⁻¹ᵁ V)
        (actualAllBranchesEquiv F G H z hU hV hVU v hv q).1
        (by
          change pairExteriorMap F G H z
            (actualAllBranchesEquiv F G H z hU hV hVU v hv q).1 ∈ V
          rw [(actualAllBranchesEquiv F G H z hU hV hVU v hv q).2]
          exact hv)
        (Motivic.FiniteCartesianAffineAlgebra.sourceSectionMap
          (pairExteriorMap_isPullback F G H z) hVU b) := by
  let := exteriorResidueAlgebra F G H z hU v
  dsimp only
  intro q b
  have h := Motivic.IntegralExteriorBranchTransport.tensorBranchStalkEquiv_sourceNumerator
    (X := F.incidence G) (Y := (F.incidenceMap G).image) (U := U)
    (X' := pairExterior F G H z) (Y' := imageExterior F G H z)
    (i := pullback.fst ((pairSupport F G z).val.subschemeι ≫ pairStructure F G)
      (H.projection ≫ Z.hom))
    (f' := pairExteriorMap F G H z) (g := targetProjection F G H z) (V := V)
    (F.incidenceMap G).toImage z.1 hU (pairExteriorMap_isPullback F G H z)
    hV hVU (⟨v.1, hv⟩ : V) (targetProjection_generic F G H z v) q b
  dsimp (config := { instances := true }) only
    [actualBranchStalkEquiv, actualAllBranchesEquiv, id, exteriorResidueAlgebra,
      originalSourceResidueAlgebra, Motivic.IntegralExteriorBranchTransport.originalResidue,
      Motivic.IntegralExteriorResidueTensor.originalResidueAlgebra] at h ⊢
  set_option backward.isDefEq.respectTransparency true in
    set_option backward.isDefEq.respectTransparency.types true in
      with_reducible exact h

/-- The branch work retains both actual support immersions into their entire
ambient products; neither support is identified with its ambient product. -/
@[reassoc] theorem actualExteriorAmbientSquare :
    pairExteriorMap F G H z ≫ imageExteriorInclusion F G H z =
      pairExteriorInclusion F G H z ≫ F.leftIntermediateImageMap G H :=
  pairExteriorMap_ambient F G H z

end MotivicTest.IntegralExteriorBranchTransport
