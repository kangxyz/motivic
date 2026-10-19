/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Exterior.Identity.Incidence
public import Motivic.Aglib.Algebra.Homology.Koszul.RegularBlockElimination

/-!
# The actual parameter-diagonal regular block on exterior coefficients

The parameter-pair map on the product of the two exterior supports is flat,
because each parameter projection is the base change of a map to the field.
The literal pullback of the parameter diagonal therefore has a regular
stalk kernel. Its actual closed-stalk surjection eliminates that same block
from Koszul homology, leaving every remaining equation and every degree.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RingTheory.Sequence

universe u

namespace Motivic.FiniteCorrespondenceGenerator
open _root_.AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] {X Y Z : SmoothSite (Spec (.of k))}
  (A : FiniteCorrespondenceGenerator X.hom Y.hom)
  (T : SmoothSite (Spec (.of k))) [GeometricallyIntegral T.hom]

/-- The literal parameter projection from the actual exterior generator support. -/
abbrev exteriorIdentityParameter : (A.exteriorIdentityGenerator T).scheme ⟶ T.left :=
  (A.exteriorIdentitySchemeIso T).inv ≫ pullback.snd (A.projection ≫ X.hom) T.hom

instance exteriorIdentityParameter_flat : Flat (A.exteriorIdentityParameter T) := by
  let : Subsingleton (Spec (.of k)) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  let : IsIntegral (Spec (.of k)) := inferInstance
  have : Flat (A.projection ≫ X.hom) :=
    Flat.instOfSubsingletonCarrierCarrierCommRingCatOfIsIntegral
      (Y := Spec (.of k)) (A.projection ≫ X.hom)
  unfold exteriorIdentityParameter
  infer_instance

@[reassoc]
theorem exteriorIdentityParameter_source_base :
    A.exteriorIdentityParameter T ≫ T.hom =
      (A.exteriorIdentityGenerator T).projection ≫ (SmoothSite.product X T).hom := by
  rw [← A.exteriorIdentitySchemeIso_inv_source T]
  simp only [exteriorIdentityParameter, SmoothSite.product_hom, Category.assoc,
    exteriorIdentitySource_fst_assoc]
  simpa only [Category.assoc] using congrArg ((A.exteriorIdentitySchemeIso T).inv ≫ ·)
    (pullback.condition (f := A.projection ≫ X.hom) (g := T.hom)).symm

@[reassoc]
theorem exteriorIdentityParameter_target_base :
    A.exteriorIdentityParameter T ≫ T.hom =
      (A.exteriorIdentityGenerator T).targetProjection ≫ (SmoothSite.product Y T).hom :=
  (A.exteriorIdentityParameter_source_base T).trans
    (A.exteriorIdentityGenerator T).projection_base

variable (B : FiniteCorrespondenceGenerator Y.hom Z.hom)

/-- The two parameter coordinates of the actual product of exterior supports. -/
def exteriorCoefficientParameterPair :
    (A.exteriorIdentityGenerator T).supportProduct (B.exteriorIdentityGenerator T) ⟶
      pullback T.hom T.hom :=
  pullback.map _ _ T.hom T.hom (A.exteriorIdentityParameter T) (B.exteriorIdentityParameter T)
    (𝟙 (Spec (.of k)))
    (by simpa using (A.exteriorIdentityParameter_target_base T).symm)
    (by simpa using (B.exteriorIdentityParameter_source_base T).symm)

/-- This coefficient flatness uses only maps to the base field, not support-to-middle flatness. -/
instance exteriorCoefficientParameterPair_flat : Flat (A.exteriorCoefficientParameterPair T B) := by
  unfold exteriorCoefficientParameterPair
  exact MorphismProperty.pullbackMap (P := @Flat)
    (inferInstanceAs (Flat (A.exteriorIdentityParameter T)))
    (inferInstanceAs (Flat (B.exteriorIdentityParameter T)))
    (A.exteriorIdentityParameter_target_base T).symm
    (B.exteriorIdentityParameter_source_base T).symm

@[reassoc (attr := simp)]
theorem exteriorCoefficientParameterPair_fst :
    A.exteriorCoefficientParameterPair T B ≫ pullback.fst T.hom T.hom =
      pullback.fst
        ((A.exteriorIdentityGenerator T).targetProjection ≫ (SmoothSite.product Y T).hom)
        ((B.exteriorIdentityGenerator T).projection ≫ (SmoothSite.product Y T).hom) ≫
          A.exteriorIdentityParameter T := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem exteriorCoefficientParameterPair_snd :
    A.exteriorCoefficientParameterPair T B ≫ pullback.snd T.hom T.hom =
      pullback.snd
        ((A.exteriorIdentityGenerator T).targetProjection ≫ (SmoothSite.product Y T).hom)
        ((B.exteriorIdentityGenerator T).projection ≫ (SmoothSite.product Y T).hom) ≫
          B.exteriorIdentityParameter T := pullback.lift_snd _ _ _

/-- Impose exactly the parameter diagonal on the actual coefficient scheme. -/
abbrev exteriorParameterDiagonal :=
  pullback (pullback.diagonal T.hom) (A.exteriorCoefficientParameterPair T B)

/-- Its inclusion retains the full closed-fiber scheme structure. -/
abbrev exteriorParameterDiagonalInclusion : A.exteriorParameterDiagonal T B ⟶
    (A.exteriorIdentityGenerator T).supportProduct (B.exteriorIdentityGenerator T) :=
  pullback.snd (pullback.diagonal T.hom) (A.exteriorCoefficientParameterPair T B)

instance exteriorParameterDiagonalInclusion_isClosedImmersion :
    IsClosedImmersion (A.exteriorParameterDiagonalInclusion T B) := inferInstance

/-- The regular block is pulled through this genuine Cartesian square. -/
theorem exteriorParameterDiagonal_isPullback :
    IsPullback
      (pullback.fst (pullback.diagonal T.hom) (A.exteriorCoefficientParameterPair T B))
      (A.exteriorParameterDiagonalInclusion T B)
      (pullback.diagonal T.hom) (A.exteriorCoefficientParameterPair T B) :=
  IsPullback.of_hasPullback _ _

/-- The actual parameter-diagonal coefficient stalk kernel has a regular generating list. -/
theorem exteriorParameterDiagonal_exists_regular_kernel (z : A.exteriorParameterDiagonal T B) :
    ∃ t : List (((A.exteriorIdentityGenerator T).supportProduct
        (B.exteriorIdentityGenerator T)).presheaf.stalk
          (A.exteriorParameterDiagonalInclusion T B z)),
      IsRegular (((A.exteriorIdentityGenerator T).supportProduct
        (B.exteriorIdentityGenerator T)).presheaf.stalk
          (A.exteriorParameterDiagonalInclusion T B z)) t ∧
        RingHom.ker ((A.exteriorParameterDiagonalInclusion T B).stalkMap z).hom = Ideal.ofList t :=
  Diagonal.exists_regular_kernel_of_flat_isPullback
    (A.exteriorParameterDiagonal_isPullback T B) z
    (Diagonal.exists_regular_kernel_of_smooth T.hom
      (pullback.fst (pullback.diagonal T.hom) (A.exteriorCoefficientParameterPair T B) z))

/-- Eliminate the literal image of a chosen parameter-diagonal list in every degree.
The remaining list is arbitrary and is mapped through the actual stalk surjection. -/
def exteriorParameterDiagonal_regularBlockHomologyIso
    (z : A.exteriorParameterDiagonal T B)
    (t : List ((pullback T.hom T.hom).presheaf.stalk
      (pullback.diagonal T.hom
        (pullback.fst (pullback.diagonal T.hom) (A.exteriorCoefficientParameterPair T B) z))))
    (ht : IsRegular ((pullback T.hom T.hom).presheaf.stalk
      (pullback.diagonal T.hom
        (pullback.fst (pullback.diagonal T.hom) (A.exteriorCoefficientParameterPair T B) z))) t)
    (hker : RingHom.ker ((pullback.diagonal T.hom).stalkMap
      (pullback.fst (pullback.diagonal T.hom) (A.exteriorCoefficientParameterPair T B) z)).hom =
        Ideal.ofList t)
    (s : List (((A.exteriorIdentityGenerator T).supportProduct
      (B.exteriorIdentityGenerator T)).presheaf.stalk
        (A.exteriorParameterDiagonalInclusion T B z))) (n : ℕ) :
    (_root_.ChainComplex.Koszul.coefficientComplex
      (ModuleCat.of
        (((A.exteriorIdentityGenerator T).supportProduct
          (B.exteriorIdentityGenerator T)).presheaf.stalk
          (A.exteriorParameterDiagonalInclusion T B z))
        (((A.exteriorIdentityGenerator T).supportProduct
          (B.exteriorIdentityGenerator T)).presheaf.stalk
          (A.exteriorParameterDiagonalInclusion T B z)))
      (t.map (Diagonal.baseChangeStalkMap
        (A.exteriorParameterDiagonal_isPullback T B) z).hom ++ s)).homology n ≅
      (ModuleCat.restrictScalars ((A.exteriorParameterDiagonalInclusion T B).stalkMap z).hom).obj
        ((_root_.ChainComplex.Koszul.coefficientComplex
          (ModuleCat.of ((A.exteriorParameterDiagonal T B).presheaf.stalk z)
            ((A.exteriorParameterDiagonal T B).presheaf.stalk z))
          (s.map ((A.exteriorParameterDiagonalInclusion T B).stalkMap z).hom)).homology n) := by
  obtain ⟨hregular, hkernel⟩ := Diagonal.mapped_equations_regular_kernel
    (A.exteriorParameterDiagonal_isPullback T B) z ht hker
  exact _root_.ChainComplex.Koszul.regularBlockHomologyIso
    ((A.exteriorParameterDiagonalInclusion T B).stalkMap z).hom
    ((A.exteriorParameterDiagonalInclusion T B).stalkMap_surjective z)
    _ s hkernel hregular.toIsWeaklyRegular n

end Motivic.FiniteCorrespondenceGenerator
