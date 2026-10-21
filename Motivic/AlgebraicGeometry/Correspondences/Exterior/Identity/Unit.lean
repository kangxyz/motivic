/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Exterior.Simplex.Basic

/-!
# Exterior extension of actual componentwise identities

The diagonal components are carried to the diagonal components of the actual
product. The component bijection preserves every coefficient one, with no
connectedness or nonemptiness hypothesis on the smooth source.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped BigOperators

universe u

namespace Motivic
open _root_.AlgebraicGeometry.Scheme

/-- The Noetherian instance used in this module. -/
local instance identityUnitNoetherian {k : Type u} [Field k] (U : SmoothSite (Spec (.of k))) :
    IsNoetherian ((𝟭 Scheme).obj U.left) := inferInstanceAs (IsNoetherian U.left)

/-- The reduced scheme instance used in this module. -/
local instance identityUnitReduced {k : Type u} [Field k] (U : SmoothSite (Spec (.of k))) :
    IsReduced ((𝟭 Scheme).obj U.left) := inferInstanceAs (IsReduced U.left)

namespace FiniteCorrespondenceGenerator
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.Hom
open _root_.AlgebraicGeometry.Scheme.IdealSheafData

section Diagonal

variable {S X : Scheme.{u}} {f : X ⟶ S}

/-- Equality of the two projections identifies the actual support map with the diagonal. -/
theorem inclusion_eq_projection_diagonal
    (A : FiniteCorrespondenceGenerator f f) (hA : A.targetProjection = A.projection) :
    A.inclusion = A.projection ≫ pullback.diagonal f := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.diagonal_fst, Category.comp_id]
    rfl
  · simp only [Category.assoc, pullback.diagonal_snd, Category.comp_id]
    exact hA

/-- Two actual integral diagonal supports with the same source image are identical. -/
theorem eq_of_diagonal_range_eq
    (A B : FiniteCorrespondenceGenerator f f)
    (hA : A.targetProjection = A.projection) (hB : B.targetProjection = B.projection)
    (h : Set.range A.projection = Set.range B.projection) : A = B := by
  apply Subtype.ext
  apply idealSheaf_eq_of_support_eq
  apply SetLike.coe_injective
  rw [← Scheme.IdealSheafData.range_subschemeι, ← Scheme.IdealSheafData.range_subschemeι]
  change Set.range A.inclusion = Set.range B.inclusion
  rw [A.inclusion_eq_projection_diagonal hA, B.inclusion_eq_projection_diagonal hB]
  change Set.range (pullback.diagonal f ∘ A.projection) =
    Set.range (pullback.diagonal f ∘ B.projection)
  rw [Set.range_comp, Set.range_comp, h]

end Diagonal

variable {k : Type u} [Field k] {X Y : SmoothSite (Spec (.of k))}
  (V : FiniteCorrespondenceGenerator X.hom Y.hom)
  (T : SmoothSite (Spec (.of k))) [GeometricallyIntegral T.hom]

omit [GeometricallyIntegral T.hom] in
/-- The source image of the actual exterior support is the Cartesian preimage. -/
theorem exteriorIdentitySource_range :
    Set.range (V.exteriorIdentitySource T) =
      (pullback.fst X.hom T.hom) ⁻¹' Set.range V.projection := by
  let h := V.exteriorIdentitySource_isPullback T
  rw [← h.isoPullback_hom_fst]
  change Set.range (fun x =>
    (pullback.fst (pullback.fst X.hom T.hom) V.projection) (h.isoPullback.hom x)) = _
  have hh : Function.Surjective h.isoPullback.hom :=
    (Scheme.homeoOfIso h.isoPullback).surjective
  exact (hh.range_comp _).trans (Scheme.Pullback.range_fst _ _)

/-- The image construction retains the literal source image of the exterior support. -/
theorem exteriorIdentityGenerator_range :
    Set.range (V.exteriorIdentityGenerator T).projection =
      (pullback.fst X.hom T.hom) ⁻¹' Set.range V.projection := by
  rw [← (surjective_toImage (V.exteriorIdentityInclusion T)).range_comp]
  change Set.range ((V.exteriorIdentityInclusion T).toImage ≫
    correspondenceProjection _ _ (V.exteriorIdentityInclusion T).ker) = _
  rw [V.exteriorIdentityInclusion_toImage_source T]
  exact V.exteriorIdentitySource_range T

/-- Exterior extension carries a diagonal support to a diagonal support. -/
theorem exteriorIdentityGenerator_targetProjection
    (V : FiniteCorrespondenceGenerator X.hom X.hom)
    (hV : V.targetProjection = V.projection) :
    (V.exteriorIdentityGenerator T).targetProjection =
      (V.exteriorIdentityGenerator T).projection := by
  apply (cancel_epi (V.exteriorIdentityInclusion T).toImage).mp
  change (V.exteriorIdentityInclusion T).toImage ≫
      (V.exteriorIdentityInclusion T).imageι ≫ pullback.snd _ _ =
    (V.exteriorIdentityInclusion T).toImage ≫
      (V.exteriorIdentityInclusion T).imageι ≫ pullback.fst _ _
  simp only [← Category.assoc, Scheme.Hom.toImage_imageι,
    exteriorIdentityInclusion_snd, exteriorIdentityInclusion_fst]
  apply pullback.hom_ext
  · simp only [exteriorIdentityTarget_fst, exteriorIdentitySource_fst, hV]
  · simp only [exteriorIdentityTarget_snd, exteriorIdentitySource_snd]

end FiniteCorrespondenceGenerator

section Components

variable {k : Type u} [Field k] {X : SmoothSite (Spec (.of k))}
  (T : SmoothSite (Spec (.of k))) [GeometricallyIntegral T.hom]

/-- Each actual exterior diagonal component is the corresponding product diagonal component. -/
theorem componentIdentityGenerator_exteriorIdentityGenerator
    (C : Set X.left) (hC : C ∈ irreducibleComponents X.left)
    (hCT : (pullback.fst X.hom T.hom) ⁻¹' C ∈
      irreducibleComponents (SmoothSite.product X T).left) :
    (componentIdentityGenerator (X := X.left) X.hom C hC).exteriorIdentityGenerator T =
      componentIdentityGenerator (X := (SmoothSite.product X T).left)
        (SmoothSite.product X T).hom
        ((pullback.fst X.hom T.hom) ⁻¹' C) hCT := by
  apply FiniteCorrespondenceGenerator.eq_of_diagonal_range_eq
  · exact FiniteCorrespondenceGenerator.exteriorIdentityGenerator_targetProjection T _
      (componentIdentityGenerator_targetProjection X.hom C hC)
  · exact componentIdentityGenerator_targetProjection _ _ _
  · rw [FiniteCorrespondenceGenerator.exteriorIdentityGenerator_range,
      componentIdentityGenerator_range, componentIdentityGenerator_range]

end Components

namespace FiniteCorrespondence
open _root_.AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] {X : SmoothSite (Spec (.of k))}
  (T : SmoothSite (Spec (.of k))) [GeometricallyIntegral T.hom]

/-- Exterior extension preserves the full identity, including disconnected and empty sources. -/
theorem exteriorIdentity_componentIdentityCycle :
    exteriorIdentity (X := X) (Y := X) T (componentIdentityCycle (X := X.left) X.hom) =
      componentIdentityCycle (X := (SmoothSite.product X T).left)
        (SmoothSite.product X T).hom := by
  classical
  let e : irreducibleComponents X.left ≃
      irreducibleComponents (SmoothSite.product X T).left :=
    ((pullback.fst X.hom T.hom).irreducibleComponentsEquiv
      (pullback.fst X.hom T.hom).isOpenMap).symm
  have he (C : irreducibleComponents X.left) :
      (e C).1 = (pullback.fst X.hom T.hom) ⁻¹' C.1 := rfl
  rw [componentIdentityCycle_eq_sum, componentIdentityCycle_eq_sum, map_sum]
  refine Finset.sum_bij (fun C _ => (pullback.fst X.hom T.hom) ⁻¹' C) ?_ ?_ ?_ ?_
  · intro C hC
    have hC' : C ∈ irreducibleComponents X.left := by simpa using hC
    have hCT : (pullback.fst X.hom T.hom) ⁻¹' C ∈
        irreducibleComponents (SmoothSite.product X T).left := (e ⟨C, hC'⟩).2
    simpa only [Set.Finite.mem_toFinset] using hCT
  · intro C hC D hD hCD
    exact (pullback.fst X.hom T.hom).surjective.preimage_injective hCD
  · intro D hD
    have hD' : D ∈ irreducibleComponents (SmoothSite.product X T).left := by
      simpa using hD
    refine ⟨(e.symm ⟨D, hD'⟩).1, (by simp), ?_⟩
    exact (he (e.symm ⟨D, hD'⟩)).symm.trans
      (congrArg Subtype.val (e.apply_symm_apply ⟨D, hD'⟩))
  · intro C hC
    have hC' : C ∈ irreducibleComponents X.left := by simpa using hC
    have hCT : (pullback.fst X.hom T.hom) ⁻¹' C ∈
        irreducibleComponents (SmoothSite.product X T).left := (e ⟨C, hC'⟩).2
    simp only [dite_eq_left hC', dite_eq_left hCT, exteriorIdentity_cycle,
      componentIdentityGenerator_exteriorIdentityGenerator T C hC' hCT]

@[simp] theorem exteriorIdentity_componentIdentityCycle_simp :
    @DFunLike.coe
      (FiniteCorrespondence X.hom X.hom →+
        FiniteCorrespondence (pullback.fst X.hom T.hom ≫ X.hom)
          (pullback.fst X.hom T.hom ≫ X.hom))
      _ _ _ (exteriorIdentity (X := X) (Y := X) T) (componentIdentityCycle (X := X.left) X.hom) =
      componentIdentityCycle (X := (SmoothSite.product X T).left)
        (SmoothSite.product X T).hom :=
  exteriorIdentity_componentIdentityCycle T

end FiniteCorrespondence

namespace Cor

variable {k : Type u} [Field k]

/-- Exterior extension with the actual algebraic simplex preserves the identity of every object. -/
@[simp] theorem simplexExterior_id (n : ℕ) (X : Cor k) :
    simplexExterior n (𝟙 X) = 𝟙 (simplexProduct X n) :=
  FiniteCorrespondence.exteriorIdentity_componentIdentityCycle
    (X := X.toSmoothSite) (_root_.AlgebraicSimplex.smoothSiteObj k n)

end Cor

end Motivic
