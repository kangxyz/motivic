/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Exterior.Identity.Unit
public import Motivic.AlgebraicGeometry.Correspondences.Graph.Functor

/-!
# Actual exterior extension of graph cycles

Exterior extension by a geometrically integral smooth parameter carries each
actual component graph to the graph of the product map on its corresponding
source component. Reindexing the genuine components proves the equality of
signed cycles for arbitrary smooth sources, including disconnected and empty
ones. The existing fundamental-cycle pushforward identifies the same supports
and preserves their exact coefficient one. No flatness of the original map is
required.
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

local instance {k : Type u} [Field k] (U : SmoothSite (Spec (.of k))) :
    IsNoetherian ((𝟭 Scheme).obj U.left) := inferInstanceAs (IsNoetherian U.left)

local instance {k : Type u} [Field k] (U : SmoothSite (Spec (.of k))) :
    IsReduced ((𝟭 Scheme).obj U.left) := inferInstanceAs (IsReduced U.left)

namespace FiniteCorrespondenceGenerator
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.IdealSheafData

section Graph

variable {S X Y : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}

/-- The graph projection relation identifies the literal closed support inclusion. -/
theorem inclusion_eq_projection_graph (φ : X ⟶ Y) (w : φ ≫ g = f)
    (A : FiniteCorrespondenceGenerator f g)
    (hA : A.projection ≫ φ = A.targetProjection) :
    A.inclusion = A.projection ≫ pullback.lift (𝟙 X) φ (by simpa using w.symm) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst, Category.comp_id]
    rfl
  · simp only [Category.assoc, pullback.lift_snd]
    exact hA.symm

/-- Integral supports in one graph are determined by their actual source images. -/
theorem eq_of_graph_range_eq (φ : X ⟶ Y) (w : φ ≫ g = f)
    (A B : FiniteCorrespondenceGenerator f g)
    (hA : A.projection ≫ φ = A.targetProjection)
    (hB : B.projection ≫ φ = B.targetProjection)
    (h : Set.range A.projection = Set.range B.projection) : A = B := by
  apply Subtype.ext
  apply idealSheaf_eq_of_support_eq
  apply SetLike.coe_injective
  rw [← Scheme.IdealSheafData.range_subschemeι, ← Scheme.IdealSheafData.range_subschemeι]
  change Set.range A.inclusion = Set.range B.inclusion
  rw [A.inclusion_eq_projection_graph φ w hA, B.inclusion_eq_projection_graph φ w hB]
  change Set.range ((pullback.lift (𝟙 X) φ (by simpa using w.symm)) ∘ A.projection) =
    Set.range ((pullback.lift (𝟙 X) φ (by simpa using w.symm)) ∘ B.projection)
  rw [Set.range_comp, Set.range_comp, h]

end Graph

variable {k : Type u} [Field k] {X Y : SmoothSite (Spec (.of k))}
  (T : SmoothSite (Spec (.of k))) [GeometricallyIntegral T.hom]

/-- The exterior support satisfies the graph relation for the actual product map. -/
theorem exteriorIdentityGenerator_projection_graph (φ : X ⟶ Y)
    (V : FiniteCorrespondenceGenerator X.hom Y.hom)
    (hV : V.projection ≫ φ.left = V.targetProjection) :
    (V.exteriorIdentityGenerator T).projection ≫
        (SmoothSite.productMap φ (𝟙 T)).left =
      (V.exteriorIdentityGenerator T).targetProjection := by
  have hfst : (SmoothSite.productMap φ (𝟙 T)).left ≫ pullback.fst Y.hom T.hom =
      pullback.fst X.hom T.hom ≫ φ.left :=
    congrArg (fun a => a.left) (SmoothSite.productMap_fst φ (𝟙 T))
  have hsnd : (SmoothSite.productMap φ (𝟙 T)).left ≫ pullback.snd Y.hom T.hom =
      pullback.snd X.hom T.hom := by
    have h := congrArg (fun a => a.left) (SmoothSite.productMap_snd φ (𝟙 T))
    change (SmoothSite.productMap φ (𝟙 T)).left ≫ pullback.snd Y.hom T.hom =
      pullback.snd X.hom T.hom ≫ 𝟙 T.left at h
    exact h.trans (Category.comp_id _)
  apply (cancel_epi (V.exteriorIdentityInclusion T).toImage).mp
  change (V.exteriorIdentityInclusion T).toImage ≫
      (V.exteriorIdentityInclusion T).imageι ≫ pullback.fst _ _ ≫
        (SmoothSite.productMap φ (𝟙 T)).left =
    (V.exteriorIdentityInclusion T).toImage ≫
      (V.exteriorIdentityInclusion T).imageι ≫ pullback.snd _ _
  simp only [← Category.assoc, Scheme.Hom.toImage_imageι,
    exteriorIdentityInclusion_snd, exteriorIdentityInclusion_fst]
  apply pullback.hom_ext
  · simp only [Category.assoc, hfst, exteriorIdentitySource_fst_assoc,
      hV, exteriorIdentityTarget_fst]
  · simp only [Category.assoc, hsnd, exteriorIdentitySource_snd, exteriorIdentityTarget_snd]

end FiniteCorrespondenceGenerator

section Components

variable {k : Type u} [Field k] {X Y : SmoothSite (Spec (.of k))}
  (T : SmoothSite (Spec (.of k))) [GeometricallyIntegral T.hom]

/-- Each genuine exterior graph component is the corresponding product graph component. -/
theorem componentGraphGeneratorOver_exteriorIdentityGenerator (φ : X ⟶ Y)
    (C : Set X.left) (hC : C ∈ irreducibleComponents X.left)
    (hCT : (pullback.fst X.hom T.hom) ⁻¹' C ∈
      irreducibleComponents (SmoothSite.product X T).left) :
    (componentGraphGeneratorOver (X := X.left) (Y := Y.left)
      φ.left (MorphismProperty.Over.w φ) C hC).exteriorIdentityGenerator T =
      componentGraphGeneratorOver (X := (SmoothSite.product X T).left)
          (Y := (SmoothSite.product Y T).left) (SmoothSite.productMap φ (𝟙 T)).left
        (MorphismProperty.Over.w (SmoothSite.productMap φ (𝟙 T)))
        ((pullback.fst X.hom T.hom) ⁻¹' C) hCT := by
  apply FiniteCorrespondenceGenerator.eq_of_graph_range_eq
      (SmoothSite.productMap φ (𝟙 T)).left
      (MorphismProperty.Over.w (SmoothSite.productMap φ (𝟙 T)))
  · exact FiniteCorrespondenceGenerator.exteriorIdentityGenerator_projection_graph T φ _
      (componentGraphGeneratorOver_projection_target _ _ _ _)
  · exact componentGraphGeneratorOver_projection_target _ _ _ _
  · calc
      _ = (pullback.fst X.hom T.hom) ⁻¹' Set.range
          (componentGraphGeneratorOver (X := X.left) (Y := Y.left)
            φ.left (MorphismProperty.Over.w φ) C hC).projection :=
        FiniteCorrespondenceGenerator.exteriorIdentityGenerator_range _ T
      _ = (pullback.fst X.hom T.hom) ⁻¹' C :=
        congrArg (fun A => (pullback.fst X.hom T.hom) ⁻¹' A)
          (componentGraphGeneratorOver_range φ.left (MorphismProperty.Over.w φ) C hC)
      _ = _ := (componentGraphGeneratorOver_range
        (SmoothSite.productMap φ (𝟙 T)).left
        (MorphismProperty.Over.w (SmoothSite.productMap φ (𝟙 T))) _ hCT).symm

/-- The product graph component has the actual pushed exterior fundamental cycle. -/
theorem componentGraphGeneratorOver_product_fundamental (φ : X ⟶ Y)
    (C : Set X.left) (hC : C ∈ irreducibleComponents X.left)
    (hCT : (pullback.fst X.hom T.hom) ⁻¹' C ∈
      irreducibleComponents (SmoothSite.product X T).left) :
    FiniteCorrespondence.toIntegralCycle
        (componentGraphGeneratorOver (X := (SmoothSite.product X T).left)
          (Y := (SmoothSite.product Y T).left) (SmoothSite.productMap φ (𝟙 T)).left
          (MorphismProperty.Over.w (SmoothSite.productMap φ (𝟙 T)))
          ((pullback.fst X.hom T.hom) ⁻¹' C) hCT).cycle =
      IntegralCycle.finitePushforward
        ((componentGraphGeneratorOver (X := X.left) (Y := Y.left)
          φ.left (MorphismProperty.Over.w φ) C hC).exteriorIdentityInclusion T)
        (fundamentalCycle
          ((componentGraphGeneratorOver (X := X.left) (Y := Y.left)
            φ.left (MorphismProperty.Over.w φ) C hC).exteriorIdentitySupport T)) := by
  rw [← componentGraphGeneratorOver_exteriorIdentityGenerator T φ C hC hCT]
  exact FiniteCorrespondenceGenerator.toIntegralCycle_exteriorIdentityGenerator_cycle _ T

end Components

namespace FiniteCorrespondence
open _root_.AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] {X Y : SmoothSite (Spec (.of k))}
  (T : SmoothSite (Spec (.of k))) [GeometricallyIntegral T.hom]

/-- Exterior extension preserves full actual graph cycles on arbitrary smooth objects. -/
theorem exteriorIdentity_componentGraphCycleOver (φ : X ⟶ Y) :
    exteriorIdentity (X := X) (Y := Y) T
        (componentGraphCycleOver (X := X.left) (Y := Y.left) φ.left (MorphismProperty.Over.w φ)) =
      componentGraphCycleOver (X := (SmoothSite.product X T).left)
        (Y := (SmoothSite.product Y T).left) (SmoothSite.productMap φ (𝟙 T)).left
        (MorphismProperty.Over.w (SmoothSite.productMap φ (𝟙 T))) := by
  classical
  let e : irreducibleComponents X.left ≃
      irreducibleComponents (SmoothSite.product X T).left :=
    ((pullback.fst X.hom T.hom).irreducibleComponentsEquiv
      (pullback.fst X.hom T.hom).isOpenMap).symm
  have he (C : irreducibleComponents X.left) :
      (e C).1 = (pullback.fst X.hom T.hom) ⁻¹' C.1 := rfl
  rw [componentGraphCycleOver_eq_sum, componentGraphCycleOver_eq_sum, map_sum]
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
      componentGraphGeneratorOver_exteriorIdentityGenerator T φ C hC' hCT]

@[simp] theorem exteriorIdentity_componentGraphCycleOver_simp (φ : X ⟶ Y) :
    @DFunLike.coe
      (FiniteCorrespondence X.hom Y.hom →+
        FiniteCorrespondence (pullback.fst X.hom T.hom ≫ X.hom)
          (pullback.fst Y.hom T.hom ≫ Y.hom))
      _ _ _ (exteriorIdentity (X := X) (Y := Y) T)
        (componentGraphCycleOver (X := X.left) (Y := Y.left) φ.left (MorphismProperty.Over.w φ)) =
      componentGraphCycleOver (X := (SmoothSite.product X T).left)
        (Y := (SmoothSite.product Y T).left) (SmoothSite.productMap φ (𝟙 T)).left
        (MorphismProperty.Over.w (SmoothSite.productMap φ (𝟙 T))) :=
  exteriorIdentity_componentGraphCycleOver T φ

end FiniteCorrespondence

namespace Cor
open _root_.AlgebraicGeometry.Scheme

variable {k : Type u} [Field k]

/-- Actual exterior extension commutes with graphs of arbitrary smooth-site maps. -/
theorem simplexExterior_graph (n : ℕ)
    {X Y : SmoothSite (Spec (.of k))} (φ : X ⟶ Y) :
    simplexExterior n ((graphFunctor k).map φ) =
      (graphFunctor k).map
        (SmoothSite.productMap φ (𝟙 (_root_.AlgebraicSimplex.smoothSiteObj k n))) :=
  FiniteCorrespondence.exteriorIdentity_componentGraphCycleOver
    (_root_.AlgebraicSimplex.smoothSiteObj k n) φ

@[simp] theorem simplexExterior_graph_simp (n : ℕ)
    {X Y : SmoothSite (Spec (.of k))} (φ : X ⟶ Y) :
    simplexExterior (X := ⟨X⟩) (Y := ⟨Y⟩) n ((graphFunctor k).map φ) =
      (graphFunctor k).map
        (SmoothSite.productMap φ (𝟙 (_root_.AlgebraicSimplex.smoothSiteObj k n))) :=
  simplexExterior_graph n φ

end Cor

end Motivic
