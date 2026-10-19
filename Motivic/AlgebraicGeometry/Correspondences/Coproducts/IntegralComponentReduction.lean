/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.IntegralComponents
public import Motivic.AlgebraicGeometry.Correspondences.Coproducts.Binary


/-!
# Reassembly along the actual integral components

The finite sum of the original diagonal components detects correspondence and
additive-presheaf equalities. No sheaf condition is used. This does not assert
that a direct summand of a free chart algebra is free.
-/

open _root_.AlgebraicGeometry.Scheme (SmoothSite)

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u v

namespace Motivic

local instance {k : Type u} [Field k] (X : SmoothSite (Spec (.of k))) :
    IsNoetherian ((𝟭 Scheme).obj X.left) :=
  inferInstanceAs (IsNoetherian X.left)

local instance {k : Type u} [Field k] (X : SmoothSite (Spec (.of k))) :
    IsReduced ((𝟭 Scheme).obj X.left) :=
  inferInstanceAs (IsReduced X.left)



namespace Cor

variable (k : Type u) [Field k]

/-- Each original diagonal component factors through its actual integral open. -/
theorem exists_component_identity_factorization
    (X : SmoothSite (Spec (.of k))) (Z : Set X.left)
    (hZ : Z ∈ irreducibleComponents X.left) :
    ∃ p : Cor.mk X ⟶ Cor.mk (SmoothSite.integralComponent k X Z hZ),
      p ≫ (graphFunctor k).map (SmoothSite.integralComponentι k X Z hZ) =
        (componentIdentityGenerator X.hom Z hZ).cycle := by
  apply exists_graph_factorization_of_range_subset k
  change Set.range (componentIdentityGenerator X.hom Z hZ).targetProjection ⊆
    Set.range (SmoothSite.componentOpen k X Z hZ).ι
  rw [componentIdentityGenerator_targetProjection, componentIdentityGenerator_range,
    (SmoothSite.componentOpen k X Z hZ).range_ι]
  exact Set.Subset.rfl

open Classical in
/-- The original identity as a finite sum, typed in the correspondence category. -/
theorem identity_eq_sum_integralComponents (X : SmoothSite (Spec (.of k))) :
    𝟙 (Cor.mk X) =
      ∑ Z ∈ TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.toFinset,
        if hZ : Z ∈ irreducibleComponents X.left then
          (show Cor.mk X ⟶ Cor.mk X from (componentIdentityGenerator X.hom Z hZ).cycle)
        else 0 := by
  classical
  exact componentIdentityCycle_eq_sum X.hom

/-- Correspondence equalities can be checked on the actual integral components. -/
theorem hom_ext_integralComponents {X Y : SmoothSite (Spec (.of k))}
    (α β : Cor.mk X ⟶ Cor.mk Y)
    (h : ∀ (Z : Set X.left) (hZ : Z ∈ irreducibleComponents X.left),
      (graphFunctor k).map (SmoothSite.integralComponentι k X Z hZ) ≫ α =
      (graphFunctor k).map (SmoothSite.integralComponentι k X Z hZ) ≫ β) : α = β := by
  classical
  have hc (Z : Set X.left) (hZ : Z ∈ irreducibleComponents X.left) :
      (componentIdentityGenerator X.hom Z hZ).cycle ≫ α =
      (componentIdentityGenerator X.hom Z hZ).cycle ≫ β := by
    obtain ⟨p, hp⟩ := exists_component_identity_factorization k X Z hZ
    rw [← hp, Category.assoc, Category.assoc, h Z hZ]
  have hi : (𝟙 (Cor.mk X)) ≫ α = (𝟙 (Cor.mk X)) ≫ β := by
    simp only [identity_eq_sum_integralComponents, Preadditive.sum_comp]
    apply Finset.sum_congr rfl
    intro Z _
    split_ifs with hz
    · exact hc Z hz
    · simp
  simpa using hi

end Cor

namespace PresheafWithTransfers

variable {k : Type u} [Field k]

/-- Additivity alone detects sections on the original finite clopen components.
This applies to arbitrary presheaves with transfers, without Nisnevich descent. -/
theorem sections_ext_integralComponents
    (F : (Cor k)ᵒᵖ ⥤ AddCommGrpCat.{v}) [F.Additive]
    (E : AddCommGrpCat.{v}) (X : SmoothSite (Spec (.of k)))
    (s t : E ⟶ F.obj (op (Cor.mk X)))
    (h : ∀ (Z : Set X.left) (hZ : Z ∈ irreducibleComponents X.left),
      s ≫ F.map ((Cor.graphFunctor k).map
        (SmoothSite.integralComponentι k X Z hZ)).op =
      t ≫ F.map ((Cor.graphFunctor k).map
        (SmoothSite.integralComponentι k X Z hZ)).op) : s = t := by
  classical
  have hc (Z : Set X.left) (hZ : Z ∈ irreducibleComponents X.left) :
      s ≫ F.map (show Cor.mk X ⟶ Cor.mk X from
        (componentIdentityGenerator X.hom Z hZ).cycle).op =
      t ≫ F.map (show Cor.mk X ⟶ Cor.mk X from
        (componentIdentityGenerator X.hom Z hZ).cycle).op := by
    obtain ⟨p, hp⟩ := Cor.exists_component_identity_factorization k X Z hZ
    rw [← hp, op_comp, F.map_comp, ← Category.assoc, ← Category.assoc, h Z hZ]
  have hi : s ≫ F.map (𝟙 (Cor.mk X)).op = t ≫ F.map (𝟙 (Cor.mk X)).op := by
    simp only [Cor.identity_eq_sum_integralComponents, op_sum, F.map_sum,
      Preadditive.comp_sum]
    apply Finset.sum_congr rfl
    intro Z _
    split_ifs with hz
    · exact hc Z hz
    · simp
  simpa using hi

end PresheafWithTransfers

end Motivic
