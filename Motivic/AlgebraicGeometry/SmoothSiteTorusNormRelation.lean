/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.SmoothSiteTorusDivisor
public import Motivic.AlgebraicGeometry.Correspondences.AffineTorusIdentityGraph
public import Motivic.AlgebraicGeometry.Correspondences.IntegralSourceBaseCorrespondences

/-! # The actual ordinary norm annihilates the original identity-axis relation -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.PolynomialLaurent
open Motivic.AffineTorusPolynomialPresentation Motivic.SmoothSiteAffineCoordinates
open Polynomial.BoundaryOneRationalFunctions Motivic.PresheafWithTransfers

universe u

namespace Motivic.SmoothSiteTorusDivisor

variable {k : Type u} [Field k]
attribute [local instance] sectionsAlgebra

local instance (X : SmoothSite (Spec (.of k))) [IsIntegral X.left] :
    IsIntegral ((𝟭 Scheme).obj X.left) := inferInstanceAs (IsIntegral X.left)

local instance (X : SmoothSite (Spec (.of k))) :
    IsNoetherian ((𝟭 Scheme).obj X.left) := inferInstanceAs (IsNoetherian X.left)

/-- The original structure morphism, retained as a morphism of smooth-site objects. -/
def structureMorphism (X : SmoothSite (Spec (.of k))) : X ⟶ SmoothSite.base (Spec (.of k)) :=
  SmoothSite.homMk X.hom (Category.comp_id _)

/-- On an integral source the actual structure graph has its single original generator. -/
theorem graph_structureMorphism (X : SmoothSite (Spec (.of k))) [IsIntegral X.left] :
    (Cor.graphFunctor k).map (structureMorphism X) = (structureGraphGenerator X.hom).cycle := by
  change componentGraphCycleOver X.hom (Category.comp_id X.hom) = _
  exact componentGraphCycleOver_eq_graphGeneratorOver_cycle X.hom (Category.comp_id X.hom)

/-- Every original correspondence into the base is an integer multiple of its structure graph. -/
theorem baseCorrespondence_eq_zsmul (X : SmoothSite (Spec (.of k))) [IsIntegral X.left]
    (a : Cor.mk X ⟶ Cor.mk (SmoothSite.base (Spec (.of k)))) :
    ∃ n : ℤ, a = n • (Cor.graphFunctor k).map (structureMorphism X) := by
  let b : FiniteCorrespondence X.hom (𝟙 (Spec (.of k))) := a
  refine ⟨b (structureGraphGenerator X.hom), ?_⟩
  rw [graph_structureMorphism]
  exact b.eq_coefficient_zsmul_structureGraph X.hom

/-- The actual affine-coordinate map respects the original structural graph. -/
@[reassoc] theorem affineIso_structureMorphism
    (X : SmoothSite (Spec (.of k))) [IsAffine X.left] :
    (affineIso X).hom ≫ structureMorphism X =
      affineStructureMorphism (k := k) (R := Γ(X.left, ⊤)) := by
  apply MorphismProperty.Over.Hom.ext
  exact isoSpec_inv_base X

/-- The original constant-one graph has trivial norm on every integral affine source. -/
theorem affineNorm_structureOne (X : SmoothSite (Spec (.of k)))
    [IsAffine X.left] [IsIntegral X.left] :
    affineNorm X
      ((Cor.graphFunctor k).map (structureMorphism X ≫ SmoothSite.torusOne (.of k))) = 0 := by
  have hc : affineCycleCoordinates X
      ((Cor.graphFunctor k).map (structureMorphism X ≫ SmoothSite.torusOne (.of k))) =
        (Cor.graphFunctor k).map (unitMorphism (k := k) (1 : (Γ(X.left, ⊤))ˣ)) := by
    change (Cor.graphFunctor k).map (affineIso X).hom ≫
      (Cor.graphFunctor k).map (structureMorphism X ≫ SmoothSite.torusOne (.of k)) = _
    rw [← Functor.map_comp, ← Category.assoc, affineIso_structureMorphism, ← unitMorphism_one]
  have he := congrArg ((signedValueHom (R := Γ(X.left, ⊤))).toAdditive.comp
    (cycleRationalFunction (k := k))) hc
  exact he.trans (signedValue_identityGraph (k := k) (R := Γ(X.left, ⊤)))

/-- The original power-one identity axis is annihilated on integral affine sources. -/
theorem affinePowerOneNorm_identityAxis (X : SmoothSite (Spec (.of k)))
    [IsAffine X.left] [IsIntegral X.left]
    (a : Cor.mk X ⟶ Cor.mk (SmoothSite.torusPower (.of k) 0)) :
    affinePowerOneNorm X
      (a ≫ (Cor.graphFunctor k).map (SmoothSite.torusInsertOne (.of k) 0 0)) = 0 := by
  obtain ⟨n, hn⟩ := baseCorrespondence_eq_zsmul X a
  change affineNorm X ((a ≫ (Cor.graphFunctor k).map (SmoothSite.torusInsertOne (.of k) 0 0)) ≫
    (Cor.graphFunctor k).map (SmoothSite.torusPowerOneIso (.of k)).hom) = 0
  rw [Category.assoc, ← Functor.map_comp, SmoothSite.torusInsertOne_zero_powerOneIso,
    hn, Preadditive.zsmul_comp, map_zsmul, ← Functor.map_comp,
    affineNorm_structureOne, smul_zero]

/-- The actual norm annihilates the original identity-axis map as an ordinary presheaf morphism. -/
theorem norm_identityAxis :
    (toPresheaf k).map (torusIdentityAxis k 1 0) ≫ norm = 0 := by
  apply (Functor.whiskerLeft_obj_map_bijective_of_isCoverDense
    (SmoothSite.nisnevichTopology (Spec (.of k))) (SmoothSite.integralAffineInclusion k) _ _
    (SmoothSite.largeUnitsPresheaf_isSheaf (Spec (.of k)))).injective
  apply NatTrans.ext
  funext X
  let : IsAffine X.unop.obj.left := X.unop.property.1
  let : IsIntegral X.unop.obj.left := X.unop.property.2
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro a
  change norm.app (op X.unop.obj)
    (((toPresheaf k).map (torusIdentityAxis k 1 0)).app (op X.unop.obj) a) = 0
  rw [norm_app]
  change ULift.up (affinePowerOneNorm X.unop.obj
    (a.down ≫ (Cor.graphFunctor k).map (SmoothSite.torusInsertOne (.of k) 0 0))) = ULift.up 0
  exact congrArg ULift.up (affinePowerOneNorm_identityAxis X.unop.obj a.down)

end Motivic.SmoothSiteTorusDivisor
