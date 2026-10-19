/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.Presheaf.ContractionHI

/-!
# Contraction preserves ordinary homotopy invariance

The literal exchange of the last two product factors identifies the affine-line
projection of parameter sections with the affine-line projection of the actual
parameter product. Hence ordinary homotopy invariance passes to parameter
sections, including the affine line and the Laurent torus. The actual Laurent
quotient then descends the inverse supplied by a constant section, proving that
its literal projection pullback is invertible. No sheafification or strict
invariance hypothesis is used.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe v u

namespace AlgebraicGeometry.Scheme.SmoothSite

variable {S : Scheme.{u}}

/-- Exchange the last two factors of the actual relative triple product. -/
def productSwapRight (X Y Z : SmoothSite S) :
    product (product X Y) Z ≅ product (product X Z) Y where
  hom := productLift
    (productLift (productFst (product X Y) Z ≫ productFst X Y)
      (productSnd (product X Y) Z))
    (productFst (product X Y) Z ≫ productSnd X Y)
  inv := productLift
    (productLift (productFst (product X Z) Y ≫ productFst X Z)
      (productSnd (product X Z) Y))
    (productFst (product X Z) Y ≫ productSnd X Z)
  hom_inv_id := by
    apply product_hom_ext
    · apply product_hom_ext <;> simp
    · simp
  inv_hom_id := by
    apply product_hom_ext
    · apply product_hom_ext <;> simp
    · simp

/-- The exchange identifies the two literal projections dropping the middle factor. -/
@[reassoc (attr := simp)] theorem productSwapRight_hom_fst (X Y Z : SmoothSite S) :
    (productSwapRight X Y Z).hom ≫ productFst (product X Z) Y =
      productMap (productFst X Y) (𝟙 Z) := by
  apply product_hom_ext <;> simp [productSwapRight]

end AlgebraicGeometry.Scheme.SmoothSite

namespace Motivic.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme

variable {k : Type u} [Field k]

/-- Ordinary HI is preserved by the actual product with a smooth integral parameter. -/
theorem withParameter_isA1Invariant (P : PresheafWithTransfers.{v} k)
    (hP : IsA1Invariant P) (T : SmoothSite (Spec (.of k)))
    [GeometricallyIntegral T.hom] : IsA1Invariant (withParameter P T) := by
  intro X
  change IsIso (transfer P ((Cor.parameterProduct T).map
    ((Cor.graphFunctor k).map (SmoothSite.a1Projection (.of k) X))))
  rw [Cor.parameterProduct_graph]
  let e := P.obj.mapIso ((Cor.graphFunctor k).mapIso
    (SmoothSite.productSwapRight X (SmoothSite.affineLine (.of k)) T)).op
  have he : IsIso e.hom := inferInstance
  have h : A1.projectionPullback (.of k) ((toPresheaf k).obj P)
      (SmoothSite.product X T) ≫ e.hom =
      transfer P ((Cor.graphFunctor k).map
        (SmoothSite.productMap (SmoothSite.a1Projection (.of k) X) (𝟙 T))) := by
    change transfer P ((Cor.graphFunctor k).map
        (SmoothSite.productFst (SmoothSite.product X T) (SmoothSite.affineLine (.of k)))) ≫
      transfer P ((Cor.graphFunctor k).map (SmoothSite.productSwapRight X _ T).hom) = _
    rw [← transfer_comp, ← Functor.map_comp, SmoothSite.productSwapRight_hom_fst]
    rfl
  have := hP (SmoothSite.product X T)
  rw [← h]
  infer_instance

/-- The genuine cokernel contraction is homotopy invariant whenever its coefficients are. -/
theorem contraction_isA1Invariant (P : PresheafWithTransfers.{v} k)
    (hP : IsA1Invariant P) : IsA1Invariant (contraction P) := by
  intro X
  let R := CommRingCat.of k
  let Q := (toPresheaf k).obj (contraction P)
  let L := (toPresheaf k).obj (torusSections P)
  let η := (toPresheaf k).map (toContraction P)
  let p := A1.projectionPullback R Q X
  let s := A1.sectionPullback R Q X 0
  have hp : p ≫ s = 𝟙 _ := A1.projectionPullback_sectionPullback R Q X 0
  have hs : s ≫ p = 𝟙 _ := by
    have hep : Epi (η.app (op (SmoothSite.a1Cylinder R X))) := by
      change Epi ((cokernel.π (contractionRestriction P).hom).app _)
      infer_instance
    apply (cancel_epi (η.app (op (SmoothSite.a1Cylinder R X)))).mp
    have hn := η.naturality (SmoothSite.a1Section R X 0).op
    have hm := η.naturality (SmoothSite.a1Projection R X).op
    change A1.sectionPullback R L X 0 ≫ η.app (op X) =
      η.app (op (SmoothSite.a1Cylinder R X)) ≫ s at hn
    change A1.projectionPullback R L X ≫ η.app (op (SmoothSite.a1Cylinder R X)) =
      η.app (op X) ≫ p at hm
    rw [← Category.assoc, ← hn, Category.assoc, ← hm, ← Category.assoc]
    have hL := withParameter_isA1Invariant P hP (SmoothSite.torus R)
    let e := A1.projectionIso R L hL X
    have he : A1.sectionPullback R L X 0 ≫ A1.projectionPullback R L X = 𝟙 _ := by
      rw [← A1.projectionIso_inv R L hL X 0]
      exact e.inv_hom_id
    rw [he, Category.id_comp, Category.comp_id]
  exact ⟨⟨s, hp, hs⟩⟩

end Motivic.PresheafWithTransfers
