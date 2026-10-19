/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.Boundary.Presheaf.RefinementImage
public import Motivic.Cohomology.A1.Contraction.RelativeNaturality

/-! # Geometric punctures give the original boundary image sieve -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace Motivic.FiniteEtaleSite.OriginalPresheaf
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
private theorem compose_projection_relations {C : Type*} [Category C]
    {A B D E G H I : C} (e : A ⟶ B) (m : B ⟶ D) (p : D ⟶ E) (o : E ⟶ I)
    (r : D ⟶ G) (s : G ⟶ I) (t : B ⟶ H) (g : H ⟶ G) (a : A ⟶ H)
    (hp : p ≫ o = r ≫ s) (hm : m ≫ r = t ≫ g) (he : e ≫ t = a) :
    (e ≫ m ≫ p) ≫ o = a ≫ g ≫ s := by
  rw [Category.assoc, Category.assoc, hp, ← Category.assoc m r s, hm,
    Category.assoc t g s, ← Category.assoc e t (g ≫ s), he]

variable {k : Type u} [Field k] (X : SmoothSite (Spec (.of k)))

/-- The literal puncture square commutes with an actual base neighborhood. -/
theorem contractionOpen_base_isPullback (V : EtaleSeparatedFiniteType X.left) :
    IsPullback
      (SmoothSite.contractionOpen (.of k) ((toSmoothSite X).obj V)).left
      (SmoothSite.productMap (toBase X V) (𝟙 (SmoothSite.torus (.of k)))).left
      ((cylinderNeighborhood X).obj V).hom
      (SmoothSite.contractionOpen (.of k) X).left := by
  have hf (Y : SmoothSite (Spec (.of k))) :
      (SmoothSite.contractionOpen (.of k) Y).left ≫
        (SmoothSite.productFst Y (SmoothSite.affineLine (.of k))).left =
      (SmoothSite.productFst Y (SmoothSite.torus (.of k))).left := by
    have h := congrArg (fun f => f.left) (SmoothSite.productMap_fst (𝟙 Y)
      (SmoothSite.torusInAffineLine (.of k)))
    change (SmoothSite.contractionOpen (.of k) Y).left ≫
      (SmoothSite.productFst Y (SmoothSite.affineLine (.of k))).left =
      (SmoothSite.productFst Y (SmoothSite.torus (.of k))).left ≫ 𝟙 Y.left at h
    simpa only [Category.comp_id] using h
  apply IsPullback.of_right
    (h₁₂ := (SmoothSite.productFst ((toSmoothSite X).obj V)
      (SmoothSite.affineLine (.of k))).left)
    (h₂₂ := (SmoothSite.productFst X (SmoothSite.affineLine (.of k))).left)
    (v₁₃ := V.hom)
  · rw [hf, hf]
    exact (parameterProduct_isPullback X (SmoothSite.torus (.of k)) V).flip
  · exact congrArg (fun f => f.left)
      (SmoothSite.contractionOpen_naturality (.of k) (toBase X V))
  · exact (parameterProduct_isPullback X (SmoothSite.affineLine (.of k)) V).flip

variable {W W' : EtaleSeparatedFiniteType (SmoothSite.a1Cylinder (.of k) X).left}
  (V : EtaleSeparatedFiniteType X.left) (b : W' ⟶ (cylinderNeighborhood X).obj V)
  (z : V.left ⟶ W'.left)
  (hz : z ≫ b.left =
    (SmoothSite.a1Section (.of k) ((toSmoothSite X).obj V) 0).left)

/-- The prescribed whole zero marking lifts to the genuine closed pullback. -/
def geometricZeroLift :
    V ⟶ (baseChange (SmoothSite.a1Section (.of k) X 0).left).obj W' :=
  MorphismProperty.Over.homMk (pullback.lift z V.hom (by
    rw [← MorphismProperty.Over.w b, ← Category.assoc, hz]
    exact congrArg (fun f => f.left)
      (SmoothSite.a1Section_naturality (.of k) (toBase X V) 0)))
    (pullback.lift_snd _ _ _)

/-- This is the original cylinder's zero lift, not merely a map with the same support. -/
theorem geometricZeroLift_comp :
    geometricZeroLift X V b z hz ≫
      (baseChange (SmoothSite.a1Section (.of k) X 0).left).map b =
        zeroNeighborhoodLift X V := by
  have hf : (zeroNeighborhoodLift X V).left ≫
      pullback.fst ((cylinderNeighborhood X).obj V).hom
        (SmoothSite.a1Section (.of k) X 0).left =
      (SmoothSite.a1Section (.of k) ((toSmoothSite X).obj V) 0).left :=
    pullback.lift_fst _ _ _
  have hs : (zeroNeighborhoodLift X V).left ≫
      pullback.snd ((cylinderNeighborhood X).obj V).hom
        (SmoothSite.a1Section (.of k) X 0).left = V.hom :=
    pullback.lift_snd _ _ _
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext
  · rw [hf]
    change (pullback.lift z V.hom _) ≫
      (pullback.lift _ _ _) ≫ pullback.fst _ _ = _
    simp only [pullback.lift_fst, pullback.lift_fst_assoc]
    exact hz
  · rw [hs]
    change (pullback.lift z V.hom _) ≫
      (pullback.lift _ _ _) ≫ pullback.snd _ _ = _
    simp only [pullback.lift_snd]

variable (P : PresheafWithTransfers.{u + 1} k)
  (O : SmoothSite (Spec (.of k)))
  (α : O ⟶ (toSmoothSite (SmoothSite.a1Cylinder (.of k) X)).obj W')
  (β : O ⟶ SmoothSite.torusCylinder (.of k) ((toSmoothSite X).obj V))
  (H : IsPullback β.left α.left
    (SmoothSite.contractionOpen (.of k) ((toSmoothSite X).obj V)).left b.left)

/-- The geometric puncture is the actual punctured small-site neighborhood. -/
def geometricPunctureIso : O ≅
    (toSmoothSite (SmoothSite.torusCylinder (.of k) X)).obj
      ((baseChange (SmoothSite.contractionOpen (.of k) X).left).obj W') := by
  have ht : IsPullback α.left
      (β.left ≫ (SmoothSite.productMap (toBase X V)
        (𝟙 (SmoothSite.torus (.of k)))).left)
      W'.hom (SmoothSite.contractionOpen (.of k) X).left := by
    simpa only [MorphismProperty.Over.w b] using
      (H.paste_horiz (contractionOpen_base_isPullback X V).flip).flip
  exact MorphismProperty.Over.isoMk ht.isoPullback (by
    change ht.isoPullback.hom ≫
      (pullback.snd W'.hom (SmoothSite.contractionOpen (.of k) X).left ≫
        (SmoothSite.torusCylinder (.of k) X).hom) = O.hom
    rw [← Category.assoc, ht.isoPullback_hom_snd]
    change (β ≫ SmoothSite.productMap (toBase X V)
      (𝟙 (SmoothSite.torus (.of k)))).left ≫
        (SmoothSite.torusCylinder (.of k) X).hom = O.hom
    exact MorphismProperty.Over.w _)

include H in
/-- A signed difference on an actual Cartesian geometric puncture supplies an
original canonical image-sieve witness. Neither a sheaf premise on P nor an
abstract image witness is an input. -/
theorem imageSieve_of_geometric_difference (f : W' ⟶ W)
    (φ : O ⟶ (toSmoothSite (SmoothSite.torusCylinder (.of k) X)).obj
      ((baseChange (SmoothSite.contractionOpen (.of k) X).left).obj W))
    (hφ₁ : φ.left ≫ pullback.fst W.hom
        (SmoothSite.contractionOpen (.of k) X).left = α.left ≫ f.left)
    (hφ₂ : φ.left ≫ pullback.snd W.hom
        (SmoothSite.contractionOpen (.of k) X).left = β.left ≫
      (SmoothSite.productMap (toBase X V) (𝟙 (SmoothSite.torus (.of k)))).left)
    (s : ((PresheafWithTransfers.toPresheaf k).obj P).obj (op
      ((toSmoothSite (SmoothSite.torusCylinder (.of k) X)).obj
        ((baseChange (SmoothSite.contractionOpen (.of k) X).left).obj W))))
    (a : ((PresheafWithTransfers.toPresheaf k).obj P).obj
      (op (SmoothSite.torusCylinder (.of k) ((toSmoothSite X).obj V))))
    (c : ((PresheafWithTransfers.toPresheaf k).obj P).obj
      (op ((toSmoothSite (SmoothSite.a1Cylinder (.of k) X)).obj W')))
    (h : ((PresheafWithTransfers.toPresheaf k).obj P).map β.op a -
      ((PresheafWithTransfers.toPresheaf k).obj P).map α.op c =
      ((PresheafWithTransfers.toPresheaf k).obj P).map φ.op s) :
    Presheaf.imageSieve (contractionToBoundary X P).hom
      ((presheafBoundaryGenerator ((PresheafWithTransfers.toPresheaf k).obj P)
        (SmoothSite.contractionOpen (.of k) X)
        (SmoothSite.a1Section (.of k) X 0)).app (op W) s)
      (geometricZeroLift X V b z hz ≫
        (baseChange (SmoothSite.a1Section (.of k) X 0).left).map f) := by
  let F := (PresheafWithTransfers.toPresheaf k).obj P
  let e := geometricPunctureIso X V b O α β H
  have he₁ : e.hom ≫
      (restrictionProjection (SmoothSite.contractionOpen (.of k) X)).app W' = α := by
    apply MorphismProperty.Over.Hom.ext
    change e.hom.left ≫ pullback.fst W'.hom
      (SmoothSite.contractionOpen (.of k) X).left = α.left
    exact IsPullback.isoPullback_hom_fst _
  have he₂ : e.hom.left ≫ pullback.snd W'.hom
      (SmoothSite.contractionOpen (.of k) X).left = β.left ≫
      (SmoothSite.productMap (toBase X V) (𝟙 (SmoothSite.torus (.of k)))).left :=
    IsPullback.isoPullback_hom_snd _
  have heβ : e.hom ≫ (toSmoothSite (SmoothSite.torusCylinder (.of k) X)).map
      ((baseChange (SmoothSite.contractionOpen (.of k) X).left).map b) ≫
        puncturedProjection X V = β := by
    apply (cancel_mono (SmoothSite.contractionOpen (.of k)
      ((toSmoothSite X).obj V))).mp
    have hb : (toSmoothSite (SmoothSite.torusCylinder (.of k) X)).map
        ((baseChange (SmoothSite.contractionOpen (.of k) X).left).map b) ≫
          (restrictionProjection (SmoothSite.contractionOpen (.of k) X)).app
            ((cylinderNeighborhood X).obj V) =
        (restrictionProjection (SmoothSite.contractionOpen (.of k) X)).app W' ≫
          (toSmoothSite (SmoothSite.a1Cylinder (.of k) X)).map b :=
      (restrictionProjection (SmoothSite.contractionOpen (.of k) X)).naturality b
    have ht := compose_projection_relations e.hom
      ((toSmoothSite (SmoothSite.torusCylinder (.of k) X)).map
        ((baseChange (SmoothSite.contractionOpen (.of k) X).left).map b))
      (puncturedProjection X V)
      (SmoothSite.contractionOpen (.of k) ((toSmoothSite X).obj V))
      ((restrictionProjection (SmoothSite.contractionOpen (.of k) X)).app
        ((cylinderNeighborhood X).obj V))
      ((parameterProductUnderlyingIso X (SmoothSite.affineLine (.of k))).hom.app V)
      ((restrictionProjection (SmoothSite.contractionOpen (.of k) X)).app W')
      ((toSmoothSite (SmoothSite.a1Cylinder (.of k) X)).map b) α
      (puncturedProjection_open X V) hb he₁
    refine ht.trans ?_
    apply MorphismProperty.Over.Hom.ext
    change α.left ≫ b.left ≫ 𝟙 _ = β.left ≫
      (SmoothSite.contractionOpen (.of k) ((toSmoothSite X).obj V)).left
    rw [Category.comp_id]
    exact H.w.symm
  have heφ : e.hom ≫ (toSmoothSite (SmoothSite.torusCylinder (.of k) X)).map
      ((baseChange (SmoothSite.contractionOpen (.of k) X).left).map f) = φ := by
    have hf₁ : ((baseChange (SmoothSite.contractionOpen (.of k) X).left).map f).left ≫
        pullback.fst W.hom (SmoothSite.contractionOpen (.of k) X).left =
      pullback.fst W'.hom (SmoothSite.contractionOpen (.of k) X).left ≫ f.left :=
      pullback.lift_fst _ _ _
    have hf₂ : ((baseChange (SmoothSite.contractionOpen (.of k) X).left).map f).left ≫
        pullback.snd W.hom (SmoothSite.contractionOpen (.of k) X).left =
      pullback.snd W'.hom (SmoothSite.contractionOpen (.of k) X).left :=
      pullback.lift_snd _ _ _
    have he₁' : e.hom.left ≫ pullback.fst W'.hom
        (SmoothSite.contractionOpen (.of k) X).left = α.left :=
      congrArg (fun m => m.left) he₁
    apply MorphismProperty.Over.Hom.ext
    change e.hom.left ≫
      ((baseChange (SmoothSite.contractionOpen (.of k) X).left).map f).left = φ.left
    apply pullback.hom_ext
    · rw [Category.assoc, hf₁, ← Category.assoc, he₁', hφ₁]
    · rw [Category.assoc, hf₂, he₂, hφ₂]
  let a' := ((PresheafWithTransfers.withParameterUnderlyingIso P
    (SmoothSite.torus (.of k))).inv.app (op ((toSmoothSite X).obj V))) a
  have ha' : (laurentToPunctured X P).app (op V) a' =
      F.map (puncturedProjection X V).op a := by
    dsimp only [laurentToPunctured, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, NatTrans.op_app]
    rw [ConcreteCategory.comp_apply]
    congr 1
  apply imageSieve_of_refinement_difference X P V f b
    (geometricZeroLift X V b z hz) (geometricZeroLift_comp X V b z hz) s a' c
  apply (ConcreteCategory.bijective_of_isIso (F.map e.hom.op)).injective
  rw [map_sub, ha']
  change F.map e.hom.op (F.map
    ((toSmoothSite (SmoothSite.torusCylinder (.of k) X)).map
      ((baseChange (SmoothSite.contractionOpen (.of k) X).left).map b)).op
        (F.map (puncturedProjection X V).op a)) -
    F.map e.hom.op (F.map
      ((restrictionProjection (SmoothSite.contractionOpen (.of k) X)).app W').op c) =
    F.map e.hom.op (F.map
      ((toSmoothSite (SmoothSite.torusCylinder (.of k) X)).map
        ((baseChange (SmoothSite.contractionOpen (.of k) X).left).map f)).op s)
  have hβa := congrArg (fun m => F.map m.op a) heβ
  have hαc := congrArg (fun m => F.map m.op c) he₁
  have hφs := congrArg (fun m => F.map m.op s) heφ
  simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply] at hβa hαc hφs
  exact (congrArg₂ (fun x y => x - y) hβa hαc).trans (h.trans hφs.symm)

end Motivic.FiniteEtaleSite.OriginalPresheaf
