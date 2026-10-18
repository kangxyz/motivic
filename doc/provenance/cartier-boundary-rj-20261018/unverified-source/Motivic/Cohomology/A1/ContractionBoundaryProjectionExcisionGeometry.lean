/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.ContractionBoundaryProjectionGeometry
public import Motivic.Cohomology.A1.BoundaryEtalePullback
public import Motivic.AlgebraicGeometry.Sites.FiniteEtaleA1BaseChange

/-! # The actual product of a chosen étale zero-section chart

The normal parameter stays last. The resulting comparison is an isomorphism
of actual neighborhood functors, not a smooth inverse-image coefficient
isomorphism. Both original projections are retained.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.SmoothSite

variable (R : CommRingCat.{u}) (X : SmoothSite (Spec R))
  {E : SmoothSite (Spec R)} (b : E ⟶ a1Cylinder R X)

/-- The chosen chart times the homotopy line, retaining the normal coordinate last. -/
def contractionChartProduct : a1Cylinder R E ⟶ a1Cylinder R (a1Cylinder R X) :=
  a1Map R b ≫ (productSwapLastIso X (affineLine R) (affineLine R)).hom

/-- The product chart lies over its original chart, with the literal projection. -/
@[reassoc (attr := simp)]
theorem contractionChartProduct_projection :
    contractionChartProduct R X b ≫ a1Map R (a1Projection R X) =
      a1Projection R E ≫ b := by
  change (a1Map R b ≫ productSwapLast X (affineLine R) (affineLine R)) ≫
      a1Map R (a1Projection R X) = _
  have hs : productSwapLast X (affineLine R) (affineLine R) ≫
      productSwapLast X (affineLine R) (affineLine R) = 𝟙 _ :=
    (productSwapLastIso X (affineLine R) (affineLine R)).hom_inv_id
  rw [Category.assoc, ← a1Projection_productSwapLast R X]
  rw [← Category.assoc (productSwapLast X (affineLine R) (affineLine R)), hs,
    Category.id_comp, a1Map_projection]

/-- Products preserve the full Cartesian chart square, not only the marked point. -/
theorem contractionChartProduct_isPullback :
    IsPullback (contractionChartProduct R X b).left (a1Projection R E).left
      (a1Map R (a1Projection R X)).left b.left := by
  have h : IsPullback (a1Map R b).left (a1Projection R E).left
      (a1Projection R (a1Cylinder R X)).left b.left := by
    apply IsPullback.of_right
      (h₁₂ := (productSnd (a1Cylinder R X) (affineLine R)).left)
      (h₂₂ := (a1Cylinder R X).hom) (v₁₃ := (affineLine R).hom)
    · have hs := congrArg (fun f ↦ f.left)
        (productMap_snd b (𝟙 (affineLine R)))
      change (a1Map R b).left ≫ (productSnd (a1Cylinder R X) (affineLine R)).left =
        (productSnd E (affineLine R)).left ≫ 𝟙 _ at hs
      rw [hs, Category.comp_id, MorphismProperty.Over.w b]
      exact (IsPullback.of_hasPullback E.hom (affineLine R).hom).flip
    · exact congrArg (fun f ↦ f.left) (a1Map_projection R b)
    · exact (IsPullback.of_hasPullback (a1Cylinder R X).hom (affineLine R).hom).flip
  refine h.of_iso (Iso.refl _)
    ((forgetScheme (Spec R)).mapIso
      (productSwapLastIso X (affineLine R) (affineLine R)))
    (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp only [Iso.refl_hom, Category.id_comp]
    rfl
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · simpa only [Iso.refl_hom, Category.comp_id, contractionChartProduct,
      a1Map_id, Category.id_comp] using
      congrArg (fun f ↦ f.left)
        (contractionChartProduct_projection R X (𝟙 (a1Cylinder R X))).symm
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]

instance contractionChartProduct_etale [Etale b.left] :
    Etale (contractionChartProduct R X b).left :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @Etale) (contractionChartProduct_isPullback R X b).flip inferInstance

/-- The whole zero section is retained after taking the chart product. -/
theorem contractionChartProduct_zero {a : X ⟶ E}
    (ha : a ≫ b = a1Section R X 0) :
    a1Map R a ≫ contractionChartProduct R X b =
      a1Section R (a1Cylinder R X) 0 := by
  rw [contractionChartProduct, ← Category.assoc, ← a1Map_comp, ha,
    ← a1Section_productSwapLast R X 0]
  have hs : productSwapLast X (affineLine R) (affineLine R) ≫
      productSwapLast X (affineLine R) (affineLine R) = 𝟙 _ :=
    (productSwapLastIso X (affineLine R) (affineLine R)).hom_inv_id
  change (_ ≫ productSwapLast X (affineLine R) (affineLine R)) ≫
      productSwapLast X (affineLine R) (affineLine R) = _
  rw [Category.assoc, hs, Category.comp_id]

/-- The punctured product chart uses the same displayed parameter permutation. -/
def contractionChartPunctureProduct {U : SmoothSite (Spec R)}
    (q : U ⟶ torusCylinder R X) :
    a1Cylinder R U ⟶ torusCylinder R (a1Cylinder R X) :=
  a1Map R q ≫ (productSwapLastIso X (torus R) (affineLine R)).hom

/-- The original open immersion is retained by the actual parameter permutation. -/
theorem contractionChartProduct_open :
    a1Map R (contractionOpen R X) ≫
        (productSwapLastIso X (affineLine R) (affineLine R)).hom =
      (productSwapLastIso X (torus R) (affineLine R)).hom ≫
        contractionOpen R (a1Cylinder R X) := by
  simpa only [productSwapLastIso, contractionOpen, a1Map, productMap_id] using
    productSwapLast_naturality X (torus R) (affineLine R)
      (𝟙 X) (torusInAffineLine R) (𝟙 (affineLine R))

/-- A chosen punctured chart square remains Cartesian after product with the
whole homotopy line, with the normal coordinate still last. -/
theorem contractionChartPunctureProduct_isPullback
    {U : SmoothSite (Spec R)} (j : U ⟶ E) (q : U ⟶ torusCylinder R X)
    (hpb : IsPullback q j (contractionOpen R X) b) :
    IsPullback (contractionChartPunctureProduct R X q) (a1Map R j)
      (contractionOpen R (a1Cylinder R X)) (contractionChartProduct R X b) := by
  have h := (parameterProduct (affineLine R)).map_isPullback hpb
  refine h.of_iso (Iso.refl _)
    (productSwapLastIso X (torus R) (affineLine R))
    (Iso.refl _) (productSwapLastIso X (affineLine R) (affineLine R)) ?_ ?_ ?_ ?_
  · simp only [Iso.refl_hom, Category.id_comp]
    rfl
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · exact contractionChartProduct_open R X
  · simp only [Iso.refl_hom, Category.id_comp]
    rfl

end Motivic.SmoothSite

namespace Motivic.FiniteEtaleSite

section Product

variable {R : CommRingCat.{u}} {U E : SmoothSite (Spec R)} (j : U ⟶ E)

/-- The literal product square of a puncture commutes on actual neighborhood
pullbacks, without any coefficient inverse-image comparison. -/
def a1PunctureProjectionBaseChangeIso :
    baseChange (SmoothSite.a1Projection R E).left ⋙
        baseChange (SmoothSite.a1Map R j).left ≅
      baseChange j.left ⋙ baseChange (SmoothSite.a1Projection R U).left :=
  (MorphismProperty.Over.pullbackComp (P := etaleSeparatedFiniteType) (Q := ⊤)
    (SmoothSite.a1Map R j).left (SmoothSite.a1Projection R E).left).symm ≪≫
    MorphismProperty.Over.pullbackComp (SmoothSite.a1Projection R U).left j.left
      (fg := (SmoothSite.a1Map R j ≫ SmoothSite.a1Projection R E).left)
      (hfg := congrArg (fun f ↦ f.left) (SmoothSite.a1Map_projection R j))

/-- The product-puncture comparison retains the original ambient projection. -/
@[reassoc (attr := simp)]
theorem a1PunctureProjectionBaseChangeIso_fst (V : FiniteEtaleSite E.left) :
    ((a1PunctureProjectionBaseChangeIso j).hom.app V).left ≫
        pullback.fst (pullback.snd V.hom j.left) (SmoothSite.a1Projection R U).left ≫
        pullback.fst V.hom j.left =
      pullback.fst (pullback.snd V.hom (SmoothSite.a1Projection R E).left)
          (SmoothSite.a1Map R j).left ≫
        pullback.fst V.hom (SmoothSite.a1Projection R E).left := by
  simp [a1PunctureProjectionBaseChangeIso,
    MorphismProperty.Over.pullbackComp_hom_app_left,
    MorphismProperty.Over.pullbackComp_inv_app_left]

/-- The actual puncture restriction commutes with the original base-change to
cylinder comparison. This is an equality of the specified geometric maps, not
an identification of coefficient inverse images. -/
theorem a1PunctureProjectionBaseChangeIso_restriction (V : FiniteEtaleSite E.left) :
    (restrictionProjection (SmoothSite.a1Map R j)).app
        ((baseChange (SmoothSite.a1Projection R E).left).obj V) ≫
        (a1BaseChangeIso R E V).hom =
      (toSmoothSite (SmoothSite.a1Cylinder R U)).map
          ((a1PunctureProjectionBaseChangeIso j).hom.app V) ≫
        (a1BaseChangeIso R U ((baseChange j.left).obj V)).hom ≫
        SmoothSite.a1Map R ((restrictionProjection j).app V) := by
  apply SmoothSite.product_hom_ext
  · change ((restrictionProjection (SmoothSite.a1Map R j)).app
          ((baseChange (SmoothSite.a1Projection R E).left).obj V) ≫
        (a1BaseChangeIso R E V).hom) ≫
        SmoothSite.a1Projection R ((toSmoothSite E).obj V) = _
    simp only [Category.assoc]
    rw [a1BaseChangeIso_hom_projection, SmoothSite.a1Map_projection,
      ← Category.assoc (a1BaseChangeIso R U ((baseChange j.left).obj V)).hom,
      a1BaseChangeIso_hom_projection]
    apply MorphismProperty.Over.Hom.ext
    exact (a1PunctureProjectionBaseChangeIso_fst j V).symm
  · have hE : (a1BaseChangeIso R E V).hom.left ≫
        (SmoothSite.productSnd ((toSmoothSite E).obj V) (SmoothSite.affineLine R)).left =
      pullback.snd V.hom (SmoothSite.a1Projection R E).left ≫
        (SmoothSite.productSnd E (SmoothSite.affineLine R)).left :=
      pullbackRightPullbackFstIso_hom_snd _ _ _
    have hU : (a1BaseChangeIso R U ((baseChange j.left).obj V)).hom.left ≫
        (SmoothSite.productSnd ((toSmoothSite U).obj ((baseChange j.left).obj V))
          (SmoothSite.affineLine R)).left =
      pullback.snd ((baseChange j.left).obj V).hom (SmoothSite.a1Projection R U).left ≫
        (SmoothSite.productSnd U (SmoothSite.affineLine R)).left :=
      pullbackRightPullbackFstIso_hom_snd _ _ _
    have hR : (SmoothSite.a1Map R ((restrictionProjection j).app V)).left ≫
        (SmoothSite.productSnd ((toSmoothSite E).obj V) (SmoothSite.affineLine R)).left =
      (SmoothSite.productSnd ((toSmoothSite U).obj ((baseChange j.left).obj V))
        (SmoothSite.affineLine R)).left := by
      simpa only [MorphismProperty.Comma.comp_left, Category.comp_id] using
        congrArg (fun f ↦ f.left)
          (SmoothSite.productMap_snd ((restrictionProjection j).app V)
            (𝟙 (SmoothSite.affineLine R)))
    have hJ : (SmoothSite.a1Map R j).left ≫
        (SmoothSite.productSnd E (SmoothSite.affineLine R)).left =
      (SmoothSite.productSnd U (SmoothSite.affineLine R)).left := by
      simpa only [MorphismProperty.Comma.comp_left, Category.comp_id] using
        congrArg (fun f ↦ f.left)
          (SmoothSite.productMap_snd j (𝟙 (SmoothSite.affineLine R)))
    have hμ : ((a1PunctureProjectionBaseChangeIso j).hom.app V).left ≫
        pullback.snd ((baseChange j.left).obj V).hom (SmoothSite.a1Projection R U).left =
      pullback.snd ((baseChange (SmoothSite.a1Projection R E).left).obj V).hom
        (SmoothSite.a1Map R j).left :=
      MorphismProperty.Over.w ((a1PunctureProjectionBaseChangeIso j).hom.app V)
    apply MorphismProperty.Over.Hom.ext
    simp only [MorphismProperty.Comma.comp_left, Category.assoc]
    rw [hR, hU, hE]
    change pullback.fst ((baseChange (SmoothSite.a1Projection R E).left).obj V).hom
        (SmoothSite.a1Map R j).left ≫
        ((baseChange (SmoothSite.a1Projection R E).left).obj V).hom ≫
        (SmoothSite.productSnd E (SmoothSite.affineLine R)).left =
      ((a1PunctureProjectionBaseChangeIso j).hom.app V).left ≫
        pullback.snd ((baseChange j.left).obj V).hom (SmoothSite.a1Projection R U).left ≫
        (SmoothSite.productSnd U (SmoothSite.affineLine R)).left
    rw [← Category.assoc, pullback.condition, Category.assoc, hJ,
      ← Category.assoc, hμ]

end Product

variable {k : Type u} [Field k] (X : SmoothSite (Spec (CommRingCat.of k)))
  {E : SmoothSite (Spec (CommRingCat.of k))} (b : E ⟶ SmoothSite.a1Cylinder (CommRingCat.of k) X)
  [Etale b.left]

local notation "b₁" => SmoothSite.contractionChartProduct (CommRingCat.of k) X b
local notation "p" => SmoothSite.a1Map (CommRingCat.of k) (SmoothSite.a1Projection (CommRingCat.of k) X)
local notation "πE" => SmoothSite.a1Projection (CommRingCat.of k) E

/-- The product chart gives the original Cartesian square in the smooth category. -/
theorem contractionChartProduct_isPullback : IsPullback b₁ πE p b :=
  IsPullback.of_map_of_faithful (SmoothSite.forgetScheme (Spec (CommRingCat.of k)))
    (SmoothSite.contractionChartProduct_isPullback (CommRingCat.of k) X b)

/-- Étale chart restriction and product pullback commute on the actual small sites. -/
def contractionChartProjectionBaseChangeIso :
    baseChange (πE).left ⋙ etalePostcompose (b₁).left ≅
      etalePostcompose b.left ⋙ baseChange (p).left :=
  NatIso.ofComponents (fun V ↦ MorphismProperty.Over.isoMk
    (puncturedNeighborhoodIso p b πE b₁
      (contractionChartProduct_isPullback X b) V)
    (puncturedNeighborhoodIso_hom_snd p b πE b₁
      (contractionChartProduct_isPullback X b) V)) (by
        intro V W f
        have hsf : ((baseChange (πE).left).map f).left ≫
            pullback.fst W.hom (πE).left =
          pullback.fst V.hom (πE).left ≫ f.left := pullback.lift_fst _ _ _
        have hss : ((baseChange (πE).left).map f).left ≫
            pullback.snd W.hom (πE).left =
          pullback.snd V.hom (πE).left := pullback.lift_snd _ _ _
        have htf : ((baseChange (p).left).map ((etalePostcompose b.left).map f)).left ≫
            pullback.fst (W.hom ≫ b.left) (p).left =
          pullback.fst (V.hom ≫ b.left) (p).left ≫ f.left := pullback.lift_fst _ _ _
        have hts : ((baseChange (p).left).map ((etalePostcompose b.left).map f)).left ≫
            pullback.snd (W.hom ≫ b.left) (p).left =
          pullback.snd (V.hom ≫ b.left) (p).left := pullback.lift_snd _ _ _
        apply MorphismProperty.Over.Hom.ext
        change ((baseChange (πE).left).map f).left ≫
            (puncturedNeighborhoodIso p b πE b₁
              (contractionChartProduct_isPullback X b) W).hom =
          (puncturedNeighborhoodIso p b πE b₁
            (contractionChartProduct_isPullback X b) V).hom ≫
            ((baseChange (p).left).map ((etalePostcompose b.left).map f)).left
        apply pullback.hom_ext
        · rw [Category.assoc, puncturedNeighborhoodIso_hom_fst, Category.assoc,
            htf, ← Category.assoc, puncturedNeighborhoodIso_hom_fst, hsf]
        · rw [Category.assoc, puncturedNeighborhoodIso_hom_snd, Category.assoc,
            hts, puncturedNeighborhoodIso_hom_snd, ← Category.assoc, hss])

/-- The comparison leaves unchanged the original base-neighborhood projection. -/
@[reassoc (attr := simp)]
theorem contractionChartProjectionBaseChangeIso_fst (V : FiniteEtaleSite E.left) :
    ((contractionChartProjectionBaseChangeIso X b).hom.app V).left ≫
        pullback.fst (V.hom ≫ b.left) (p).left = pullback.fst V.hom (πE).left :=
  puncturedNeighborhoodIso_hom_fst p b πE b₁
    (contractionChartProduct_isPullback X b) V

end Motivic.FiniteEtaleSite
