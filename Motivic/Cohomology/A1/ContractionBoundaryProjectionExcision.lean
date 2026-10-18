/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.ContractionBoundaryProjectionSupport
public import Motivic.Cohomology.A1.BoundaryEtaleExcision
public import Motivic.Cohomology.A1.ContractionBoundaryProjectionExcisionGeometry
public import Motivic.AlgebraicGeometry.Sites.FiniteEtalePointCokernelLifting

/-! # Product projection on the original ambient cokernel of an étale chart

The map is the restriction of the actual cylinder projection map through
genuine étale excision. The quotient equation retains the original punctured
representatives. No closed-support identification on a later local quotient
lift is required.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Motivic.FiniteEtaleSite

section Product

variable {k : Type u} [Field k] {U E : SmoothSite (Spec (CommRingCat.of k))} (j : U ⟶ E)

/-- The direct images in the literal puncture/product square commute. -/
def a1PunctureProjectionDirectImageIso :
    directImage (SmoothSite.a1Projection (CommRingCat.of k) U).left ⋙ directImage j.left ≅
      directImage (SmoothSite.a1Map (CommRingCat.of k) j).left ⋙
        directImage (SmoothSite.a1Projection (CommRingCat.of k) E).left := by
  have := Functor.isContinuous_comp (baseChange j.left)
    (baseChange (SmoothSite.a1Projection (CommRingCat.of k) U).left)
    (nisnevichTopology E.left) (nisnevichTopology U.left)
    (nisnevichTopology (SmoothSite.a1Cylinder (CommRingCat.of k) U).left)
  have := Functor.isContinuous_comp (baseChange (SmoothSite.a1Projection (CommRingCat.of k) E).left)
    (baseChange (SmoothSite.a1Map (CommRingCat.of k) j).left)
    (nisnevichTopology E.left) (nisnevichTopology (SmoothSite.a1Cylinder (CommRingCat.of k) E).left)
    (nisnevichTopology (SmoothSite.a1Cylinder (CommRingCat.of k) U).left)
  exact Functor.sheafPushforwardContinuousIso
    (a1PunctureProjectionBaseChangeIso j).symm AddCommGrpCat.{u + 1}
    (nisnevichTopology E.left) (nisnevichTopology (SmoothSite.a1Cylinder (CommRingCat.of k) U).left)

variable (G : Sheaf (SmoothSite.nisnevichTopology (Spec (CommRingCat.of k))) AddCommGrpCat.{u + 1})

/-- Pullback of original punctured sections along the actual homotopy projection. -/
def a1PuncturedProjectionMap :
    (directImage j.left).obj ((restrict U AddCommGrpCat).obj G) ⟶
      (directImage (SmoothSite.a1Projection (CommRingCat.of k) E).left).obj
        ((directImage (SmoothSite.a1Map (CommRingCat.of k) j).left).obj
          ((restrict (SmoothSite.a1Cylinder (CommRingCat.of k) U) AddCommGrpCat).obj G)) :=
  (directImage j.left).map
    (restrictionToDirectImage G (SmoothSite.a1Projection (CommRingCat.of k) U)) ≫
    (a1PunctureProjectionDirectImageIso j).hom.app
      ((restrict (SmoothSite.a1Cylinder (CommRingCat.of k) U) AddCommGrpCat).obj G)

/-- The actual product pullback preserves the original ambient restriction relation. -/
theorem a1PuncturedProjectionMap_restriction :
    restrictionToDirectImage G j ≫ a1PuncturedProjectionMap j G =
      restrictionToDirectImage G (SmoothSite.a1Projection (CommRingCat.of k) E) ≫
        (directImage (SmoothSite.a1Projection (CommRingCat.of k) E).left).map
          (restrictionToDirectImage G (SmoothSite.a1Map (CommRingCat.of k) j)) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  change (G).obj.map ((restrictionProjection j).app V.unop).op ≫
      ((G).obj.map ((restrictionProjection (SmoothSite.a1Projection (CommRingCat.of k) U)).app
        ((baseChange j.left).obj V.unop)).op ≫
        (G).obj.map ((toSmoothSite (SmoothSite.a1Cylinder (CommRingCat.of k) U)).map
          ((a1PunctureProjectionBaseChangeIso j).hom.app V.unop)).op) =
    (G).obj.map
      ((restrictionProjection (SmoothSite.a1Projection (CommRingCat.of k) E)).app V.unop).op ≫
      (G).obj.map ((restrictionProjection (SmoothSite.a1Map (CommRingCat.of k) j)).app
        ((baseChange (SmoothSite.a1Projection (CommRingCat.of k) E).left).obj V.unop)).op
  simp only [← Functor.map_comp, ← op_comp]
  congr 2
  apply MorphismProperty.Over.Hom.ext
  change ((a1PunctureProjectionBaseChangeIso j).hom.app V.unop).left ≫
      pullback.fst (pullback.snd V.unop.hom j.left)
        (SmoothSite.a1Projection (CommRingCat.of k) U).left ≫
      pullback.fst V.unop.hom j.left =
    pullback.fst (pullback.snd V.unop.hom (SmoothSite.a1Projection (CommRingCat.of k) E).left)
        (SmoothSite.a1Map (CommRingCat.of k) j).left ≫
      pullback.fst V.unop.hom (SmoothSite.a1Projection (CommRingCat.of k) E).left
  exact a1PunctureProjectionBaseChangeIso_fst j V.unop

/-- The actual ambient cokernel projection pullback for an original puncture.
This is the coefficient map needed by the ordinary localization sequence. -/
def a1AmbientProjectionMap :
    boundaryAmbientCokernel G j ⟶
      (directImage (SmoothSite.a1Projection (CommRingCat.of k) E).left).obj
        (boundaryAmbientCokernel G (SmoothSite.a1Map (CommRingCat.of k) j)) :=
  cokernel.desc (restrictionToDirectImage G j)
    (a1PuncturedProjectionMap j G ≫
      (directImage (SmoothSite.a1Projection (CommRingCat.of k) E).left).map
        (cokernel.π (restrictionToDirectImage G (SmoothSite.a1Map (CommRingCat.of k) j)))) (by
          rw [← Category.assoc, a1PuncturedProjectionMap_restriction, Category.assoc,
            ← Functor.map_comp, cokernel.condition, Functor.map_zero, comp_zero])

/-- The actual product map sends each unchanged punctured generator through
the original target cokernel projection. -/
@[reassoc (attr := simp)]
theorem a1AmbientProjectionMap_π :
    cokernel.π (restrictionToDirectImage G j) ≫ a1AmbientProjectionMap j G =
      a1PuncturedProjectionMap j G ≫
        (directImage (SmoothSite.a1Projection (CommRingCat.of k) E).left).map
          (cokernel.π (restrictionToDirectImage G (SmoothSite.a1Map (CommRingCat.of k) j))) :=
  cokernel.π_desc _ _ _

/-- Once the original split-chart product equality has been established, the
native cokernel epimorphism lifts it after a genuine pointed base refinement.
The original marking point, quotient and product restriction remain unchanged.
No support-unit assertion is made on the refined ambient neighborhood. -/
theorem exists_pointed_a1_product_quotient_lift
    (Φ : (nisnevichTopology E.left).Point.{u + 1})
    (V : FiniteEtaleSite E.left) (v : Φ.fiber.obj V)
    (c₀ : (boundaryAmbientCokernel G j).obj.obj (op V))
    (c₁ : (boundaryAmbientCokernel G (SmoothSite.a1Map (CommRingCat.of k) j)).obj.obj
      (op ((baseChange (SmoothSite.a1Projection (CommRingCat.of k) E).left).obj V)))
    (hc : (a1AmbientProjectionMap j G).hom.app
      (op V) c₀ = c₁) :
    ∃ (W : FiniteEtaleSite E.left) (a : W ⟶ V) (w : Φ.fiber.obj W)
      (t : ((directImage j.left).obj ((restrict U AddCommGrpCat).obj G)).obj.obj (op W)),
      Φ.fiber.map a w = v ∧
      (cokernel.π (restrictionToDirectImage G (SmoothSite.a1Map (CommRingCat.of k) j))).hom.app
          (op ((baseChange (SmoothSite.a1Projection (CommRingCat.of k) E).left).obj W))
          ((a1PuncturedProjectionMap j G).hom.app
            (op W) t) =
        (boundaryAmbientCokernel G (SmoothSite.a1Map (CommRingCat.of k) j)).obj.map
          ((baseChange (SmoothSite.a1Projection (CommRingCat.of k) E).left).map a).op c₁ := by
  let r := restrictionToDirectImage G j
  have hzero : cokernel.π (cokernel.π r) = 0 :=
    (isZero_cokernel_of_epi (cokernel.π r)).eq_of_tgt _ _
  obtain ⟨W, a, w, t, ha, ht⟩ := exists_pointed_local_lift_of_cokernel_germ_zero
    Φ (cokernel.π r) V v c₀ (by simp [hzero])
  refine ⟨W, a, w, t, ha, ?_⟩
  have hπ := ConcreteCategory.congr_hom
    (congrArg (fun f ↦ f.hom.app (op W))
      (a1AmbientProjectionMap_π j G)) t
  change (a1AmbientProjectionMap j G).hom.app
      (op W) ((cokernel.π r).hom.app (op W) t) = _ at hπ
  rw [ht] at hπ
  have hn := ConcreteCategory.congr_hom
    ((a1AmbientProjectionMap j G).hom.naturality a.op) c₀
  change (a1AmbientProjectionMap j G).hom.app
      (op W) ((boundaryAmbientCokernel G j).obj.map a.op c₀) =
    (boundaryAmbientCokernel G (SmoothSite.a1Map (CommRingCat.of k) j)).obj.map
      ((baseChange (SmoothSite.a1Projection (CommRingCat.of k) E).left).map a).op
      ((a1AmbientProjectionMap j G).hom.app
        (op V) c₀) at hn
  rw [hc] at hn
  exact hπ.symm.trans hn

end Product

variable {k : Type u} [Field k] (X : SmoothSite (Spec (CommRingCat.of k)))
  {E : SmoothSite (Spec (CommRingCat.of k))} (b : E ⟶ SmoothSite.a1Cylinder (CommRingCat.of k) X)
  [Etale b.left]

local notation "X₁" => SmoothSite.a1Cylinder (CommRingCat.of k) X
local notation "b₁" => SmoothSite.contractionChartProduct (CommRingCat.of k) X b
local notation "p" =>
  SmoothSite.a1Map (CommRingCat.of k) (SmoothSite.a1Projection (CommRingCat.of k) X)
local notation "πE" => SmoothSite.a1Projection (CommRingCat.of k) E
local notation "j₀" => SmoothSite.contractionOpen (CommRingCat.of k) X
local notation "j₁" => SmoothSite.contractionOpen (CommRingCat.of k) X₁

/-- Restriction to the actual étale chart commutes with the original product
direct image, via the displayed Cartesian neighborhood comparison. -/
def contractionChartProjectionDirectImageIso :
    directImage (p).left ⋙ etaleRestriction b.left ≅
      etaleRestriction (b₁).left ⋙ directImage (πE).left := by
  have := Functor.isContinuous_comp (etalePostcompose b.left) (baseChange (p).left)
    (nisnevichTopology E.left) (nisnevichTopology (X₁).left)
    (nisnevichTopology (SmoothSite.a1Cylinder (CommRingCat.of k) X₁).left)
  have := Functor.isContinuous_comp (baseChange (πE).left) (etalePostcompose (b₁).left)
    (nisnevichTopology E.left) (nisnevichTopology (SmoothSite.a1Cylinder (CommRingCat.of k) E).left)
    (nisnevichTopology (SmoothSite.a1Cylinder (CommRingCat.of k) X₁).left)
  exact Functor.sheafPushforwardContinuousIso
    (contractionChartProjectionBaseChangeIso X b).symm AddCommGrpCat.{u + 1}
    (nisnevichTopology E.left)
    (nisnevichTopology (SmoothSite.a1Cylinder (CommRingCat.of k) X₁).left)

variable (F : SheafWithTransfers.{u + 1} k)
  {U U₁ : SmoothSite (Spec (CommRingCat.of k))}
  (j : U ⟶ E) (q : U ⟶ SmoothSite.torusCylinder (CommRingCat.of k) X)
  (hpb : IsPullback q j (SmoothSite.contractionOpen (CommRingCat.of k) X) b)
  (j' : U₁ ⟶ SmoothSite.a1Cylinder (CommRingCat.of k) E)
  (q' : U₁ ⟶ SmoothSite.torusCylinder (CommRingCat.of k)
    (SmoothSite.a1Cylinder (CommRingCat.of k) X))
  (hpb' : IsPullback q' j'
    (SmoothSite.contractionOpen (CommRingCat.of k) (SmoothSite.a1Cylinder (CommRingCat.of k) X))
    (SmoothSite.contractionChartProduct (CommRingCat.of k) X b))

local notation "G" => Functor.obj (SheafWithTransfers.toSheaf k) F
local notation "C₀" => boundaryAmbientCokernel G j₀
local notation "C₁" => boundaryAmbientCokernel G j₁

/-- The punctured projection on a chosen chart, retaining both actual étale
Cartesian identifications. The target chart may be supplied by the literal
product square, without choosing a second normal coordinate. -/
def contractionChartPuncturedProjectionMap :
    (directImage j.left).obj ((restrict U AddCommGrpCat).obj G) ⟶
      (directImage (πE).left).obj
        ((directImage j'.left).obj ((restrict U₁ AddCommGrpCat).obj G)) :=
  (etalePuncturedCoefficientIso G j₀ b j q hpb).inv ≫
    (etaleRestriction b.left).map (contractionPuncturedProjectionMap X F) ≫
    (contractionChartProjectionDirectImageIso X b).hom.app
      ((directImage (j₁).left).obj
        ((restrict (SmoothSite.torusCylinder (CommRingCat.of k) X₁) AddCommGrpCat).obj G)) ≫
    (directImage (πE).left).map (etalePuncturedCoefficientIso G j₁ b₁ j' q' hpb').hom

/-- The ambient projection is transported through actual étale cokernel
excision, not through an assumed smooth coefficient inverse-image comparison. -/
def contractionChartAmbientProjectionMap :
    boundaryAmbientCokernel G j ⟶
      (directImage (πE).left).obj (boundaryAmbientCokernel G j') :=
  (boundaryAmbientEtaleIso G j₀ b j q hpb).inv ≫
    (etaleRestriction b.left).map (contractionAmbientProjectionMap X F) ≫
    (contractionChartProjectionDirectImageIso X b).hom.app C₁ ≫
    (directImage (πE).left).map (boundaryAmbientEtaleIso G j₁ b₁ j' q' hpb').hom

/-- The transported map preserves the unchanged quotient projections. This
equation is the one subsequently restricted after a local quotient lift. -/
@[reassoc]
theorem contractionChartAmbientProjectionMap_π :
    cokernel.π (restrictionToDirectImage G j) ≫
        contractionChartAmbientProjectionMap X b F j q hpb j' q' hpb' =
      contractionChartPuncturedProjectionMap X b F j q hpb j' q' hpb' ≫
        (directImage (πE).left).map (cokernel.π (restrictionToDirectImage G j')) := by
  have hπ : cokernel.π (restrictionToDirectImage G j) ≫
      (boundaryAmbientEtaleIso G j₀ b j q hpb).inv =
    (etalePuncturedCoefficientIso G j₀ b j q hpb).inv ≫
      (etaleRestriction b.left).map (cokernel.π (restrictionToDirectImage G j₀)) := by
    apply (cancel_mono (boundaryAmbientEtaleIso G j₀ b j q hpb).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
      boundaryAmbientEtaleIso_π, Iso.inv_hom_id_assoc]
  simp only [contractionChartAmbientProjectionMap,
    contractionChartPuncturedProjectionMap, ← Category.assoc]
  rw [hπ]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc, contractionAmbientProjectionMap_π,
    Functor.map_comp_assoc]
  erw [(contractionChartProjectionDirectImageIso X b).hom.naturality_assoc
    (cokernel.π (restrictionToDirectImage G
      (SmoothSite.contractionOpen (CommRingCat.of k) X₁)))]
  simp only [Functor.comp_map]
  rw [← Functor.map_comp, boundaryAmbientEtaleIso_π, Functor.map_comp]

/-- The chart-transported punctured map is the literal product pullback, not
merely an isomorphic map with the same source and target. -/
theorem contractionChartPuncturedProjectionMap_eq_a1 [IsOpenImmersion j.left] :
    contractionChartPuncturedProjectionMap X b F j q hpb
        (SmoothSite.a1Map (CommRingCat.of k) j)
        (SmoothSite.contractionChartPunctureProduct (CommRingCat.of k) X q)
        (SmoothSite.contractionChartPunctureProduct_isPullback (CommRingCat.of k) X b j q hpb) =
      a1PuncturedProjectionMap j G := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  let V₀ := (etalePostcompose b.left).obj V.unop
  let V₁ := (baseChange (πE).left).obj V.unop
  let r := (restrictionProjection
    (SmoothSite.productMap (SmoothSite.a1Projection (CommRingCat.of k) X)
      (𝟙 (SmoothSite.torus (CommRingCat.of k))))).app ((baseChange (j₀).left).obj V₀)
  let ν := (contractionPunctureProjectionBaseChangeIso X).hom.app V₀
  let ν' := (toSmoothSite (SmoothSite.torusCylinder (CommRingCat.of k) X₁)).map ν
  let ρ := (contractionChartProjectionBaseChangeIso X b).hom.app V.unop
  let ρ' := (toSmoothSite (SmoothSite.torusCylinder (CommRingCat.of k) X₁)).map
    ((baseChange (j₁).left).map ρ)
  let e₀ := (etalePuncturedToSmoothIso j₀ b j q hpb).app V.unop
  let e₁ := (etalePuncturedToSmoothIso j₁ b₁ (SmoothSite.a1Map (CommRingCat.of k) j)
    (SmoothSite.contractionChartPunctureProduct (CommRingCat.of k) X q)
    (SmoothSite.contractionChartPunctureProduct_isPullback (CommRingCat.of k) X b j q hpb)).app V₁
  let μ := (a1PunctureProjectionBaseChangeIso j).hom.app V.unop
  let μ' := (toSmoothSite (SmoothSite.a1Cylinder (CommRingCat.of k) U)).map μ
  change (G).obj.map e₀.inv.op ≫ ((G).obj.map r.op ≫ (G).obj.map ν'.op) ≫
      (G).obj.map ρ'.op ≫ (G).obj.map e₁.hom.op =
    (G).obj.map ((restrictionProjection (SmoothSite.a1Projection (CommRingCat.of k) U)).app
      ((baseChange j.left).obj V.unop)).op ≫ (G).obj.map μ'.op
  simp only [← Functor.map_comp, ← op_comp]
  congr 2
  have : Mono ((restrictionProjection j).app V.unop) :=
    (SmoothSite.forgetScheme (Spec (CommRingCat.of k))).mono_of_mono_map
      (inferInstanceAs (Mono (pullback.fst V.unop.hom j.left)))
  apply (cancel_mono ((restrictionProjection j).app V.unop)).mp
  apply MorphismProperty.Over.Hom.ext
  have he₀ : e₀.inv.left ≫ pullback.fst V.unop.hom j.left =
      pullback.fst (V.unop.hom ≫ b.left) (j₀).left := by
    exact (Iso.inv_comp_eq
      (puncturedNeighborhoodIso j₀ b j q hpb V.unop)).mpr
      (puncturedNeighborhoodIso_hom_fst j₀ b j q hpb V.unop).symm
  simp only [MorphismProperty.Comma.comp_left, Category.assoc]
  change e₁.hom.left ≫ ((baseChange (j₁).left).map ρ).left ≫ ν.left ≫
      pullback.fst (pullback.snd V₀.hom (j₀).left)
        (SmoothSite.productMap (SmoothSite.a1Projection (CommRingCat.of k) X)
          (𝟙 (SmoothSite.torus (CommRingCat.of k)))).left ≫
        e₀.inv.left ≫ pullback.fst V.unop.hom j.left =
    μ.left ≫ pullback.fst (pullback.snd V.unop.hom j.left)
      (SmoothSite.a1Projection (CommRingCat.of k) U).left ≫ pullback.fst V.unop.hom j.left
  rw [he₀]
  change e₁.hom.left ≫ ((baseChange (j₁).left).map ρ).left ≫ ν.left ≫
      pullback.fst (pullback.snd V₀.hom (j₀).left)
        (SmoothSite.productMap (SmoothSite.a1Projection (CommRingCat.of k) X)
          (𝟙 (SmoothSite.torus (CommRingCat.of k)))).left ≫
        pullback.fst V₀.hom (j₀).left =
    μ.left ≫ pullback.fst (pullback.snd V.unop.hom j.left)
      (SmoothSite.a1Projection (CommRingCat.of k) U).left ≫ pullback.fst V.unop.hom j.left
  have hμ : μ.left ≫ pullback.fst (pullback.snd V.unop.hom j.left)
      (SmoothSite.a1Projection (CommRingCat.of k) U).left ≫ pullback.fst V.unop.hom j.left =
      pullback.fst (pullback.snd V.unop.hom (πE).left)
          (SmoothSite.a1Map (CommRingCat.of k) j).left ≫
        pullback.fst V.unop.hom (πE).left :=
    a1PunctureProjectionBaseChangeIso_fst j V.unop
  rw [hμ, contractionPunctureProjectionBaseChangeIso_fst]
  have hmap : ((baseChange (j₁).left).map ρ).left ≫
      pullback.fst ((baseChange (p).left).obj V₀).hom (j₁).left =
    pullback.fst ((etalePostcompose (b₁).left).obj V₁).hom (j₁).left ≫ ρ.left :=
    pullback.lift_fst _ _ _
  change e₁.hom.left ≫ ((baseChange (j₁).left).map ρ).left ≫
      pullback.fst ((baseChange (p).left).obj V₀).hom (j₁).left ≫
      pullback.fst V₀.hom (p).left =
    pullback.fst V₁.hom (SmoothSite.a1Map (CommRingCat.of k) j).left ≫
      pullback.fst V.unop.hom (πE).left
  have hρ : ρ.left ≫ pullback.fst V₀.hom (p).left =
      pullback.fst V.unop.hom (πE).left :=
    contractionChartProjectionBaseChangeIso_fst X b V.unop
  rw [← Category.assoc ((baseChange (j₁).left).map ρ).left, hmap, Category.assoc]
  erw [hρ]
  exact puncturedNeighborhoodIso_hom_fst_assoc j₁ b₁ (SmoothSite.a1Map (CommRingCat.of k) j)
    (SmoothSite.contractionChartPunctureProduct (CommRingCat.of k) X q)
    (SmoothSite.contractionChartPunctureProduct_isPullback (CommRingCat.of k) X b j q hpb)
    V₁ _

/-- The transported ambient comparison is exactly the original quotient-induced
product pullback used by the localization sequence. -/
theorem contractionChartAmbientProjectionMap_eq_a1 [IsOpenImmersion j.left] :
    contractionChartAmbientProjectionMap X b F j q hpb
        (SmoothSite.a1Map (CommRingCat.of k) j)
        (SmoothSite.contractionChartPunctureProduct (CommRingCat.of k) X q)
        (SmoothSite.contractionChartPunctureProduct_isPullback (CommRingCat.of k) X b j q hpb) =
      a1AmbientProjectionMap j G := by
  apply (cancel_epi (cokernel.π (restrictionToDirectImage G j))).mp
  rw [contractionChartAmbientProjectionMap_π,
    contractionChartPuncturedProjectionMap_eq_a1, a1AmbientProjectionMap_π]

include b q hpb in
/-- On the original étale chart, the actual quotient-induced product map is
invertible. Support is used only on the literal cylinder model; the chart
transport consists entirely of the specified actual étale comparisons. -/
theorem a1AmbientProjectionMap_isIso_of_chart [IsOpenImmersion j.left]
    (hF : F.obj.IsA1Invariant)
    (hE₀ : Epi (contractionToBoundary X F hF))
    (hE₁ : Epi (contractionToBoundary X₁ F hF)) :
    IsIso (a1AmbientProjectionMap j G) := by
  let := contractionAmbientProjection_isIso X F hF hE₀ hE₁
  have h : IsIso (contractionChartAmbientProjectionMap X b F j q hpb
      (SmoothSite.a1Map (CommRingCat.of k) j)
      (SmoothSite.contractionChartPunctureProduct (CommRingCat.of k) X q)
      (SmoothSite.contractionChartPunctureProduct_isPullback
        (CommRingCat.of k) X b j q hpb)) := by
    dsimp only [contractionChartAmbientProjectionMap]
    infer_instance
  rwa [contractionChartAmbientProjectionMap_eq_a1] at h

include b q hpb in
/-- Every original product-boundary section has a genuine pointed local
punctured lift after a base refinement. The global antecedent is obtained
first, on the original chart; no support or retraction assertion is used on
the subsequently refined ambient object. The canonical Epi inputs are explicit. -/
theorem exists_pointed_a1_product_quotient_lift_of_chart [IsOpenImmersion j.left]
    (hF : F.obj.IsA1Invariant)
    (hE₀ : Epi (contractionToBoundary X F hF))
    (hE₁ : Epi (contractionToBoundary X₁ F hF))
    (Φ : (nisnevichTopology E.left).Point.{u + 1})
    (V : FiniteEtaleSite E.left) (v : Φ.fiber.obj V)
    (c₁ : (boundaryAmbientCokernel G (SmoothSite.a1Map (CommRingCat.of k) j)).obj.obj
      (op ((baseChange (SmoothSite.a1Projection (CommRingCat.of k) E).left).obj V))) :
    ∃ (W : FiniteEtaleSite E.left) (a : W ⟶ V) (w : Φ.fiber.obj W)
      (t : ((directImage j.left).obj ((restrict U AddCommGrpCat).obj G)).obj.obj (op W)),
      Φ.fiber.map a w = v ∧
      (cokernel.π (restrictionToDirectImage G (SmoothSite.a1Map (CommRingCat.of k) j))).hom.app
          (op ((baseChange (SmoothSite.a1Projection (CommRingCat.of k) E).left).obj W))
          ((a1PuncturedProjectionMap j G).hom.app (op W) t) =
        (boundaryAmbientCokernel G (SmoothSite.a1Map (CommRingCat.of k) j)).obj.map
          ((baseChange (SmoothSite.a1Projection (CommRingCat.of k) E).left).map a).op c₁ := by
  let α := a1AmbientProjectionMap j G
  let : IsIso α := a1AmbientProjectionMap_isIso_of_chart X b F j q hpb hF hE₀ hE₁
  let c₀ := (inv α).hom.app (op V) c₁
  have hc : α.hom.app (op V) c₀ = c₁ :=
    ConcreteCategory.congr_hom
      (congrArg (fun f ↦ f.hom.app (op V)) (IsIso.inv_hom_id α)) c₁
  exact exists_pointed_a1_product_quotient_lift j G Φ V v c₀ c₁ hc

end Motivic.FiniteEtaleSite
