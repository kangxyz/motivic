/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Data.BoundarySections
public import Motivic.Transfers.Presheaf.Actions.Pencils.GraphBoundary
public import Motivic.Transfers.Presheaf.Actions.Pencils.CorrectionBoundary
public import Motivic.AlgebraicGeometry.Correspondences.Moving.Pencils.DiagonalSigned

/-! # The same simultaneous section data gives the graph action identity -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open Scheme.Modules Scheme.Modules.Invertible
universe u w
namespace AlgebraicGeometry.Scheme.RelativeCurvePencil
local instance {X Y : Scheme.{u}} (f : X ⟶ Y) [SmoothOfRelativeDimension 1 f] :
    Smooth f := SmoothOfRelativeDimension.smooth 1 f

variable (k : Type u) [Field k] {S X Y A B Z C D V : Scheme.{u}}
  [IsAffine S] [IsAffine Y] [IsAffine A] [IsAffine B] [IsAffine V]
  (t : S ⟶ Spec (.of k)) [Smooth t]
  (q : X ⟶ S) [IsSeparated q] [SmoothOfRelativeDimension 1 q]
  (π : C ⟶ S) [IsProper π]
  (j : Y ⟶ C) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ π)]
  (p : Y ⟶ X) [Flat p] (hq : j ≫ π = p ≫ q)
  (a : A ⟶ X) [IsOpenImmersion a]
  (α : B ⟶ Y) [Smooth α] (β : B ⟶ A) [Flat β] (h : α ≫ p = β ≫ a)
  (z : Z ⟶ X) (s : Z ⟶ Y) (hs : s ≫ p = z) (H : IsPullback s (𝟙 _) p z)
  (e : SheafOfModules.unit (pullback q (z ≫ q)).ringCatSheaf ≅
    Hom.idealModule (Hom.boundaryGraphTarget q z))
  (ha : Disjoint (Set.range a) (Set.range z)) (d : D ⟶ C)
  (hd : Disjoint (Set.range j) (Set.range d))

/-- The same constructed numerator-minus-pole acts by the identity after
its original target inclusion. -/
theorem transfer_dataOfBoundarySections_lam_comp_graph_eq_id
    (v : V ⟶ C) [IsOpenImmersion v] [SmoothOfRelativeDimension 1 (v ≫ π)]
    (hc : ∀ c : C, c ∈ Set.range v ∨ c ∈ Set.range d ∨ c ∈ Set.range (s ≫ j))
    (T : LineBundle (pullback (j ≫ π) π)) (N : LineBundle (pullback (a ≫ q) π))
    (aS : SheafOfModules.unit (pullback (j ≫ π) π).ringCatSheaf ⟶
      (tensorLineBundle _ T (dualLineBundle _ (Hom.relativeCompactificationGraphLine π j))).val)
    (bS : SheafOfModules.unit (pullback (j ≫ π) π).ringCatSheaf ⟶ T.val)
    (nS dS : SheafOfModules.unit (pullback (a ≫ q) π).ringCatSheaf ⟶ N.val)
    (hA :
      let zA := coprod.desc (Hom.infinityProductMap π j d) (Hom.graphBoundaryRestriction π j s)
      pullbackSectionMap zA aS ≫ pullbackTensorMap zA T.val
        (dualLineBundle _ (Hom.relativeCompactificationGraphLine π j)).val =
      tensorUnitSection (pullbackSectionMap zA bS)
        (Hom.relativeFullBoundaryFrame q π j p hq z s hs H e d hd).inv)
    (hN : pullbackSectionMap (psiBoundaryInclusion q π j p hq a z s hs d) nS =
      (fixedProductBoundaryFrame q π a z e ha d).hom ≫
        pullbackSectionMap (psiBoundaryInclusion q π j p hq a z s hs d) dS)
    [IsIso (pullbackSectionMap
      (coprod.desc (Hom.infinityProductMap π j d) (Hom.graphBoundaryRestriction π j s)) aS)]
    [IsIso (pullbackSectionMap
      (coprod.desc (Hom.infinityProductMap π j d) (Hom.graphBoundaryRestriction π j s)) bS)]
    [IsIso (pullbackSectionMap (psiBoundaryInclusion q π j p hq a z s hs d) nS)]
    [IsIso (pullbackSectionMap (psiBoundaryInclusion q π j p hq a z s hs d) dS)]
    (φ : B ⟶ V) (hφ : φ ≫ v = α ≫ j)
    (u : V ⟶ Y) (hu : u ≫ j = v)
    (P : PresheafWithTransfers.{w} k) (hP : P.IsA1Invariant) :
    let uSite : relativeTargetSite k t π v ⟶ lambdaSourceSite k t π j :=
      SmoothSite.homMk u (by
        change u ≫ ((j ≫ π) ≫ t) = (v ≫ π) ≫ t
        simpa only [Category.assoc] using congrArg (fun f => f ≫ π ≫ t) hu)
    PresheafWithTransfers.transfer P
      ((dataOfBoundarySections k t q π j p hq a α β h z s hs H e ha d hd
        v hc T N aS bS nS dS hA hN φ hφ).lam ≫ (Cor.graphFunctor k).map uSite) =
      PresheafWithTransfers.transfer P
        ((Cor.graphFunctor k).map (𝟙 (lambdaSourceSite k t π j))) := by
  have : IsAffine (lambdaSourceSite k t π j).left := ‹IsAffine Y›
  let qA := j ≫ π
  let iA := retainedProductInclusion qA π v
  let iY := retainedProductInclusion qA π j
  let zA := Hom.fullBoundaryProductMap π j d s
  let zI := Hom.infinityProductMap π j d
  let uSite : relativeTargetSite k t π v ⟶ lambdaSourceSite k t π j :=
    SmoothSite.homMk u (by
      change u ≫ ((j ≫ π) ≫ t) = (v ≫ π) ≫ t
      simpa only [Category.assoc] using congrArg (fun f => f ≫ π ≫ t) hu)
  let r : retainedProduct qA π v ⟶ retainedProduct qA π j :=
    pullback.lift (pullback.fst qA (v ≫ π)) (pullback.snd qA (v ≫ π) ≫ u)
      (by rw [Category.assoc, ← Category.assoc u j π, hu, pullback.condition])
  have hr : r ≫ iY = iA := by
    apply pullback.hom_ext <;>
      simp [r, iY, iA, Category.assoc, ← hu]
  have hg : pullback.snd qA (v ≫ π) ≫ uSite.left =
      r ≫ pullback.snd qA (j ≫ π) := by simp [r, uSite]
  have : IsAffine (retainedProduct qA π v) := retainedProduct_affine qA π v
  have : IsAffine (retainedProduct qA π j) := retainedProduct_affine qA π j
  have : SmoothOfRelativeDimension 1 (iA ≫ pullback.fst qA π) :=
    retainedProduct_smooth qA π v
  have : SmoothOfRelativeDimension 1 (iY ≫ pullback.fst qA π) :=
    retainedProduct_smooth qA π j
  have hcA := lambdaBoundary_retained_cover π j s d v hc
  have hcY : ∀ x : (pullback qA π : Scheme.{u}),
      x ∈ Set.range iY ∨ x ∈ Set.range zI := by
    intro x
    rcases hc ((pullback.snd qA π) x) with hx | hx | hx
    · obtain ⟨y, hy⟩ := hx
      obtain ⟨b, _, hb⟩ := Scheme.exists_preimage_of_isPullback
        (retainedProductInclusion_isPullback qA π j) (u y) x
        ((congrArg (fun f => f y) hu).trans hy)
      exact Or.inl ⟨b, hb⟩
    · right
      rw [Scheme.Pullback.range_fst]
      exact hx
    · obtain ⟨y, hy⟩ := hx
      obtain ⟨b, _, hb⟩ := Scheme.exists_preimage_of_isPullback
        (retainedProductInclusion_isPullback qA π j) (s y) x hy
      exact Or.inl ⟨b, hb⟩
  have boundaryUnit {M : (pullback qA π : Scheme.{u}).Modules}
      (x : SheafOfModules.unit (pullback qA π).ringCatSheaf ⟶ M)
      [IsIso (pullbackSectionMap zA x)] : IsIso (pullbackSectionMap zI x) := by
    have hi : IsIso (pullbackSectionMap (coprod.inl ≫ zA) x) := by
      rw [← pullbackSectionMap_comp]
      have : IsIso (pullbackSectionMap coprod.inl (pullbackSectionMap zA x)) := by
        change IsIso ((pullbackUnitIso coprod.inl).inv ≫
          (Modules.pullback coprod.inl).map (pullbackSectionMap zA x))
        infer_instance
      infer_instance
    dsimp only [zA, Hom.fullBoundaryProductMap] at hi
    rw [coprod.inl_desc] at hi
    exact hi
  have : IsIso (pullbackSectionMap zA aS) := by
    change IsIso (pullbackSectionMap
      (coprod.desc (Hom.infinityProductMap π j d) (Hom.graphBoundaryRestriction π j s)) aS)
    infer_instance
  have : IsIso (pullbackSectionMap zA bS) := by
    change IsIso (pullbackSectionMap
      (coprod.desc (Hom.infinityProductMap π j d) (Hom.graphBoundaryRestriction π j s)) bS)
    infer_instance
  have : IsIso (pullbackSectionMap zI aS) := boundaryUnit aS
  have : IsIso (pullbackSectionMap zI bS) := boundaryUnit bS
  have hbA : (iA ≫ pullback.fst qA π) ≫ ((j ≫ π) ≫ t) =
      pullback.snd qA (v ≫ π) ≫ ((v ≫ π) ≫ t) := by
    simp only [iA, retainedProductInclusion_fst]
    simpa only [qA, Category.assoc] using
      congrArg (fun f => f ≫ t) (pullback.condition (f := qA) (g := v ≫ π))
  have hbY : (iY ≫ pullback.fst qA π) ≫ ((j ≫ π) ≫ t) =
      pullback.snd qA (j ≫ π) ≫ ((j ≫ π) ≫ t) := by
    simp only [iY, retainedProductInclusion_fst]
    simpa only [qA, Category.assoc] using
      congrArg (fun f => f ≫ t) (pullback.condition (f := qA) (g := j ≫ π))
  have : IsClosedImmersion (Hom.compactificationGraph π j) := by
    dsimp only [Hom.compactificationGraph]
    infer_instance
  have hδ : pullback.diagonal qA ≫ iY = Hom.compactificationGraph π j := by
    dsimp only [iY, qA]
    apply pullback.hom_ext <;> simp [Hom.compactificationGraph]
  have hγ : Hom.compactificationGraph π j ≫ pullback.fst qA π = 𝟙 Y := by
    simp [Hom.compactificationGraph, qA]
  have hγg : pullback.diagonal qA ≫ pullback.snd qA (j ≫ π) =
      𝟙 Y := by simp [qA]
  have hi := Hom.infinity_pullbackIdealInclusion_isIso π j d hd
  have : IsIso ((Modules.pullback zI).map
      (Hom.idealInclusion (Hom.compactificationGraph π j))) := by
    have he : (Modules.pullback zI).map (Hom.idealInclusion (Hom.compactificationGraph π j)) =
        Hom.pullbackToUnit (Hom.idealInclusion (Hom.compactificationGraph π j)) zI ≫
          (pullbackUnitIso zI).inv := by
      simp only [Hom.pullbackToUnit, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [he]
    infer_instance
  have he := graphSections_infinity_eq q π j p hq z s hs H e d hd T aS bS hA
  have hgraph := PresheafWithTransfers.transfer_graphTwistedSections_sub_eq_graph
    (lambdaSourceSite k t π j) (lambdaSourceSite k t π j) zI (pullback.fst qA π) iY
    (Hom.compactificationGraph π j) (Hom.relativeCompactificationGraphLine π j).property
    (pullback.diagonal qA) hδ hγ T aS bS he hcY
    (pullback.snd qA (j ≫ π)) (𝟙 _) hγg hbY P hP
  have hcomp (L : LineBundle (pullback qA π))
      (x : SheafOfModules.unit (pullback qA π).ringCatSheaf ⟶ L.val)
      [IsIso (pullbackSectionMap zA x)] [IsIso (pullbackSectionMap zI x)] :
      Cor.boundarySection (lambdaSourceSite k t π j) (relativeTargetSite k t π v)
          zA (pullback.fst qA π) iA L hcA (pullback.snd qA (v ≫ π)) hbA x ≫
            (Cor.graphFunctor k).map uSite =
        Cor.boundarySection (lambdaSourceSite k t π j) (lambdaSourceSite k t π j)
          zI (pullback.fst qA π) iY L hcY (pullback.snd qA (j ≫ π)) hbY x := by
    have := sectionDualFunctional_pullback_map_isIso zA L x
    have := sectionDualFunctional_pullback_map_isIso zI L x
    exact Cor.boundaryFunctional_comp_graph_of_open_extension
      (lambdaSourceSite k t π j) (relativeTargetSite k t π v) (lambdaSourceSite k t π j)
      zA zI (pullback.fst qA π) iA iY r hr (dualLineBundle _ L)
      (sectionDualFunctional _ L x) hcA hcY
      (pullback.snd qA (v ≫ π)) hbA (pullback.snd qA (j ≫ π)) hbY uSite hg
  have haction : PresheafWithTransfers.transfer P
      ((Cor.boundarySection (lambdaSourceSite k t π j) (relativeTargetSite k t π v)
          zA (pullback.fst qA π) iA
          (tensorLineBundle _ T (dualLineBundle _ (Hom.relativeCompactificationGraphLine π j)))
          hcA (pullback.snd qA (v ≫ π)) hbA aS -
        Cor.boundarySection (lambdaSourceSite k t π j) (relativeTargetSite k t π v)
          zA (pullback.fst qA π) iA T hcA (pullback.snd qA (v ≫ π)) hbA bS) ≫
          (Cor.graphFunctor k).map uSite) =
      PresheafWithTransfers.transfer P
        ((Cor.graphFunctor k).map (𝟙 (lambdaSourceSite k t π j))) := by
    rw [Preadditive.sub_comp, hcomp, hcomp]
    exact hgraph
  simpa only [Cor.boundarySection, Cor.boundaryFunctional,
    _root_.AlgebraicGeometry.Scheme.SmoothSite.GraphDivisorPencil.Data.lam, dataOfBoundarySections,
    relativeSectionPencilDataOfSections, qA, iA, retainedProductInclusion_fst,
    Category.assoc] using haction

end AlgebraicGeometry.Scheme.RelativeCurvePencil
