/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Data.BoundarySections
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Correction.InfinityEquality
public import Motivic.Transfers.Presheaf.Actions.Pencils.CorrectionBoundary
public import Motivic.AlgebraicGeometry.Correspondences.Moving.Pencils.DiagonalSigned

/-! # The same simultaneous section data gives the correcting action identity -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open Scheme.Modules Scheme.Modules.Invertible
universe u w
namespace AlgebraicGeometry.Scheme.RelativeCurvePencil
/-- The smoothness instance used in this module. -/
local instance correctionSmooth {X Y : Scheme.{u}} (f : X ⟶ Y) [SmoothOfRelativeDimension 1 f] :
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

/-- The same constructed correction acts by zero after its original target inclusion. -/
theorem transfer_dataOfBoundarySections_psi_comp_graph_eq_zero
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
        v hc T N aS bS nS dS hA hN φ hφ).psi ≫ (Cor.graphFunctor k).map uSite) = 0 := by
  have : IsAffine (psiSourceSite k t q a).left := ‹IsAffine A›
  let qN := a ≫ q
  let iN := retainedProductInclusion qN π v
  let iY := retainedProductInclusion qN π j
  let zN := psiBoundaryInclusion q π j p hq a z s hs d
  let zI := pullback.fst (pullback.snd qN π) d
  let uSite : relativeTargetSite k t π v ⟶ lambdaSourceSite k t π j :=
    SmoothSite.homMk u (by
      change u ≫ ((j ≫ π) ≫ t) = (v ≫ π) ≫ t
      simpa only [Category.assoc] using congrArg (fun f => f ≫ π ≫ t) hu)
  let r : retainedProduct qN π v ⟶ retainedProduct qN π j :=
    pullback.lift (pullback.fst qN (v ≫ π)) (pullback.snd qN (v ≫ π) ≫ u)
      (by rw [Category.assoc, ← Category.assoc u j π, hu, pullback.condition])
  have hr : r ≫ iY = iN := by
    apply pullback.hom_ext <;>
      simp [r, iY, iN, Category.assoc, ← hu]
  have hg : pullback.snd qN (v ≫ π) ≫ uSite.left =
      r ≫ pullback.snd qN (j ≫ π) := by simp [r, uSite]
  have : IsAffine (retainedProduct qN π v) := retainedProduct_affine qN π v
  have : IsAffine (retainedProduct qN π j) := retainedProduct_affine qN π j
  have : SmoothOfRelativeDimension 1 (iN ≫ pullback.fst qN π) :=
    retainedProduct_smooth qN π v
  have : SmoothOfRelativeDimension 1 (iY ≫ pullback.fst qN π) :=
    retainedProduct_smooth qN π j
  have hcN := psiBoundary_retained_cover q π j p hq a z s hs d v hc
  have hcY : ∀ x : (pullback qN π : Scheme.{u}),
      x ∈ Set.range iY ∨ x ∈ Set.range zI := by
    intro x
    rcases hc ((pullback.snd qN π) x) with hx | hx | hx
    · obtain ⟨y, hy⟩ := hx
      obtain ⟨b, _, hb⟩ := Scheme.exists_preimage_of_isPullback
        (retainedProductInclusion_isPullback qN π j) (u y) x
        ((congrArg (fun f => f y) hu).trans hy)
      exact Or.inl ⟨b, hb⟩
    · right
      rw [Scheme.Pullback.range_fst]
      exact hx
    · obtain ⟨y, hy⟩ := hx
      obtain ⟨b, _, hb⟩ := Scheme.exists_preimage_of_isPullback
        (retainedProductInclusion_isPullback qN π j) (s y) x hy
      exact Or.inl ⟨b, hb⟩
  have hni : IsIso (pullbackSectionMap zI nS) := by
    have hi : IsIso (pullbackSectionMap (coprod.inl ≫ zN) nS) := by
      rw [← pullbackSectionMap_comp]
      have : IsIso (pullbackSectionMap coprod.inl (pullbackSectionMap zN nS)) := by
        change IsIso ((pullbackUnitIso coprod.inl).inv ≫
          (Modules.pullback coprod.inl).map (pullbackSectionMap zN nS))
        infer_instance
      infer_instance
    dsimp only [zN, psiBoundaryInclusion] at hi
    rw [coprod.inl_desc] at hi
    exact hi
  have hdi : IsIso (pullbackSectionMap zI dS) := by
    have hi : IsIso (pullbackSectionMap (coprod.inl ≫ zN) dS) := by
      rw [← pullbackSectionMap_comp]
      have : IsIso (pullbackSectionMap coprod.inl (pullbackSectionMap zN dS)) := by
        change IsIso ((pullbackUnitIso coprod.inl).inv ≫
          (Modules.pullback coprod.inl).map (pullbackSectionMap zN dS))
        infer_instance
      infer_instance
    dsimp only [zN, psiBoundaryInclusion] at hi
    rw [coprod.inl_desc] at hi
    exact hi
  have hn := correctionSections_infinity_eq q π j p hq a z s hs e ha d N nS dS hN
  have hbN : (iN ≫ pullback.fst qN π) ≫ ((a ≫ q) ≫ t) =
      pullback.snd qN (v ≫ π) ≫ ((v ≫ π) ≫ t) := by
    simp only [iN, retainedProductInclusion_fst]
    simpa only [qN, Category.assoc] using
      congrArg (fun f => f ≫ t) (pullback.condition (f := qN) (g := v ≫ π))
  have hbY : (iY ≫ pullback.fst qN π) ≫ ((a ≫ q) ≫ t) =
      pullback.snd qN (j ≫ π) ≫ ((j ≫ π) ≫ t) := by
    simp only [iY, retainedProductInclusion_fst]
    simpa only [qN, Category.assoc] using
      congrArg (fun f => f ≫ t) (pullback.condition (f := qN) (g := j ≫ π))
  have hzero := PresheafWithTransfers.transfer_correctionSections_comp_graph_eq_zero
    (psiSourceSite k t q a) (relativeTargetSite k t π v) (lambdaSourceSite k t π j)
    zN zI (pullback.fst qN π) iN iY r hr hcN hcY
    (pullback.snd qN (v ≫ π)) hbN (pullback.snd qN (j ≫ π)) hbY
    uSite hg P hP N nS dS hn
  simpa only [ Cor.boundarySection, Cor.boundaryFunctional,
    _root_.AlgebraicGeometry.Scheme.SmoothSite.GraphDivisorPencil.Data.psi, dataOfBoundarySections,
    relativeSectionPencilDataOfSections, qN, iN, retainedProductInclusion_fst,
    Category.assoc] using hzero

end AlgebraicGeometry.Scheme.RelativeCurvePencil
