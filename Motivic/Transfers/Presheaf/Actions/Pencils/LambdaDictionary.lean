/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Data.BoundarySections
public import Motivic.Transfers.Presheaf.StaticBoundaryPencilAction
public import Motivic.AlgebraicGeometry.Correspondences.Spans.FiniteFlat.Graph
public import Motivic.AlgebraicGeometry.Correspondences.Moving.Pencils.DiagonalSigned

/-! # The original section-data lambda and its actual target postcomposition

The constructor's literal zero schemes are retained. Right graph composition
is computed by finite-flat spans, without a transfer-action or cycle-equality
hypothesis and without changing the numerator or pole sections.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurvePencil
/-- The smoothness instance used in this module. -/
local instance lambdaDictionarySmooth
    {X Y : Scheme.{u}} (f : X ⟶ Y) [SmoothOfRelativeDimension 1 f] :
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

/-- Target postcomposition of the original constructed lambda is exactly the
same numerator-minus-pole boundary correspondence with the composed target map. -/
theorem dataOfBoundarySections_lam_comp_graph
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
    (Q : SmoothSite (Spec (.of k))) (u : relativeTargetSite k t π v ⟶ Q) :
    let qA := j ≫ π
    let iA := retainedProductInclusion qA π v
    let zA := coprod.desc (Hom.infinityProductMap π j d) (Hom.graphBoundaryRestriction π j s)
    let : IsAffine (lambdaSourceSite k t π j).left := ‹IsAffine Y›
    let : IsAffine (retainedProduct qA π v) := retainedProduct_affine qA π v
    let : SmoothOfRelativeDimension 1 (iA ≫ pullback.fst qA π) :=
      retainedProduct_smooth qA π v
    let hcA := lambdaBoundary_retained_cover π j s d v hc
    let g := pullback.snd qA (v ≫ π) ≫ u.left
    let hb : (iA ≫ pullback.fst qA π) ≫ (lambdaSourceSite k t π j).hom = g ≫ Q.hom := by
      change (iA ≫ pullback.fst qA π) ≫ (qA ≫ t) =
        (pullback.snd qA (v ≫ π) ≫ u.left) ≫ Q.hom
      have hu : u.left ≫ Q.hom = (v ≫ π) ≫ t := u.w
      rw [Category.assoc (pullback.snd qA (v ≫ π)) u.left Q.hom, hu]
      rw [retainedProductInclusion_fst]
      simpa only [Category.assoc] using
        congrArg (fun f => f ≫ t) (pullback.condition (f := qA) (g := v ≫ π))
    (dataOfBoundarySections k t q π j p hq a α β h z s hs H e ha d hd
      v hc T N aS bS nS dS hA hN φ hφ).lam ≫ (Cor.graphFunctor k).map u =
      Cor.boundarySection (lambdaSourceSite k t π j) Q zA (pullback.fst qA π) iA
        (tensorLineBundle _ T (dualLineBundle _ (Hom.relativeCompactificationGraphLine π j)))
        hcA g hb aS -
      Cor.boundarySection (lambdaSourceSite k t π j) Q zA (pullback.fst qA π) iA
        T hcA g hb bS := by
  dsimp only
  simp only [_root_.AlgebraicGeometry.Scheme.SmoothSite.GraphDivisorPencil.Data.lam,
      dataOfBoundarySections,
    relativeSectionPencilDataOfSections, Cor.boundarySection, Cor.boundaryFunctional,
    Preadditive.sub_comp, Cor.ofFiniteFlatSpan_comp_graph,
    retainedProductInclusion_fst, Category.assoc]

/-- Target postcomposition retains the original correction sign, pole minus
numerator, and both whole zero schemes from the same constructor. -/
theorem dataOfBoundarySections_psi_comp_graph
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
    (Q : SmoothSite (Spec (.of k))) (u : relativeTargetSite k t π v ⟶ Q) :
    let qN := a ≫ q
    let iN := retainedProductInclusion qN π v
    let zN := psiBoundaryInclusion q π j p hq a z s hs d
    let : IsAffine (psiSourceSite k t q a).left := ‹IsAffine A›
    let : IsAffine (retainedProduct qN π v) := retainedProduct_affine qN π v
    let : SmoothOfRelativeDimension 1 (iN ≫ pullback.fst qN π) :=
      retainedProduct_smooth qN π v
    let hcN := psiBoundary_retained_cover q π j p hq a z s hs d v hc
    let g := pullback.snd qN (v ≫ π) ≫ u.left
    let hb : (iN ≫ pullback.fst qN π) ≫ (psiSourceSite k t q a).hom = g ≫ Q.hom := by
      change (iN ≫ pullback.fst qN π) ≫ (qN ≫ t) =
        (pullback.snd qN (v ≫ π) ≫ u.left) ≫ Q.hom
      have hu : u.left ≫ Q.hom = (v ≫ π) ≫ t := u.w
      rw [Category.assoc (pullback.snd qN (v ≫ π)) u.left Q.hom, hu]
      rw [retainedProductInclusion_fst]
      simpa only [Category.assoc] using
        congrArg (fun f => f ≫ t) (pullback.condition (f := qN) (g := v ≫ π))
    (dataOfBoundarySections k t q π j p hq a α β h z s hs H e ha d hd
      v hc T N aS bS nS dS hA hN φ hφ).psi ≫ (Cor.graphFunctor k).map u =
      Cor.boundarySection (psiSourceSite k t q a) Q zN (pullback.fst qN π) iN
        N hcN g hb dS -
      Cor.boundarySection (psiSourceSite k t q a) Q zN (pullback.fst qN π) iN
        N hcN g hb nS := by
  dsimp only
  simp only [_root_.AlgebraicGeometry.Scheme.SmoothSite.GraphDivisorPencil.Data.psi,
      dataOfBoundarySections,
    relativeSectionPencilDataOfSections, Cor.boundarySection, Cor.boundaryFunctional,
    Preadditive.sub_comp, Cor.ofFiniteFlatSpan_comp_graph,
    retainedProductInclusion_fst, Category.assoc]

end AlgebraicGeometry.Scheme.RelativeCurvePencil
