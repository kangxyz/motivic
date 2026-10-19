/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Frames.RelativeCurve.FullBoundaryCoordinate
public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.DualBoundaryNaturality

/-! # A full ideal frame coherent with the existing chosen divisor frame

The canonical infinity ideal frame and the same supplied marked ideal frame
are glued before section choices. Naturality of duality and coproduct
restriction faithfulness identify its dual with the EXISTING full-boundary
divisor frame. No canonical graph section is cancelled at its zero locus.


Intended upstream module:
`Aglib.AlgebraicGeometry.RelativeCurve.Boundary.Frames.CoherentIdealFrame`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.Frames.CoherentIdealCoordinate`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.Hom
private theorem coprod_ideal_dual_eq {A B P : Scheme.{u}}
    (a : A ⟶ P) (b : B ⟶ P) (L : LineBundle P)
    (eA : SheafOfModules.unit A.ringCatSheaf ≅ (Modules.pullback a).obj L.val)
    (eB : SheafOfModules.unit B.ringCatSheaf ≅ (Modules.pullback b).obj L.val)
    (F : (Modules.pullback (coprod.desc a b)).obj (dualLineBundle P L).val ≅
      SheafOfModules.unit (A ⨿ B).ringCatSheaf)
    (hA : (Modules.restrictFunctor (coprod.inl : A ⟶ A ⨿ B)).map F.hom ≫
      (restrictUnitIso _).hom = (coprodPullbackRestrictLeft a b).hom.app
        (dualLineBundle P L).val ≫ (dualBoundaryTrivialization a L eA).hom)
    (hB : (Modules.restrictFunctor (coprod.inr : B ⟶ A ⨿ B)).map F.hom ≫
      (restrictUnitIso _).hom = (coprodPullbackRestrictRight a b).hom.app
        (dualLineBundle P L).val ≫ (dualBoundaryTrivialization b L eB).hom) :
    dualBoundaryTrivialization (coprod.desc a b) L
      (Classical.choose (exists_coprod_pullback_unitIso a b L.val eA.symm eB.symm)).symm = F := by
  let E := Classical.choose (exists_coprod_pullback_unitIso a b L.val eA.symm eB.symm)
  have hE := Classical.choose_spec (exists_coprod_pullback_unitIso a b L.val eA.symm eB.symm)
  apply Iso.ext
  apply hom_ext_coprod_restrict A B
  · apply (cancel_mono (restrictUnitIso (coprod.inl : A ⟶ A ⨿ B)).hom).mp
    have hn := dualBoundaryTrivialization_restrict_of_inv
      (coprod.inl : A ⟶ A ⨿ B) (coprod.desc a b) a (coprod.inl_desc a b) L E.symm eA
      (by simpa only [coprodPullbackRestrictLeft, Iso.trans_hom,
            NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
            Iso.symm_inv, Iso.symm_hom, Category.assoc] using hE.1)
    have hn' : (Modules.restrictFunctor (coprod.inl : A ⟶ A ⨿ B)).map
        (dualBoundaryTrivialization (coprod.desc a b) L E.symm).hom ≫
          (restrictUnitIso _).hom = (coprodPullbackRestrictLeft a b).hom.app
            (dualLineBundle P L).val ≫ (dualBoundaryTrivialization a L eA).hom := by
      simpa only [coprodPullbackRestrictLeft, Iso.trans_hom, NatTrans.comp_app,
        Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Category.assoc] using hn
    exact hn'.trans hA.symm
  · apply (cancel_mono (restrictUnitIso (coprod.inr : B ⟶ A ⨿ B)).hom).mp
    have hn := dualBoundaryTrivialization_restrict_of_inv
      (coprod.inr : B ⟶ A ⨿ B) (coprod.desc a b) b (coprod.inr_desc a b) L E.symm eB
      (by simpa only [coprodPullbackRestrictRight, Iso.trans_hom,
            NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
            Iso.symm_inv, Iso.symm_hom, Category.assoc] using hE.2)
    have hn' : (Modules.restrictFunctor (coprod.inr : B ⟶ A ⨿ B)).map
        (dualBoundaryTrivialization (coprod.desc a b) L E.symm).hom ≫
          (restrictUnitIso _).hom = (coprodPullbackRestrictRight a b).hom.app
            (dualLineBundle P L).val ≫ (dualBoundaryTrivialization b L eB).hom := by
      simpa only [coprodPullbackRestrictRight, Iso.trans_hom, NatTrans.comp_app,
        Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Category.assoc] using hn
    exact hn'.trans hB.symm

variable {S X Y Z C D : Scheme.{u}} (q : X ⟶ S) [IsSeparated q]
  [SmoothOfRelativeDimension 1 q] (qC : C ⟶ S) [IsSeparated qC]
  (j : Y ⟶ C) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ qC)]
  (p : Y ⟶ X) [Flat p] (hq : j ≫ qC = p ≫ q)
  (z : Z ⟶ X) (s : Z ⟶ Y) (h : s ≫ p = z) (H : IsPullback s (𝟙 _) p z)
  (e : SheafOfModules.unit (pullback q (z ≫ q)).ringCatSheaf ≅
    idealModule (boundaryGraphTarget q z))
  (d : D ⟶ C) (hd : Disjoint (Set.range j) (Set.range d))

/-- The actual ideal-side whole-boundary frame, using the unchanged component frames. -/
def relativeFullBoundaryIdealFrame := Classical.choose
  (exists_coprod_pullback_unitIso (infinityProductMap qC j d) (graphBoundaryRestriction qC j s)
    (idealModule (compactificationGraph qC j))
    (infinityBoundaryIdealIso qC j d hd).symm
    (relativeCompactificationBoundaryFrame q qC j p hq z s h H e).symm)

/-- The glued ideal frame dualizes to the already chosen full divisor frame,
not merely to a frame with an equal canonical section coordinate. -/
theorem relativeFullBoundaryIdealFrame_dual_eq :
    dualBoundaryTrivialization
      (coprod.desc (infinityProductMap qC j d) (graphBoundaryRestriction qC j s))
      (relativeCompactificationGraphLine qC j)
      (relativeFullBoundaryIdealFrame q qC j p hq z s h H e d hd).symm =
    relativeFullBoundaryFrame q qC j p hq z s h H e d hd := by
  have hF := Classical.choose_spec
    (exists_relativeFullBoundaryDivisorFrame q qC j p hq z s h H e d hd)
  apply coprod_ideal_dual_eq (infinityProductMap qC j d) (graphBoundaryRestriction qC j s)
    (relativeCompactificationGraphLine qC j) (infinityBoundaryIdealIso qC j d hd)
    (relativeCompactificationBoundaryFrame q qC j p hq z s h H e)
  · simpa only [relativeFullBoundaryFrame, infinityBoundaryDivisorIso,
      relativeCompactificationGraphLine] using hF.1
  · exact hF.2

end AlgebraicGeometry.Scheme.Hom
