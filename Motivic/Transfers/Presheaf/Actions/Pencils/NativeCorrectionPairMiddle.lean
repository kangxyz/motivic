/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.Presheaf.StaticBoundaryPencilAction
public import Motivic.AlgebraicGeometry.Correspondences.Coproducts.Binary
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Data.BoundarySectionData
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Correction.OriginalCorrectionActionGeometry
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Charts.Basic
public import Motivic.Aglib.Data.Fin.TwoCases

/-! # The actual middle correspondence for the original correction pair

This leaf extracts only the existing marked-product theorem's
left-hand expression. It does not invoke that theorem or construct a norm,
germ, normalized unit, or transfer action. Every native bridge below specializes to the
original finite-pair geometry, the same source data, and the same target pair.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Scheme Scheme.Modules Scheme.Modules.Invertible Scheme.Hom Scheme.RelativeCurvePencil
open AlgebraicGeometry.FiniteSchemeNormBaseChange RelativeProjectiveLine
open _root_.AlgebraicGeometry.Scheme (SmoothSite)
universe u
namespace Motivic.Cor

/-- The smoothness instance used in this module. -/
local instance nativeCorrectionPairMiddleSmooth
    {X Y : Scheme.{u}} (f : X ⟶ Y) [SmoothOfRelativeDimension 1 f] :
    Smooth f := SmoothOfRelativeDimension.smooth 1 f

/-- The existing marked-product theorem's left-hand expression, with no norm
or desired correspondence relation as an input. Its actual specialization below
is the single shared middle correspondence. -/
def originalPairMarkedMiddle
    {k : Type u} [Field k]
    (X Z : SmoothSite (Spec (.of k)))
    (O : Fin 2 → SmoothSite (Spec (.of k))) [∀ i, IsAffine (O i).left]
    (α : ∀ i, X ⟶ O i)
    (C₀ U₁ B₁ : Fin 2 → Scheme.{u})
    (q₀ : ∀ i, C₀ i ⟶ (O i).left) [∀ i, IsProper (q₀ i)]
    (i₁ : ∀ i, B₁ i ⟶ C₀ i) (j₁ : ∀ i, U₁ i ⟶ C₀ i)
    [∀ i, IsOpenImmersion (j₁ i)] [∀ i, (U₁ i).IsQuasiAffine]
    [∀ i, SmoothOfRelativeDimension 1 (j₁ i ≫ q₀ i)]
    (γ : (O 0).left ⟶ C₀ 0)
    (hI : IsLocallyRankOne (C₀ 0) (idealModule γ))
    (M : LineBundle (C₀ 0))
    (aS : SheafOfModules.unit (C₀ 0).ringCatSheaf ⟶
      (tensorLineBundle (C₀ 0) M
        (dualLineBundle (C₀ 0) ⟨idealModule γ, hI⟩)).val)
    (bS : SheafOfModules.unit (C₀ 0).ringCatSheaf ⟶ M.val)
    (N : LineBundle (C₀ 1))
    (nS dS : N.val ⟶ SheafOfModules.unit (C₀ 1).ringCatSheaf)
    (hc₁ : ∀ i (x : C₀ i), x ∈ Set.range (j₁ i) ∨ x ∈ Set.range (i₁ i))
    [IsIso (pullbackSectionMap (i₁ 0) aS)]
    [IsIso (pullbackSectionMap (i₁ 0) bS)]
    [IsIso ((Modules.pullback (i₁ 1)).map nS)]
    [IsIso ((Modules.pullback (i₁ 1)).map dS)]
    (g₁ : ∀ i, U₁ i ⟶ Z.left)
    (hb₁ : ∀ i, (j₁ i ≫ q₀ i) ≫ (O i).hom = g₁ i ≫ Z.hom)
    (r : X ⟶ Z) : Cor.mk X ⟶ Cor.mk Z :=
  let I : LineBundle (C₀ 0) := ⟨idealModule γ, hI⟩
  let A := tensorLineBundle (C₀ 0) M (dualLineBundle (C₀ 0) I)
  let target : Cor.mk X ⟶ Cor.mk Z :=
    ((Cor.graphFunctor k).map (α 0) : Cor.mk X ⟶ Cor.mk (O 0)) ≫
      (Cor.boundarySection (O 0) Z (i₁ 0) (q₀ 0) (j₁ 0) A
          (hc₁ 0) (g₁ 0) (hb₁ 0) aS -
        Cor.boundarySection (O 0) Z (i₁ 0) (q₀ 0) (j₁ 0) M
          (hc₁ 0) (g₁ 0) (hb₁ 0) bS)
  let correction : Cor.mk X ⟶ Cor.mk Z :=
    ((Cor.graphFunctor k).map (α 1) : Cor.mk X ⟶ Cor.mk (O 1)) ≫
      (Cor.boundaryFunctional (O 1) Z (i₁ 1) (q₀ 1) (j₁ 1) N dS
          (hc₁ 1) (g₁ 1) (hb₁ 1) -
        Cor.boundaryFunctional (O 1) Z (i₁ 1) (q₀ 1) (j₁ 1) N nS
          (hc₁ 1) (g₁ 1) (hb₁ 1))
  let graph : Cor.mk X ⟶ Cor.mk Z := (Cor.graphFunctor k).map r
  target - correction - graph

/-- Assemble the same two branch identifications using only correspondence algebra. -/
private theorem nativeCorrection_branch_assembly
    {k : Type u} [Field k] {A X Z : Cor k}
    (g : A ⟶ X) (e : A ⟶ A) (r : A ⟶ Z)
    {T T' : X ⟶ Z} {S S' : A ⟶ Z}
    (he : e = 𝟙 A) (ht : T = T') (hs : S = S') :
    g ≫ T' - S' - r = g ≫ T - (e ≫ S) - r := by
  have htarget : g ≫ T = g ≫ T' := congrArg (fun h : X ⟶ Z => g ≫ h) ht
  have hsource : e ≫ S = S' :=
    ((congrArg (fun h : A ⟶ A => h ≫ S) he).trans (Category.id_comp S)).trans hs
  exact (congrArg (fun h : A ⟶ Z => h - r)
    (congrArg₂ (fun h l : A ⟶ Z => h - l) htarget hsource)).symm

variable (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R]

variable {Y A Z C D V WA : Scheme.{u}} [IsAffine Y] [IsAffine A] [IsAffine V]
  [SmoothOfRelativeDimension 1 (boundaryLineProjection R)] [SmoothOfRelativeDimension 1 ((chart R
    0) ≫ (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))))]
  (f : C ⟶ (ProjectiveSpace R (ULift.{u} (Fin 2)))) [IsFinite f] (j : Y ⟶ C) [IsOpenImmersion j]
  [SmoothOfRelativeDimension 1 (j ≫ (f ≫ (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))))]
  (p : Y ⟶ (Spec (CommRingCat.of (Polynomial R)))) [Flat p] (hq : j ≫ (f ≫
    (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))) = p ≫ (boundaryLineProjection R))
  (hret : j ≫ f = p ≫ (chart R 0))
  (a : A ⟶ (Spec (CommRingCat.of (Polynomial R)))) [IsOpenImmersion a]
  (z : Z ⟶ (Spec (CommRingCat.of (Polynomial R)))) [IsClosedImmersion (z ≫ (chart R 0))]
  (s : Z ⟶ Y) (hs : s ≫ p = z) (H : IsPullback s (𝟙 Z) p z)
  (hsK : (s ≫ j) ≫ f = z ≫ (chart R 0))
  (e : SheafOfModules.unit (pullback (boundaryLineProjection R) (z ≫ (boundaryLineProjection
    R))).ringCatSheaf ≅
    Hom.idealModule (Hom.boundaryGraphTarget (boundaryLineProjection R) z))
  (ha : Disjoint (Set.range a) (Set.range z))
  (d : D ⟶ C) (hd : Disjoint (Set.range j) (Set.range d))
  (c : BoundarySectionData (boundaryLineProjection R) (f ≫ (ProjectiveSpace.toSpec R (ULift.{u}
    (Fin 2)))) j p hq a z s hs H e ha d hd)
  (v : V ⟶ C) [IsOpenImmersion v] [SmoothOfRelativeDimension 1 (v ≫ (f ≫ (ProjectiveSpace.toSpec
    R (ULift.{u} (Fin 2)))))]
  (hcover : ∀ x : C, x ∈ Set.range v ∨ x ∈ Set.range d ∨ x ∈ Set.range (s ≫ j))
  {DA : Scheme.{u}} (dA : DA ⟶ (ProjectiveSpace R (ULift.{u} (Fin 2)))) [IsAffineHom dA]
  (hdA : Disjoint (Set.range (chart R 0)) (Set.range dA))
  (bI : pullback f dA ⟶ D) (hbI : bI ≫ d = pullback.fst f dA)
  (bE : (Scheme.residualMarkedFiberOpen f j (z ≫ (chart R 0)) s hsK).toScheme ⟶ D)
  (hbE : bE ≫ d = Scheme.residualMarkedFiberMap f j (z ≫ (chart R 0)) s hsK)
  (LA : LineBundle (pullback ((chart R 0) ≫ (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))))
    (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))))
  (aA : SheafOfModules.unit (pullback ((chart R 0) ≫ (ProjectiveSpace.toSpec R (ULift.{u} (Fin
    2)))) (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))).ringCatSheaf ⟶
    (tensorLineBundle _ LA (dualLineBundle _ (Hom.relativeCompactificationGraphLine
      (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) (chart R 0)))).val)
  (bA : SheafOfModules.unit (pullback ((chart R 0) ≫ (ProjectiveSpace.toSpec R (ULift.{u} (Fin
    2)))) (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))).ringCatSheaf ⟶ LA.val)
  (iA : WA ⟶ pullback ((chart R 0) ≫ (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))))
    (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))) [IsOpenImmersion iA]
  (hFa : CoherentGraph.SectionDivisorFiniteFlat (pullback.fst ((chart R 0) ≫
    (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))) (ProjectiveSpace.toSpec R (ULift.{u} (Fin
    2)))) iA
    (tensorLineBundle _ LA (dualLineBundle _ (Hom.relativeCompactificationGraphLine
      (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) (chart R 0)))) aA)
  (hFb : CoherentGraph.SectionDivisorFiniteFlat (pullback.fst ((chart R 0) ≫
    (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))) (ProjectiveSpace.toSpec R (ULift.{u} (Fin
    2)))) iA LA bA)
  (hpairA :
    let zA := coprod.desc (Hom.infinityProductMap (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))
      (chart R 0) dA) (Hom.graphBoundaryRestriction (ProjectiveSpace.toSpec R (ULift.{u} (Fin
      2))) (chart R 0) z)
    pullbackSectionMap zA aA ≫ pullbackTensorMap zA LA.val
      (dualLineBundle _ (Hom.relativeCompactificationGraphLine (ProjectiveSpace.toSpec R
        (ULift.{u} (Fin 2))) (chart R 0))).val =
    tensorUnitSection (pullbackSectionMap zA bA)
      (Hom.relativeFullBoundaryFrame (boundaryLineProjection R) (ProjectiveSpace.toSpec R
        (ULift.{u} (Fin 2))) (chart R 0) (𝟙 (Spec (CommRingCat.of (Polynomial R))))
        ((chart_toSpec R 0).trans (Category.id_comp (boundaryLineProjection R)).symm)
        z z (Category.comp_id z) (IsPullback.id_vert z) e dA hdA).inv)
  [haA : IsIso (pullbackSectionMap
    (coprod.desc (Hom.infinityProductMap (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) (chart R
      0) dA) (Hom.graphBoundaryRestriction (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) (chart
      R 0) z)) aA)]

variable [hbAUnit : IsIso (pullbackSectionMap
    (fullBoundaryProductMap (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))
      (chart R 0) dA z) bA)]
  {k : Type u} [instK : Field k] (t : Spec (.of R) ⟶ Spec (.of k)) [Smooth t]
  {U : Scheme.{u}} [IsAffine U]
  (u : U ⟶ Spec (.of (Polynomial R))) [IsOpenImmersion u]
  [SmoothOfRelativeDimension 1
    ((u ≫ chart R 0) ≫ ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))]
  (vY : V ⟶ Y) (hvY : vY ≫ j = v) (pV : V ⟶ U) (hpV : pV ≫ u = vY ≫ p)
  (rA : A ⟶ U) (hrA : rA ≫ u = a)
  (hinfty : (Set.range (chart R 0))ᶜ ⊆ Set.range dA)
  (hpuncture : (Set.range u)ᶜ ⊆ Set.range z)

omit [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R]
  [IsAffine Y] [IsOpenImmersion j]
  [SmoothOfRelativeDimension 1
    (j ≫ (f ≫ ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))))]
  [Flat p] [IsClosedImmersion (z ≫ chart R 0)] [IsAffineHom dA] in
/-- The actual finite-pair target branch is the original target section pair. -/
private theorem nativeCorrection_target_branch :
    let π := ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))
    let q := boundaryLineProjection R
    let jA := chart R 0
    let X₀ := lambdaSourceSite k t π jA
    let Q := relativeTargetSite k t π (u ≫ jA)
    let : IsAffine X₀.left := inferInstanceAs (IsAffine (Spec (.of (Polynomial R))))
    let : IsAffine (retainedProduct (jA ≫ π) π (u ≫ jA)) :=
      retainedProduct_affine (jA ≫ π) π (u ≫ jA)
    let : SmoothOfRelativeDimension 1
        (retainedProductInclusion (jA ≫ π) π (u ≫ jA) ≫ pullback.fst (jA ≫ π) π) :=
      retainedProduct_smooth (jA ≫ π) π (u ≫ jA)
    let O := originalCorrectionPairSite t q π jA a
    let C₀ := originalCorrectionPairCompact q π f jA a
    let U₁ := originalCorrectionPairSmallRetained q π f jA a u v
    let i₁ := originalCorrectionPairFullBoundaryInclusion q π f j jA p a d dA z s hq hs
    let j₁ := originalCorrectionPairSmallInclusion q π f jA a u v
    let q₀ : ∀ i, C₀ i ⟶ (O i).left := originalCorrectionPairProjection q π f jA a
    let g₁ : ∀ i, U₁ i ⟶ Q.left := originalCorrectionPairSmallTargetMap q π f jA a u v pV
    let hc₁ := originalCorrectionPair_fullBoundary_cover q π f j jA p a d dA z s hq hs
      u v hinfty hpuncture hcover
    let hb₁ : ∀ i, (j₁ i ≫ q₀ i) ≫ (O i).hom = g₁ i ≫ Q.hom :=
      Fin.twoCases (retainedProduct_structure (jA ≫ π) π (u ≫ jA) t)
        (retainedProduct_structure_factor (a ≫ q) (f ≫ π) v t pV Q.hom
          (correctionSmallTarget_structure t π f j jA p hret u v vY hvY pV hpV))
    let γ := compactificationGraph π jA
    let hI : IsLocallyRankOne (C₀ 0) (idealModule γ) :=
      (relativeCompactificationGraphLine π jA).property
    let MC : LineBundle (C₀ 0) := LA
    let MA := tensorLineBundle (C₀ 0) MC (dualLineBundle (C₀ 0) ⟨idealModule γ, hI⟩)
    let M := tensorLineBundle _ LA (dualLineBundle _ (relativeCompactificationGraphLine π jA))
    let aSC : SheafOfModules.unit (C₀ 0).ringCatSheaf ⟶ MA.val := aA
    let bSC : SheafOfModules.unit (C₀ 0).ringCatSheaf ⟶ MC.val := bA
    let : IsIso (pullbackSectionMap (i₁ 0) aSC) := haA
    let : IsIso (pullbackSectionMap (i₁ 0) bSC) := hbAUnit
    let : IsIso (pullbackSectionMap (fullBoundaryProductMap π jA dA z) aA) := haA
    let hcA := lambdaBoundary_retained_cover π jA z dA (u ≫ jA)
      (correction_target_small_cover jA dA z u hinfty hpuncture)
    let hbA := retainedProduct_structure (jA ≫ π) π (u ≫ jA) t
    (show Cor.mk X₀ ⟶ Cor.mk Q from
      Cor.boundarySection (O 0) Q (i₁ 0) (q₀ 0) (j₁ 0) MA
          (hc₁ 0) (g₁ 0) (hb₁ 0) aSC -
        Cor.boundarySection (O 0) Q (i₁ 0) (q₀ 0) (j₁ 0) MC
          (hc₁ 0) (g₁ 0) (hb₁ 0) bSC) =
      (Cor.boundarySection X₀ Q (fullBoundaryProductMap π jA dA z)
          (pullback.fst (jA ≫ π) π) (retainedProductInclusion (jA ≫ π) π (u ≫ jA)) M
          hcA (pullback.snd (jA ≫ π) ((u ≫ jA) ≫ π)) hbA aA -
        Cor.boundarySection X₀ Q (fullBoundaryProductMap π jA dA z)
          (pullback.fst (jA ≫ π) π) (retainedProductInclusion (jA ≫ π) π (u ≫ jA)) LA
          hcA (pullback.snd (jA ≫ π) ((u ≫ jA) ≫ π)) hbA bA) := by
  dsimp only
  rfl

omit [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R]
  [IsAffine Y] [IsClosedImmersion (z ≫ chart R 0)] [IsAffineHom dA] haA hbAUnit in
/-- The actual finite-pair source functionals are the original correction sections. -/
private theorem nativeCorrection_source_branch :
    let π := ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))
    let q := boundaryLineProjection R
    let jA := chart R 0
    let A₀ := psiSourceSite k t q a
    let Q := relativeTargetSite k t π (u ≫ jA)
    let : IsAffine A₀.left := ‹IsAffine A›
    let : IsAffine (retainedProduct (a ≫ q) (f ≫ π) v) :=
      retainedProduct_affine (a ≫ q) (f ≫ π) v
    let : SmoothOfRelativeDimension 1
        (retainedProductInclusion (a ≫ q) (f ≫ π) v ≫
          pullback.fst (a ≫ q) (f ≫ π)) :=
      retainedProduct_smooth (a ≫ q) (f ≫ π) v
    let O := originalCorrectionPairSite t q π jA a
    let C₀ := originalCorrectionPairCompact q π f jA a
    let U₁ := originalCorrectionPairSmallRetained q π f jA a u v
    let i₁ := originalCorrectionPairFullBoundaryInclusion q π f j jA p a d dA z s hq hs
    let j₁ := originalCorrectionPairSmallInclusion q π f jA a u v
    let q₀ : ∀ i, C₀ i ⟶ (O i).left := originalCorrectionPairProjection q π f jA a
    let g₁ : ∀ i, U₁ i ⟶ Q.left := originalCorrectionPairSmallTargetMap q π f jA a u v pV
    let hc₁ := originalCorrectionPair_fullBoundary_cover q π f j jA p a d dA z s hq hs
      u v hinfty hpuncture hcover
    let hb₁ : ∀ i, (j₁ i ≫ q₀ i) ≫ (O i).hom = g₁ i ≫ Q.hom :=
      Fin.twoCases (retainedProduct_structure (jA ≫ π) π (u ≫ jA) t)
        (retainedProduct_structure_factor (a ≫ q) (f ≫ π) v t pV Q.hom
          (correctionSmallTarget_structure t π f j jA p hret u v vY hvY pV hpV))
    let nφ := sectionDualFunctional _ c.N c.nS
    let dφ := sectionDualFunctional _ c.N c.dS
    let NC : LineBundle (C₀ 1) := dualLineBundle _ c.N
    let nSC : NC.val ⟶ SheafOfModules.unit (C₀ 1).ringCatSheaf := nφ
    let dSC : NC.val ⟶ SheafOfModules.unit (C₀ 1).ringCatSheaf := dφ
    let := c.n_unit
    let := c.d_unit
    let : IsIso (pullbackSectionMap (i₁ 1) c.nS) := c.n_unit
    let : IsIso (pullbackSectionMap (i₁ 1) c.dS) := c.d_unit
    let : IsIso ((Modules.pullback (i₁ 1)).map nSC) :=
      sectionDualFunctional_pullback_map_isIso (i₁ 1) c.N c.nS
    let : IsIso ((Modules.pullback (i₁ 1)).map dSC) :=
      sectionDualFunctional_pullback_map_isIso (i₁ 1) c.N c.dS
    let hcN := psiBoundary_retained_cover q (f ≫ π) j p hq a z s hs d v hcover
    let hbN := retainedProduct_structure_factor (a ≫ q) (f ≫ π) v t pV Q.hom
      (correctionSmallTarget_structure t π f j jA p hret u v vY hvY pV hpV)
    (show Cor.mk A₀ ⟶ Cor.mk Q from
      Cor.boundaryFunctional (O 1) Q (i₁ 1) (q₀ 1) (j₁ 1) NC dSC
          (hc₁ 1) (g₁ 1) (hb₁ 1) -
        Cor.boundaryFunctional (O 1) Q (i₁ 1) (q₀ 1) (j₁ 1) NC nSC
          (hc₁ 1) (g₁ 1) (hb₁ 1)) =
      (Cor.boundarySection A₀ Q (psiBoundaryInclusion q (f ≫ π) j p hq a z s hs d)
          (pullback.fst (a ≫ q) (f ≫ π)) (retainedProductInclusion (a ≫ q) (f ≫ π) v)
          c.N hcN (pullback.snd (a ≫ q) (v ≫ (f ≫ π)) ≫ pV) hbN c.dS -
        Cor.boundarySection A₀ Q (psiBoundaryInclusion q (f ≫ π) j p hq a z s hs d)
          (pullback.fst (a ≫ q) (f ≫ π)) (retainedProductInclusion (a ≫ q) (f ≫ π) v)
          c.N hcN (pullback.snd (a ≫ q) (v ≫ (f ≫ π)) ≫ pV) hbN c.nS) := by
  dsimp only
  rfl

omit [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R]
  [IsAffine Y] [IsClosedImmersion (z ≫ chart R 0)] [IsAffineHom dA] in
/-- Canonicalize the exact original finite-pair left-hand side, without norm data. -/
theorem nativeCorrection_canonical_to_middle :
    let π := ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))
    let q := boundaryLineProjection R
    let jA := chart R 0
    let X₀ := lambdaSourceSite k t π jA
    let A₀ := psiSourceSite k t q a
    let Q := relativeTargetSite k t π (u ≫ jA)
    let jAret := retainedProductInclusion (jA ≫ π) π (u ≫ jA)
    let jNret := retainedProductInclusion (a ≫ q) (f ≫ π) v
    let M := tensorLineBundle _ LA (dualLineBundle _ (relativeCompactificationGraphLine π jA))
    let : IsIso (pullbackSectionMap (fullBoundaryProductMap π jA dA z) aA) := haA
    let := c.n_unit
    let := c.d_unit
    let : IsAffine X₀.left := inferInstanceAs (IsAffine (Spec (.of (Polynomial R))))
    let : IsAffine A₀.left := ‹IsAffine A›
    let : IsAffine (retainedProduct (jA ≫ π) π (u ≫ jA)) :=
      retainedProduct_affine (jA ≫ π) π (u ≫ jA)
    let : IsAffine (retainedProduct (a ≫ q) (f ≫ π) v) :=
      retainedProduct_affine (a ≫ q) (f ≫ π) v
    let : SmoothOfRelativeDimension 1 (jAret ≫ pullback.fst (jA ≫ π) π) :=
      retainedProduct_smooth (jA ≫ π) π (u ≫ jA)
    let : SmoothOfRelativeDimension 1 (jNret ≫ pullback.fst (a ≫ q) (f ≫ π)) :=
      retainedProduct_smooth (a ≫ q) (f ≫ π) v
    let hcA := lambdaBoundary_retained_cover π jA z dA (u ≫ jA)
      (correction_target_small_cover jA dA z u hinfty hpuncture)
    let hcN := psiBoundary_retained_cover q (f ≫ π) j p hq a z s hs d v hcover
    let hbA := retainedProduct_structure (jA ≫ π) π (u ≫ jA) t
    let hbN := retainedProduct_structure_factor (a ≫ q) (f ≫ π) v t pV Q.hom
      (correctionSmallTarget_structure t π f j jA p hret u v vY hvY pV hpV)
    let O := originalCorrectionPairSite t q π jA a
    let α := originalCorrectionPairSiteMap t q π jA (chart_toSpec R 0) a
    let C₀ := originalCorrectionPairCompact q π f jA a
    let U₁ := originalCorrectionPairSmallRetained q π f jA a u v
    let i₁ := originalCorrectionPairFullBoundaryInclusion q π f j jA p a d dA z s hq hs
    let j₁ := originalCorrectionPairSmallInclusion q π f jA a u v
    let q₀ : ∀ i, C₀ i ⟶ (O i).left := originalCorrectionPairProjection q π f jA a
    let g₁ : ∀ i, U₁ i ⟶ Q.left := originalCorrectionPairSmallTargetMap q π f jA a u v pV
    let hc₁ := originalCorrectionPair_fullBoundary_cover q π f j jA p a d dA z s hq hs
      u v hinfty hpuncture hcover
    let hb₁ : ∀ i, (j₁ i ≫ q₀ i) ≫ (O i).hom = g₁ i ≫ Q.hom := by
      intro i
      fin_cases i
      · exact retainedProduct_structure (jA ≫ π) π (u ≫ jA) t
      · exact retainedProduct_structure_factor (a ≫ q) (f ≫ π) v t pV Q.hom
          (correctionSmallTarget_structure t π f j jA p hret u v vY hvY pV hpV)
    let B₁ := originalCorrectionPairFullBoundary q π f jA a d dA z
    let γ := compactificationGraph π jA
    let hI : IsLocallyRankOne (C₀ 0) (idealModule γ) :=
      (relativeCompactificationGraphLine π jA).property
    let MC : LineBundle (C₀ 0) := LA
    let MA := tensorLineBundle (C₀ 0) MC (dualLineBundle (C₀ 0) ⟨idealModule γ, hI⟩)
    let aSC : SheafOfModules.unit (C₀ 0).ringCatSheaf ⟶ MA.val := aA
    let bSC : SheafOfModules.unit (C₀ 0).ringCatSheaf ⟶ MC.val := bA
    let : IsIso (pullbackSectionMap (i₁ 0) aSC) := haA
    let : IsIso (pullbackSectionMap (i₁ 0) bSC) := hbAUnit
    let nφ := sectionDualFunctional _ c.N c.nS
    let dφ := sectionDualFunctional _ c.N c.dS
    let NC : LineBundle (C₀ 1) := dualLineBundle _ c.N
    let nSC : NC.val ⟶ SheafOfModules.unit (C₀ 1).ringCatSheaf := nφ
    let dSC : NC.val ⟶ SheafOfModules.unit (C₀ 1).ringCatSheaf := dφ
    let : IsIso (pullbackSectionMap (i₁ 1) c.nS) := c.n_unit
    let : IsIso (pullbackSectionMap (i₁ 1) c.dS) := c.d_unit
    let : IsIso ((Modules.pullback (i₁ 1)).map nSC) :=
      sectionDualFunctional_pullback_map_isIso (i₁ 1) c.N c.nS
    let : IsIso ((Modules.pullback (i₁ 1)).map dSC) :=
      sectionDualFunctional_pullback_map_isIso (i₁ 1) c.N c.dS
    let rsite := correctionSmallParameterMap t q π jA (chart_toSpec R 0) a u rA hrA
    let haSmall : IsIso (pullbackSectionMap (i₁ 0) aSC) := haA
    let hbSmall : IsIso (pullbackSectionMap (i₁ 0) bSC) := hbAUnit
    let Ω : Cor.mk A₀ ⟶ Cor.mk Q :=
      @originalPairMarkedMiddle k inferInstance A₀ Q O (fun _ => inferInstance) α
      C₀ U₁ B₁ q₀ (fun _ => inferInstance) i₁ j₁
      (fun _ => inferInstance) (fun _ => inferInstance) (fun _ => inferInstance)
      γ hI MC aSC bSC NC nSC dSC hc₁ haSmall hbSmall
      inferInstance inferInstance g₁ hb₁ rsite
    ((show Cor.mk A₀ ⟶ Cor.mk X₀ from (Cor.graphFunctor k).map
        (originalCorrectionPairSiteMap t q π jA (chart_toSpec R 0) a 0)) ≫
      (Cor.boundarySection X₀ Q (fullBoundaryProductMap π jA dA z)
        (pullback.fst (jA ≫ π) π) jAret M hcA
        (pullback.snd (jA ≫ π) ((u ≫ jA) ≫ π)) hbA aA -
      Cor.boundarySection X₀ Q (fullBoundaryProductMap π jA dA z)
        (pullback.fst (jA ≫ π) π) jAret LA hcA
        (pullback.snd (jA ≫ π) ((u ≫ jA) ≫ π)) hbA bA)) -
      (Cor.boundarySection A₀ Q (psiBoundaryInclusion q (f ≫ π) j p hq a z s hs d)
          (pullback.fst (a ≫ q) (f ≫ π)) jNret c.N hcN
          (pullback.snd (a ≫ q) (v ≫ (f ≫ π)) ≫ pV) hbN c.dS -
        Cor.boundarySection A₀ Q (psiBoundaryInclusion q (f ≫ π) j p hq a z s hs d)
          (pullback.fst (a ≫ q) (f ≫ π)) jNret c.N hcN
          (pullback.snd (a ≫ q) (v ≫ (f ≫ π)) ≫ pV) hbN c.nS) -
      (show Cor.mk A₀ ⟶ Cor.mk Q from (Cor.graphFunctor k).map
        (correctionSmallParameterMap t q π jA (chart_toSpec R 0) a u rA hrA)) = Ω := by
  dsimp only
  unfold originalPairMarkedMiddle
  let π := ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))
  let q := boundaryLineProjection R
  let jA := chart R 0
  let X₀ := lambdaSourceSite k t π jA
  let A₀ := psiSourceSite k t q a
  let Q := relativeTargetSite k t π (u ≫ jA)
  let α := originalCorrectionPairSiteMap t q π jA (chart_toSpec R 0) a
  let rsite := correctionSmallParameterMap t q π jA (chart_toSpec R 0) a u rA hrA
  have hα₁ : α 1 = 𝟙 A₀ := by
    ext1
    rfl
  have hαgraph : ((Cor.graphFunctor k).map (α 1) : Cor.mk A₀ ⟶ Cor.mk A₀) =
      𝟙 (Cor.mk A₀) := by
    exact (congrArg (fun g : A₀ ⟶ A₀ =>
      ((Cor.graphFunctor k).map g : Cor.mk A₀ ⟶ Cor.mk A₀)) hα₁).trans
        ((Cor.graphFunctor k).map_id A₀)
  have htarget := nativeCorrection_target_branch (R := R) (f := f) (j := j)
    (p := p) (hq := hq) (hret := hret) (a := a) (z := z) (s := s) (hs := hs)
    (d := d) (v := v) (hcover := hcover) (dA := dA) (LA := LA) (aA := aA) (bA := bA)
    (t := t) (u := u) (vY := vY) (hvY := hvY) (pV := pV) (hpV := hpV)
    (hinfty := hinfty) (hpuncture := hpuncture)
  have hsource := nativeCorrection_source_branch (R := R) (f := f) (j := j)
    (p := p) (hq := hq) (hret := hret) (a := a) (z := z) (s := s) (hs := hs)
    (H := H) (e := e) (ha := ha) (d := d) (hd := hd) (c := c) (v := v)
    (hcover := hcover) (dA := dA) (t := t) (u := u) (vY := vY) (hvY := hvY)
    (pV := pV) (hpV := hpV) (hinfty := hinfty) (hpuncture := hpuncture)
  have hassembled := nativeCorrection_branch_assembly
    (A := Cor.mk A₀) (X := Cor.mk X₀) (Z := Cor.mk Q)
    ((Cor.graphFunctor k).map (α 0)) ((Cor.graphFunctor k).map (α 1))
    ((Cor.graphFunctor k).map rsite) hαgraph htarget hsource
  exact hassembled

omit [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R]
  [IsAffine Y] [IsClosedImmersion (z ≫ chart R 0)] [IsAffineHom dA] in
/-- The exact generic result expression, at the actual finite-pair tuple,
lands in the same middle term. No product-norm theorem is invoked. -/
theorem nativeCorrection_generic_to_middle :
    let π := ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))
    let q := boundaryLineProjection R
    let jA := chart R 0
    let X₀ := lambdaSourceSite k t π jA
    let A₀ := psiSourceSite k t q a
    let Q := relativeTargetSite k t π (u ≫ jA)
    let jAret := retainedProductInclusion (jA ≫ π) π (u ≫ jA)
    let jNret := retainedProductInclusion (a ≫ q) (f ≫ π) v
    let : IsIso (pullbackSectionMap (fullBoundaryProductMap π jA dA z) aA) := haA
    let := c.n_unit
    let := c.d_unit
    let : IsAffine X₀.left := inferInstanceAs (IsAffine (Spec (.of (Polynomial R))))
    let : IsAffine A₀.left := ‹IsAffine A›
    let : IsAffine (retainedProduct (jA ≫ π) π (u ≫ jA)) :=
      retainedProduct_affine (jA ≫ π) π (u ≫ jA)
    let : IsAffine (retainedProduct (a ≫ q) (f ≫ π) v) :=
      retainedProduct_affine (a ≫ q) (f ≫ π) v
    let : SmoothOfRelativeDimension 1 (jAret ≫ pullback.fst (jA ≫ π) π) :=
      retainedProduct_smooth (jA ≫ π) π (u ≫ jA)
    let : SmoothOfRelativeDimension 1 (jNret ≫ pullback.fst (a ≫ q) (f ≫ π)) :=
      retainedProduct_smooth (a ≫ q) (f ≫ π) v
    let O := originalCorrectionPairSite t q π jA a
    let α := originalCorrectionPairSiteMap t q π jA (chart_toSpec R 0) a
    let C₀ := originalCorrectionPairCompact q π f jA a
    let U₁ := originalCorrectionPairSmallRetained q π f jA a u v
    let i₁ := originalCorrectionPairFullBoundaryInclusion q π f j jA p a d dA z s hq hs
    let j₁ := originalCorrectionPairSmallInclusion q π f jA a u v
    let q₀ : ∀ i, C₀ i ⟶ (O i).left := originalCorrectionPairProjection q π f jA a
    let g₁ : ∀ i, U₁ i ⟶ Q.left := originalCorrectionPairSmallTargetMap q π f jA a u v pV
    let hc₁ := originalCorrectionPair_fullBoundary_cover q π f j jA p a d dA z s hq hs
      u v hinfty hpuncture hcover
    let hb₁ : ∀ i, (j₁ i ≫ q₀ i) ≫ (O i).hom = g₁ i ≫ Q.hom := by
      intro i
      fin_cases i
      · exact retainedProduct_structure (jA ≫ π) π (u ≫ jA) t
      · exact retainedProduct_structure_factor (a ≫ q) (f ≫ π) v t pV Q.hom
          (correctionSmallTarget_structure t π f j jA p hret u v vY hvY pV hpV)
    let B₁ := originalCorrectionPairFullBoundary q π f jA a d dA z
    let γ := compactificationGraph π jA
    let hI : IsLocallyRankOne (C₀ 0) (idealModule γ) :=
      (relativeCompactificationGraphLine π jA).property
    let MC : LineBundle (C₀ 0) := LA
    let MA := tensorLineBundle (C₀ 0) MC (dualLineBundle (C₀ 0) ⟨idealModule γ, hI⟩)
    let aSC : SheafOfModules.unit (C₀ 0).ringCatSheaf ⟶ MA.val := aA
    let bSC : SheafOfModules.unit (C₀ 0).ringCatSheaf ⟶ MC.val := bA
    let : IsIso (pullbackSectionMap (i₁ 0) aSC) := haA
    let : IsIso (pullbackSectionMap (i₁ 0) bSC) := hbAUnit
    let nφ := sectionDualFunctional _ c.N c.nS
    let dφ := sectionDualFunctional _ c.N c.dS
    let NC : LineBundle (C₀ 1) := dualLineBundle _ c.N
    let nSC : NC.val ⟶ SheafOfModules.unit (C₀ 1).ringCatSheaf := nφ
    let dSC : NC.val ⟶ SheafOfModules.unit (C₀ 1).ringCatSheaf := dφ
    let : IsIso (pullbackSectionMap (i₁ 1) c.nS) := c.n_unit
    let : IsIso (pullbackSectionMap (i₁ 1) c.dS) := c.d_unit
    let : IsIso ((Modules.pullback (i₁ 1)).map nSC) :=
      sectionDualFunctional_pullback_map_isIso (i₁ 1) c.N c.nS
    let : IsIso ((Modules.pullback (i₁ 1)).map dSC) :=
      sectionDualFunctional_pullback_map_isIso (i₁ 1) c.N c.dS
    let rsite := correctionSmallParameterMap t q π jA (chart_toSpec R 0) a u rA hrA
    let haSmall : IsIso (pullbackSectionMap (i₁ 0) aSC) := haA
    let hbSmall : IsIso (pullbackSectionMap (i₁ 0) bSC) := hbAUnit
    let exactGenericExpression := fun
      {k : Type u} [Field k]
      (X Z : SmoothSite (Spec (.of k)))
      (O : Fin 2 → SmoothSite (Spec (.of k))) [∀ i, IsAffine (O i).left]
      (α : ∀ i, X ⟶ O i)
      (C₀ U₁ B₁ : Fin 2 → Scheme.{u})
      (q₀ : ∀ i, C₀ i ⟶ (O i).left) [∀ i, IsProper (q₀ i)]
      (i₁ : ∀ i, B₁ i ⟶ C₀ i) (j₁ : ∀ i, U₁ i ⟶ C₀ i)
      [∀ i, IsOpenImmersion (j₁ i)] [∀ i, (U₁ i).IsQuasiAffine]
      [∀ i, SmoothOfRelativeDimension 1 (j₁ i ≫ q₀ i)]
      (γ : (O 0).left ⟶ C₀ 0)
      (hI : IsLocallyRankOne (C₀ 0) (idealModule γ))
      (M : LineBundle (C₀ 0))
      (aS : SheafOfModules.unit (C₀ 0).ringCatSheaf ⟶
        (tensorLineBundle (C₀ 0) M
          (dualLineBundle (C₀ 0) ⟨idealModule γ, hI⟩)).val)
      (bS : SheafOfModules.unit (C₀ 0).ringCatSheaf ⟶ M.val)
      (N : LineBundle (C₀ 1))
      (nS dS : N.val ⟶ SheafOfModules.unit (C₀ 1).ringCatSheaf)
      (hc₁ : ∀ i (x : C₀ i), x ∈ Set.range (j₁ i) ∨ x ∈ Set.range (i₁ i))
      [IsIso (pullbackSectionMap (i₁ 0) aS)]
      [IsIso (pullbackSectionMap (i₁ 0) bS)]
      [IsIso ((Modules.pullback (i₁ 1)).map nS)]
      [IsIso ((Modules.pullback (i₁ 1)).map dS)]
      (g₁ : ∀ i, U₁ i ⟶ Z.left)
      (hb₁ : ∀ i, (j₁ i ≫ q₀ i) ≫ (O i).hom = g₁ i ≫ Z.hom)
      (r : X ⟶ Z) =>
      let I : LineBundle (C₀ 0) := ⟨idealModule γ, hI⟩
      let A := tensorLineBundle (C₀ 0) M (dualLineBundle (C₀ 0) I)
      let target : Cor.mk X ⟶ Cor.mk Z :=
        ((Cor.graphFunctor k).map (α 0) : Cor.mk X ⟶ Cor.mk (O 0)) ≫
          (Cor.boundarySection (O 0) Z (i₁ 0) (q₀ 0) (j₁ 0) A
              (hc₁ 0) (g₁ 0) (hb₁ 0) aS -
            Cor.boundarySection (O 0) Z (i₁ 0) (q₀ 0) (j₁ 0) M
              (hc₁ 0) (g₁ 0) (hb₁ 0) bS)
      let correction : Cor.mk X ⟶ Cor.mk Z :=
        ((Cor.graphFunctor k).map (α 1) : Cor.mk X ⟶ Cor.mk (O 1)) ≫
          (Cor.boundaryFunctional (O 1) Z (i₁ 1) (q₀ 1) (j₁ 1) N dS
              (hc₁ 1) (g₁ 1) (hb₁ 1) -
            Cor.boundaryFunctional (O 1) Z (i₁ 1) (q₀ 1) (j₁ 1) N nS
              (hc₁ 1) (g₁ 1) (hb₁ 1))
      let graph : Cor.mk X ⟶ Cor.mk Z := (Cor.graphFunctor k).map r
      target - correction - graph
    let genericLHS : Cor.mk A₀ ⟶ Cor.mk Q :=
      @exactGenericExpression k inferInstance A₀ Q O (fun _ => inferInstance) α
      C₀ U₁ B₁ q₀ (fun _ => inferInstance) i₁ j₁
      (fun _ => inferInstance) (fun _ => inferInstance) (fun _ => inferInstance)
      γ hI MC aSC bSC NC nSC dSC hc₁ haSmall hbSmall
      inferInstance inferInstance g₁ hb₁ rsite
    let Ω : Cor.mk A₀ ⟶ Cor.mk Q :=
      @originalPairMarkedMiddle k inferInstance A₀ Q O (fun _ => inferInstance) α
      C₀ U₁ B₁ q₀ (fun _ => inferInstance) i₁ j₁
      (fun _ => inferInstance) (fun _ => inferInstance) (fun _ => inferInstance)
      γ hI MC aSC bSC NC nSC dSC hc₁ haSmall hbSmall
      inferInstance inferInstance g₁ hb₁ rsite
    genericLHS = Ω := by
  rfl

omit [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R]
  [IsAffine Y] [IsClosedImmersion (z ≫ chart R 0)] [IsAffineHom dA] in
/-- Kernel-check the actual canonical/generic composition before any norm
or principal-action proof is added. This statement allows the empty parameter. -/
theorem nativeCorrection_middle_composition :
    let π := ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))
    let q := boundaryLineProjection R
    let jA := chart R 0
    let X₀ := lambdaSourceSite k t π jA
    let A₀ := psiSourceSite k t q a
    let Q := relativeTargetSite k t π (u ≫ jA)
    let jAret := retainedProductInclusion (jA ≫ π) π (u ≫ jA)
    let jNret := retainedProductInclusion (a ≫ q) (f ≫ π) v
    let M := tensorLineBundle _ LA (dualLineBundle _ (relativeCompactificationGraphLine π jA))
    let : IsIso (pullbackSectionMap (fullBoundaryProductMap π jA dA z) aA) := haA
    let := c.n_unit
    let := c.d_unit
    let : IsAffine X₀.left := inferInstanceAs (IsAffine (Spec (.of (Polynomial R))))
    let : IsAffine A₀.left := ‹IsAffine A›
    let : IsAffine (retainedProduct (jA ≫ π) π (u ≫ jA)) :=
      retainedProduct_affine (jA ≫ π) π (u ≫ jA)
    let : IsAffine (retainedProduct (a ≫ q) (f ≫ π) v) :=
      retainedProduct_affine (a ≫ q) (f ≫ π) v
    let : SmoothOfRelativeDimension 1 (jAret ≫ pullback.fst (jA ≫ π) π) :=
      retainedProduct_smooth (jA ≫ π) π (u ≫ jA)
    let : SmoothOfRelativeDimension 1 (jNret ≫ pullback.fst (a ≫ q) (f ≫ π)) :=
      retainedProduct_smooth (a ≫ q) (f ≫ π) v
    let hcA := lambdaBoundary_retained_cover π jA z dA (u ≫ jA)
      (correction_target_small_cover jA dA z u hinfty hpuncture)
    let hcN := psiBoundary_retained_cover q (f ≫ π) j p hq a z s hs d v hcover
    let hbA := retainedProduct_structure (jA ≫ π) π (u ≫ jA) t
    let hbN := retainedProduct_structure_factor (a ≫ q) (f ≫ π) v t pV Q.hom
      (correctionSmallTarget_structure t π f j jA p hret u v vY hvY pV hpV)
    let O := originalCorrectionPairSite t q π jA a
    let α := originalCorrectionPairSiteMap t q π jA (chart_toSpec R 0) a
    let C₀ := originalCorrectionPairCompact q π f jA a
    let U₁ := originalCorrectionPairSmallRetained q π f jA a u v
    let i₁ := originalCorrectionPairFullBoundaryInclusion q π f j jA p a d dA z s hq hs
    let j₁ := originalCorrectionPairSmallInclusion q π f jA a u v
    let q₀ : ∀ i, C₀ i ⟶ (O i).left := originalCorrectionPairProjection q π f jA a
    let g₁ : ∀ i, U₁ i ⟶ Q.left := originalCorrectionPairSmallTargetMap q π f jA a u v pV
    let hc₁ := originalCorrectionPair_fullBoundary_cover q π f j jA p a d dA z s hq hs
      u v hinfty hpuncture hcover
    let hb₁ : ∀ i, (j₁ i ≫ q₀ i) ≫ (O i).hom = g₁ i ≫ Q.hom := by
      intro i
      fin_cases i
      · exact retainedProduct_structure (jA ≫ π) π (u ≫ jA) t
      · exact retainedProduct_structure_factor (a ≫ q) (f ≫ π) v t pV Q.hom
          (correctionSmallTarget_structure t π f j jA p hret u v vY hvY pV hpV)
    let B₁ := originalCorrectionPairFullBoundary q π f jA a d dA z
    let γ := compactificationGraph π jA
    let hI : IsLocallyRankOne (C₀ 0) (idealModule γ) :=
      (relativeCompactificationGraphLine π jA).property
    let MC : LineBundle (C₀ 0) := LA
    let MA := tensorLineBundle (C₀ 0) MC (dualLineBundle (C₀ 0) ⟨idealModule γ, hI⟩)
    let aSC : SheafOfModules.unit (C₀ 0).ringCatSheaf ⟶ MA.val := aA
    let bSC : SheafOfModules.unit (C₀ 0).ringCatSheaf ⟶ MC.val := bA
    let : IsIso (pullbackSectionMap (i₁ 0) aSC) := haA
    let : IsIso (pullbackSectionMap (i₁ 0) bSC) := hbAUnit
    let nφ := sectionDualFunctional _ c.N c.nS
    let dφ := sectionDualFunctional _ c.N c.dS
    let NC : LineBundle (C₀ 1) := dualLineBundle _ c.N
    let nSC : NC.val ⟶ SheafOfModules.unit (C₀ 1).ringCatSheaf := nφ
    let dSC : NC.val ⟶ SheafOfModules.unit (C₀ 1).ringCatSheaf := dφ
    let : IsIso (pullbackSectionMap (i₁ 1) c.nS) := c.n_unit
    let : IsIso (pullbackSectionMap (i₁ 1) c.dS) := c.d_unit
    let : IsIso ((Modules.pullback (i₁ 1)).map nSC) :=
      sectionDualFunctional_pullback_map_isIso (i₁ 1) c.N c.nS
    let : IsIso ((Modules.pullback (i₁ 1)).map dSC) :=
      sectionDualFunctional_pullback_map_isIso (i₁ 1) c.N c.dS
    let rsite := correctionSmallParameterMap t q π jA (chart_toSpec R 0) a u rA hrA
    let haSmall : IsIso (pullbackSectionMap (i₁ 0) aSC) := haA
    let hbSmall : IsIso (pullbackSectionMap (i₁ 0) bSC) := hbAUnit
    let exactGenericExpression := fun
      {k : Type u} [Field k]
      (X Z : SmoothSite (Spec (.of k)))
      (O : Fin 2 → SmoothSite (Spec (.of k))) [∀ i, IsAffine (O i).left]
      (α : ∀ i, X ⟶ O i)
      (C₀ U₁ B₁ : Fin 2 → Scheme.{u})
      (q₀ : ∀ i, C₀ i ⟶ (O i).left) [∀ i, IsProper (q₀ i)]
      (i₁ : ∀ i, B₁ i ⟶ C₀ i) (j₁ : ∀ i, U₁ i ⟶ C₀ i)
      [∀ i, IsOpenImmersion (j₁ i)] [∀ i, (U₁ i).IsQuasiAffine]
      [∀ i, SmoothOfRelativeDimension 1 (j₁ i ≫ q₀ i)]
      (γ : (O 0).left ⟶ C₀ 0)
      (hI : IsLocallyRankOne (C₀ 0) (idealModule γ))
      (M : LineBundle (C₀ 0))
      (aS : SheafOfModules.unit (C₀ 0).ringCatSheaf ⟶
        (tensorLineBundle (C₀ 0) M
          (dualLineBundle (C₀ 0) ⟨idealModule γ, hI⟩)).val)
      (bS : SheafOfModules.unit (C₀ 0).ringCatSheaf ⟶ M.val)
      (N : LineBundle (C₀ 1))
      (nS dS : N.val ⟶ SheafOfModules.unit (C₀ 1).ringCatSheaf)
      (hc₁ : ∀ i (x : C₀ i), x ∈ Set.range (j₁ i) ∨ x ∈ Set.range (i₁ i))
      [IsIso (pullbackSectionMap (i₁ 0) aS)]
      [IsIso (pullbackSectionMap (i₁ 0) bS)]
      [IsIso ((Modules.pullback (i₁ 1)).map nS)]
      [IsIso ((Modules.pullback (i₁ 1)).map dS)]
      (g₁ : ∀ i, U₁ i ⟶ Z.left)
      (hb₁ : ∀ i, (j₁ i ≫ q₀ i) ≫ (O i).hom = g₁ i ≫ Z.hom)
      (r : X ⟶ Z) =>
      let I : LineBundle (C₀ 0) := ⟨idealModule γ, hI⟩
      let A := tensorLineBundle (C₀ 0) M (dualLineBundle (C₀ 0) I)
      let target : Cor.mk X ⟶ Cor.mk Z :=
        ((Cor.graphFunctor k).map (α 0) : Cor.mk X ⟶ Cor.mk (O 0)) ≫
          (Cor.boundarySection (O 0) Z (i₁ 0) (q₀ 0) (j₁ 0) A
              (hc₁ 0) (g₁ 0) (hb₁ 0) aS -
            Cor.boundarySection (O 0) Z (i₁ 0) (q₀ 0) (j₁ 0) M
              (hc₁ 0) (g₁ 0) (hb₁ 0) bS)
      let correction : Cor.mk X ⟶ Cor.mk Z :=
        ((Cor.graphFunctor k).map (α 1) : Cor.mk X ⟶ Cor.mk (O 1)) ≫
          (Cor.boundaryFunctional (O 1) Z (i₁ 1) (q₀ 1) (j₁ 1) N dS
              (hc₁ 1) (g₁ 1) (hb₁ 1) -
            Cor.boundaryFunctional (O 1) Z (i₁ 1) (q₀ 1) (j₁ 1) N nS
              (hc₁ 1) (g₁ 1) (hb₁ 1))
      let graph : Cor.mk X ⟶ Cor.mk Z := (Cor.graphFunctor k).map r
      target - correction - graph
    let genericLHS : Cor.mk A₀ ⟶ Cor.mk Q :=
      @exactGenericExpression k inferInstance A₀ Q O (fun _ => inferInstance) α
      C₀ U₁ B₁ q₀ (fun _ => inferInstance) i₁ j₁
      (fun _ => inferInstance) (fun _ => inferInstance) (fun _ => inferInstance)
      γ hI MC aSC bSC NC nSC dSC hc₁ haSmall hbSmall
      inferInstance inferInstance g₁ hb₁ rsite
    ((show Cor.mk A₀ ⟶ Cor.mk X₀ from (Cor.graphFunctor k).map
        (originalCorrectionPairSiteMap t q π jA (chart_toSpec R 0) a 0)) ≫
      (Cor.boundarySection X₀ Q (fullBoundaryProductMap π jA dA z)
        (pullback.fst (jA ≫ π) π) jAret M hcA
        (pullback.snd (jA ≫ π) ((u ≫ jA) ≫ π)) hbA aA -
      Cor.boundarySection X₀ Q (fullBoundaryProductMap π jA dA z)
        (pullback.fst (jA ≫ π) π) jAret LA hcA
        (pullback.snd (jA ≫ π) ((u ≫ jA) ≫ π)) hbA bA)) -
      (Cor.boundarySection A₀ Q (psiBoundaryInclusion q (f ≫ π) j p hq a z s hs d)
          (pullback.fst (a ≫ q) (f ≫ π)) jNret c.N hcN
          (pullback.snd (a ≫ q) (v ≫ (f ≫ π)) ≫ pV) hbN c.dS -
        Cor.boundarySection A₀ Q (psiBoundaryInclusion q (f ≫ π) j p hq a z s hs d)
          (pullback.fst (a ≫ q) (f ≫ π)) jNret c.N hcN
          (pullback.snd (a ≫ q) (v ≫ (f ≫ π)) ≫ pV) hbN c.nS) -
      (show Cor.mk A₀ ⟶ Cor.mk Q from (Cor.graphFunctor k).map
        (correctionSmallParameterMap t q π jA (chart_toSpec R 0) a u rA hrA)) = genericLHS := by
  have hcanonical := nativeCorrection_canonical_to_middle (R := R) (f := f) (j := j)
    (p := p) (hq := hq) (hret := hret) (a := a) (z := z) (s := s) (hs := hs)
    (H := H) (e := e) (ha := ha) (d := d) (hd := hd) (c := c) (v := v)
    (hcover := hcover) (dA := dA) (LA := LA) (aA := aA) (bA := bA)
    (t := t) (u := u) (vY := vY) (hvY := hvY) (pV := pV) (hpV := hpV)
    (rA := rA) (hrA := hrA) (hinfty := hinfty) (hpuncture := hpuncture)
  have hgeneric := nativeCorrection_generic_to_middle (R := R) (f := f) (j := j)
    (p := p) (hq := hq) (hret := hret) (a := a) (z := z) (s := s) (hs := hs)
    (H := H) (e := e) (ha := ha) (d := d) (hd := hd) (c := c) (v := v)
    (hcover := hcover) (dA := dA) (LA := LA) (aA := aA) (bA := bA)
    (t := t) (u := u) (vY := vY) (hvY := hvY) (pV := pV) (hpV := hpV)
    (rA := rA) (hrA := hrA) (hinfty := hinfty) (hpuncture := hpuncture)
  exact hcanonical.trans hgeneric.symm

omit [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R]
  [IsAffine Y] [IsClosedImmersion (z ≫ chart R 0)] [IsAffineHom dA] in
/-- The same actual middle vanishes on an empty parameter scheme; no
integral-target supplier is used for this branch. -/
theorem nativeCorrection_middle_empty [IsEmpty A] :
    let π := ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))
    let q := boundaryLineProjection R
    let jA := chart R 0
    let X₀ := lambdaSourceSite k t π jA
    let A₀ := psiSourceSite k t q a
    let Q := relativeTargetSite k t π (u ≫ jA)
    let jAret := retainedProductInclusion (jA ≫ π) π (u ≫ jA)
    let jNret := retainedProductInclusion (a ≫ q) (f ≫ π) v
    let : IsIso (pullbackSectionMap (fullBoundaryProductMap π jA dA z) aA) := haA
    let := c.n_unit
    let := c.d_unit
    let : IsAffine X₀.left := inferInstanceAs (IsAffine (Spec (.of (Polynomial R))))
    let : IsAffine A₀.left := ‹IsAffine A›
    let : IsAffine (retainedProduct (jA ≫ π) π (u ≫ jA)) :=
      retainedProduct_affine (jA ≫ π) π (u ≫ jA)
    let : IsAffine (retainedProduct (a ≫ q) (f ≫ π) v) :=
      retainedProduct_affine (a ≫ q) (f ≫ π) v
    let : SmoothOfRelativeDimension 1 (jAret ≫ pullback.fst (jA ≫ π) π) :=
      retainedProduct_smooth (jA ≫ π) π (u ≫ jA)
    let : SmoothOfRelativeDimension 1 (jNret ≫ pullback.fst (a ≫ q) (f ≫ π)) :=
      retainedProduct_smooth (a ≫ q) (f ≫ π) v
    let O := originalCorrectionPairSite t q π jA a
    let α := originalCorrectionPairSiteMap t q π jA (chart_toSpec R 0) a
    let C₀ := originalCorrectionPairCompact q π f jA a
    let U₁ := originalCorrectionPairSmallRetained q π f jA a u v
    let i₁ := originalCorrectionPairFullBoundaryInclusion q π f j jA p a d dA z s hq hs
    let j₁ := originalCorrectionPairSmallInclusion q π f jA a u v
    let q₀ : ∀ i, C₀ i ⟶ (O i).left := originalCorrectionPairProjection q π f jA a
    let g₁ : ∀ i, U₁ i ⟶ Q.left := originalCorrectionPairSmallTargetMap q π f jA a u v pV
    let hc₁ := originalCorrectionPair_fullBoundary_cover q π f j jA p a d dA z s hq hs
      u v hinfty hpuncture hcover
    let hb₁ : ∀ i, (j₁ i ≫ q₀ i) ≫ (O i).hom = g₁ i ≫ Q.hom := by
      intro i
      fin_cases i
      · exact retainedProduct_structure (jA ≫ π) π (u ≫ jA) t
      · exact retainedProduct_structure_factor (a ≫ q) (f ≫ π) v t pV Q.hom
          (correctionSmallTarget_structure t π f j jA p hret u v vY hvY pV hpV)
    let B₁ := originalCorrectionPairFullBoundary q π f jA a d dA z
    let γ := compactificationGraph π jA
    let hI : IsLocallyRankOne (C₀ 0) (idealModule γ) :=
      (relativeCompactificationGraphLine π jA).property
    let MC : LineBundle (C₀ 0) := LA
    let MA := tensorLineBundle (C₀ 0) MC (dualLineBundle (C₀ 0) ⟨idealModule γ, hI⟩)
    let aSC : SheafOfModules.unit (C₀ 0).ringCatSheaf ⟶ MA.val := aA
    let bSC : SheafOfModules.unit (C₀ 0).ringCatSheaf ⟶ MC.val := bA
    let : IsIso (pullbackSectionMap (i₁ 0) aSC) := haA
    let : IsIso (pullbackSectionMap (i₁ 0) bSC) := hbAUnit
    let nφ := sectionDualFunctional _ c.N c.nS
    let dφ := sectionDualFunctional _ c.N c.dS
    let NC : LineBundle (C₀ 1) := dualLineBundle _ c.N
    let nSC : NC.val ⟶ SheafOfModules.unit (C₀ 1).ringCatSheaf := nφ
    let dSC : NC.val ⟶ SheafOfModules.unit (C₀ 1).ringCatSheaf := dφ
    let : IsIso (pullbackSectionMap (i₁ 1) c.nS) := c.n_unit
    let : IsIso (pullbackSectionMap (i₁ 1) c.dS) := c.d_unit
    let : IsIso ((Modules.pullback (i₁ 1)).map nSC) :=
      sectionDualFunctional_pullback_map_isIso (i₁ 1) c.N c.nS
    let : IsIso ((Modules.pullback (i₁ 1)).map dSC) :=
      sectionDualFunctional_pullback_map_isIso (i₁ 1) c.N c.dS
    let rsite := correctionSmallParameterMap t q π jA (chart_toSpec R 0) a u rA hrA
    let haSmall : IsIso (pullbackSectionMap (i₁ 0) aSC) := haA
    let hbSmall : IsIso (pullbackSectionMap (i₁ 0) bSC) := hbAUnit
    let Ω : Cor.mk A₀ ⟶ Cor.mk Q :=
      @originalPairMarkedMiddle k inferInstance A₀ Q O (fun _ => inferInstance) α
      C₀ U₁ B₁ q₀ (fun _ => inferInstance) i₁ j₁
      (fun _ => inferInstance) (fun _ => inferInstance) (fun _ => inferInstance)
      γ hI MC aSC bSC NC nSC dSC hc₁ haSmall hbSmall
      inferInstance inferInstance g₁ hb₁ rsite
    Ω = 0 := by
  dsimp only
  let : IsEmpty (Cor.mk (psiSourceSite k t (boundaryLineProjection R) a)).toSmoothSite.left :=
    ‹IsEmpty A›
  exact Cor.hom_eq_zero_of_isEmpty_source k _

end Motivic.Cor
