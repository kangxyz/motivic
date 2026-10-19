/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.Presheaf.Actions.Pencils.NativeCorrectionNormAction
public import Motivic.Transfers.Presheaf.Actions.Pencils.NativeCorrectionPairMiddle
public import Motivic.Transfers.Presheaf.Actions.Pencils.OriginalPairMarkedNormMiddle
public import Motivic.AlgebraicGeometry.Correspondences.Moving.Pencils.Norm.OriginalPairMarkedNormProduct
public import Motivic.Transfers.Presheaf.Actions.Pencils.OriginalPairNormDictionary
public import Motivic.AlgebraicGeometry.Correspondences.Coproducts.Binary
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Correction.OriginalCorrectionActionGeometry
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Correction.OriginalCorrectionInfinityUnits
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.GenericFiber.LineRatioIdentity
public import Motivic.Aglib.Data.Fin.TwoCases

/-! # Transfer comparison from the same original correction sections

The exact original sections construct the normalized product. The actual
identity/finite-map diagram then compares their transfers. The correction has
its original denominator-minus-numerator sign. No normalized unit, germ, value,
correspondence identity or presheaf action identity is an input.
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
universe v u
namespace Motivic.PresheafWithTransfers

local instance {X Y : Scheme.{u}} (f : X ⟶ Y) [SmoothOfRelativeDimension 1 f] :
    Smooth f := SmoothOfRelativeDimension.smooth 1 f

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
  {k : Type u} [Field k] (Pst : PresheafWithTransfers.{v} k)
  (hPst : Pst.IsA1Invariant) (t : Spec (.of R) ⟶ Spec (.of k)) [Smooth t]
  {U : Scheme.{u}} [IsAffine U]
  (u : U ⟶ Spec (.of (Polynomial R))) [IsOpenImmersion u]
  [SmoothOfRelativeDimension 1
    ((u ≫ chart R 0) ≫ ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))]
  (vY : V ⟶ Y) (hvY : vY ≫ j = v) (pV : V ⟶ U) (hpV : pV ≫ u = vY ≫ p)
  (rA : A ⟶ U) (hrA : rA ≫ u = a)
  (hinfty : (Set.range (chart R 0))ᶜ ⊆ Set.range dA)
  (hpuncture : (Set.range u)ᶜ ⊆ Set.range z)

omit [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R]
  [IsAffine Y] [IsAffine A] [IsAffineHom dA]
  [IsClosedImmersion (z ≫ chart R 0)] in
include hpairA in
/-- The actual original and changed infinity units, proved once from the same
full-boundary sections and the actual compact parameter squares. -/
private theorem nativeCorrection_infinity_units :
    let π := ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))
    let q := boundaryLineProjection R
    let jA := chart R 0
    let τ := retainedNormParameterMap π (a ≫ q) jA a
      (congrArg (fun k => a ≫ k) (chart_toSpec R 0).symm)
    let M := tensorLineBundle _ LA (dualLineBundle _ (relativeCompactificationGraphLine π jA))
    let cA := twistedIdealSection _ (relativeCompactificationGraphLine π jA) LA
      (idealInclusion (compactificationGraph π jA)) bA
    let nφ := sectionDualFunctional _ c.N c.nS
    let dφ := sectionDualFunctional _ c.N c.dS
    let aφ := pullbackUnitMap τ (sectionDualFunctional _ M aA)
    let cφ := pullbackUnitMap τ (sectionDualFunctional _ M cA)
    let i₀ := originalCorrectionPairInfinityInclusion q π f jA a d dA
    let i := originalCorrectionPairChangedInfinityInclusion q π f a d dA
    IsIso (pullbackSectionMap (i₀ 0) aA) ∧
    IsIso (pullbackSectionMap (i₀ 0) bA) ∧
    IsIso ((Modules.pullback (i₀ 0)).map (idealInclusion (compactificationGraph π jA))) ∧
    IsIso (pullbackSectionMap (i₀ 0) cA) ∧
    IsIso ((Modules.pullback (i₀ 1)).map nφ) ∧
    IsIso ((Modules.pullback (i₀ 1)).map dφ) ∧
    IsIso ((Modules.pullback (i 0)).map aφ) ∧
    IsIso ((Modules.pullback (i 0)).map cφ) ∧
    IsIso ((Modules.pullback (i 0)).map
      (pullbackUnitMap τ (sectionDualFunctional _ LA bA))) ∧
    IsIso ((Modules.pullback (i 1)).map (pullbackUnitMap (𝟙 _) nφ)) ∧
    IsIso ((Modules.pullback (i 1)).map (pullbackUnitMap (𝟙 _) dφ)) := by
  let π := ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))
  let q := boundaryLineProjection R
  let jA := chart R 0
  let τ := retainedNormParameterMap π (a ≫ q) jA a
    (congrArg (fun k => a ≫ k) (chart_toSpec R 0).symm)
  let M := tensorLineBundle _ LA (dualLineBundle _ (relativeCompactificationGraphLine π jA))
  let cA := twistedIdealSection _ (relativeCompactificationGraphLine π jA) LA
    (idealInclusion (compactificationGraph π jA)) bA
  let nφ := sectionDualFunctional _ c.N c.nS
  let dφ := sectionDualFunctional _ c.N c.dS
  let aφ := pullbackUnitMap τ (sectionDualFunctional _ M aA)
  let cφ := pullbackUnitMap τ (sectionDualFunctional _ M cA)
  let i₀ := originalCorrectionPairInfinityInclusion q π f jA a d dA
  let i := originalCorrectionPairChangedInfinityInclusion q π f a d dA
  let c' := originalCorrectionPairCompactMap q π f jA (chart_toSpec R 0) a
  let := c.n_unit
  let := c.d_unit
  let : IsIso (pullbackSectionMap (fullBoundaryProductMap π jA dA z) aA) := haA
  let : IsIso (pullbackSectionMap
      (coprod.desc (infinityProductMap π jA dA) (graphBoundaryRestriction π jA z)) bA) :=
    hbAUnit
  let : IsIso (pullbackSectionMap (i₀ 0) aA) :=
    pullbackSectionMap_coprod_left_isIso (infinityProductMap π jA dA)
      (graphBoundaryRestriction π jA z) aA
  let : IsIso (pullbackSectionMap (i₀ 0) bA) :=
    pullbackSectionMap_coprod_left_isIso (infinityProductMap π jA dA)
      (graphBoundaryRestriction π jA z) bA
  let : IsIso ((Modules.pullback (i₀ 0)).map (idealInclusion (compactificationGraph π jA))) :=
    correctionInfinity_pullbackIdealInclusion_isIso π jA dA hdA
  let : IsIso (pullbackSectionMap (i₀ 0) cA) :=
    graphTwistedSection_infinity_isIso q π jA (𝟙 _)
      ((chart_toSpec R 0).trans (Category.id_comp q).symm)
      z z (Category.comp_id z) (IsPullback.id_vert z) e dA hdA LA aA bA hpairA
  let : IsIso (pullbackSectionMap (i₀ 1) c.nS) :=
    pullbackSectionMap_coprod_left_isIso
      (pullback.fst (pullback.snd (a ≫ q) (f ≫ π)) d)
      (psiZeroInclusion q (f ≫ π) j p hq a z s hs) c.nS
  let : IsIso (pullbackSectionMap (i₀ 1) c.dS) :=
    pullbackSectionMap_coprod_left_isIso
      (pullback.fst (pullback.snd (a ≫ q) (f ≫ π)) d)
      (psiZeroInclusion q (f ≫ π) j p hq a z s hs) c.dS
  let : IsIso ((Modules.pullback (i₀ 0)).map (sectionDualFunctional _ M aA)) :=
    sectionDualFunctional_pullback_map_isIso (i₀ 0) M aA
  let : IsIso ((Modules.pullback (i₀ 0)).map (sectionDualFunctional _ M cA)) :=
    sectionDualFunctional_pullback_map_isIso (i₀ 0) M cA
  let : IsIso ((Modules.pullback (i₀ 0)).map (sectionDualFunctional _ LA bA)) :=
    sectionDualFunctional_pullback_map_isIso (i₀ 0) LA bA
  let : IsIso ((Modules.pullback (i₀ 1)).map nφ) :=
    sectionDualFunctional_pullback_map_isIso (i₀ 1) c.N c.nS
  let : IsIso ((Modules.pullback (i₀ 1)).map dφ) :=
    sectionDualFunctional_pullback_map_isIso (i₀ 1) c.N c.dS
  let l := originalCorrectionPairInfinityMap q π f jA (chart_toSpec R 0) a d dA
  have hi : ∀ t, i t ≫ c' t = l t ≫ i₀ t := fun t =>
    (originalCorrectionPairInfinityMap_inclusion q π f jA (chart_toSpec R 0) a d dA t).symm
  let : IsIso ((Modules.pullback (i 0)).map aφ) :=
    pullback_map_unit_isIso_of_comm (c' 0) (i₀ 0) (i 0) (l 0) (hi 0)
      (sectionDualFunctional _ M aA)
  let : IsIso ((Modules.pullback (i 0)).map cφ) :=
    pullback_map_unit_isIso_of_comm (c' 0) (i₀ 0) (i 0) (l 0) (hi 0)
      (sectionDualFunctional _ M cA)
  let : IsIso ((Modules.pullback (i 0)).map
      (pullbackUnitMap τ (sectionDualFunctional _ LA bA))) :=
    pullback_map_unit_isIso_of_comm (c' 0) (i₀ 0) (i 0) (l 0) (hi 0)
      (sectionDualFunctional _ LA bA)
  let : IsIso ((Modules.pullback (i 1)).map (pullbackUnitMap (𝟙 _) nφ)) :=
    pullback_map_unit_isIso_of_comm (c' 1) (i₀ 1) (i 1) (l 1) (hi 1) nφ
  let : IsIso ((Modules.pullback (i 1)).map (pullbackUnitMap (𝟙 _) dφ)) :=
    pullback_map_unit_isIso_of_comm (c' 1) (i₀ 1) (i 1) (l 1) (hi 1) dφ
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩

omit [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R]
  [IsAffine Y] [IsAffine A] [IsAffineHom dA]
  [IsClosedImmersion (z ≫ chart R 0)] haA hbAUnit in
/-- Only the finite-pair type wrappers are changed. Every regularity and
infinity-unit proof comes from the same original section tuple. -/
private theorem nativeCorrection_functional_wrapper_properties :
    let π := ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))
    let q := boundaryLineProjection R
    let jA := chart R 0
    let τ := retainedNormParameterMap π (a ≫ q) jA a
      (congrArg (fun k => a ≫ k) (chart_toSpec R 0).symm)
    let M := tensorLineBundle _ LA (dualLineBundle _ (relativeCompactificationGraphLine π jA))
    let cA := twistedIdealSection _ (relativeCompactificationGraphLine π jA) LA
      (idealInclusion (compactificationGraph π jA)) bA
    let nφ := sectionDualFunctional _ c.N c.nS
    let dφ := sectionDualFunctional _ c.N c.dS
    let aφ := pullbackUnitMap τ (sectionDualFunctional _ M aA)
    let cφ := pullbackUnitMap τ (sectionDualFunctional _ M cA)
    let C₀ := originalCorrectionPairCompact q π f jA a
    let c' := originalCorrectionPairCompactMap q π f jA (chart_toSpec R 0) a
    let i := originalCorrectionPairChangedInfinityInclusion q π f a d dA
    let I : LineBundle (C₀ 0) := ⟨idealModule (compactificationGraph π jA),
      (relativeCompactificationGraphLine π jA).property⟩
    let MC : LineBundle (C₀ 0) := LA
    let MA := tensorLineBundle (C₀ 0) MC (dualLineBundle (C₀ 0) I)
    let aSC : SheafOfModules.unit (C₀ 0).ringCatSheaf ⟶ MA.val := aA
    let bSC : SheafOfModules.unit (C₀ 0).ringCatSheaf ⟶ MC.val := bA
    let cSC := twistedIdealSection (C₀ 0) I MC
      (idealInclusion (compactificationGraph π jA)) bSC
    let NC : LineBundle (C₀ 1) := dualLineBundle _ c.N
    let nSC : NC.val ⟶ SheafOfModules.unit (C₀ 1).ringCatSheaf := nφ
    let dSC : NC.val ⟶ SheafOfModules.unit (C₀ 1).ringCatSheaf := dφ
    let aT := Hom.pullbackToUnit (sectionDualFunctional (C₀ 0) MA aSC) (c' 0)
    let cT := Hom.pullbackToUnit (sectionDualFunctional (C₀ 0) MA cSC) (c' 0)
    let nT := Hom.pullbackToUnit nSC (c' 1)
    let dT := Hom.pullbackToUnit dSC (c' 1)
    let bT := Hom.pullbackToUnit (sectionDualFunctional (C₀ 0) MC bSC) (c' 0)
    Mono nφ → Mono dφ → Mono aφ → Mono cφ →
    IsIso ((Modules.pullback (i 0)).map aφ) →
    IsIso ((Modules.pullback (i 0)).map cφ) →
    IsIso ((Modules.pullback (i 1)).map (pullbackUnitMap (𝟙 _) nφ)) →
    IsIso ((Modules.pullback (i 1)).map (pullbackUnitMap (𝟙 _) dφ)) →
    IsIso ((Modules.pullback (i 0)).map
      (pullbackUnitMap τ (sectionDualFunctional _ LA bA))) →
    Mono aT ∧ Mono cT ∧ Mono nT ∧ Mono dT ∧
    IsIso ((Modules.pullback (i 0)).map aT) ∧
    IsIso ((Modules.pullback (i 0)).map cT) ∧
    IsIso ((Modules.pullback (i 1)).map nT) ∧
    IsIso ((Modules.pullback (i 1)).map dT) ∧
    IsIso ((Modules.pullback (i 0)).map bT) := by
  dsimp only
  intro hn hd' haM hcM hai hci hni hdi hbi
  let := hn
  let := hd'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · with_reducible
      simpa only [originalCorrectionPairCompact, originalCorrectionPairChangedCompact,
        originalCorrectionPairCompactMap, Fin.twoCases_zero, Matrix.cons_val_zero,
        relativeCompactificationGraphLine, pullbackUnitMap, Hom.pullbackToUnit] using haM
  · with_reducible
      simpa only [originalCorrectionPairCompact, originalCorrectionPairChangedCompact,
        originalCorrectionPairCompactMap, Fin.twoCases_zero, Matrix.cons_val_zero,
        relativeCompactificationGraphLine, pullbackUnitMap, Hom.pullbackToUnit] using hcM
  · with_reducible
      simpa only [originalCorrectionPairCompact, originalCorrectionPairChangedCompact,
        originalCorrectionPairCompactMap, Fin.twoCases_one, Matrix.cons_val_one,
        Matrix.cons_val_zero, pullbackUnitMap, Hom.pullbackToUnit] using
        pullbackUnitMap_id_mono (sectionDualFunctional _ c.N c.nS)
  · with_reducible
      simpa only [originalCorrectionPairCompact, originalCorrectionPairChangedCompact,
        originalCorrectionPairCompactMap, Fin.twoCases_one, Matrix.cons_val_one,
        Matrix.cons_val_zero, pullbackUnitMap, Hom.pullbackToUnit] using
        pullbackUnitMap_id_mono (sectionDualFunctional _ c.N c.dS)
  · with_reducible
      simpa only [originalCorrectionPairCompact, originalCorrectionPairChangedCompact,
        originalCorrectionPairCompactMap, Fin.twoCases_zero, Matrix.cons_val_zero,
        relativeCompactificationGraphLine, pullbackUnitMap, Hom.pullbackToUnit] using hai
  · with_reducible
      simpa only [originalCorrectionPairCompact, originalCorrectionPairChangedCompact,
        originalCorrectionPairCompactMap, Fin.twoCases_zero, Matrix.cons_val_zero,
        relativeCompactificationGraphLine, pullbackUnitMap, Hom.pullbackToUnit] using hci
  · with_reducible
      simpa only [originalCorrectionPairCompact, originalCorrectionPairChangedCompact,
        originalCorrectionPairCompactMap, Fin.twoCases_one, Matrix.cons_val_one,
        Matrix.cons_val_zero, pullbackUnitMap, Hom.pullbackToUnit] using hni
  · with_reducible
      simpa only [originalCorrectionPairCompact, originalCorrectionPairChangedCompact,
        originalCorrectionPairCompactMap, Fin.twoCases_one, Matrix.cons_val_one,
        Matrix.cons_val_zero, pullbackUnitMap, Hom.pullbackToUnit] using hdi
  · with_reducible
      simpa only [originalCorrectionPairCompact, originalCorrectionPairChangedCompact,
        originalCorrectionPairCompactMap, Fin.twoCases_zero, Matrix.cons_val_zero,
        relativeCompactificationGraphLine, pullbackUnitMap, Hom.pullbackToUnit] using hbi

omit [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R]
  [IsAffine Y] [IsAffine A] [IsAffineHom dA]
  [IsClosedImmersion (z ≫ chart R 0)] haA hbAUnit in
/-- The same proved generic product is expressed in the literal finite-pair
wrappers. No ratio, norm, frame or generic section is reconstructed. -/
private theorem nativeCorrection_germ_wrapper :
    let π := ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))
    let q := boundaryLineProjection R
    let jA := chart R 0
    let T := pullback (a ≫ q) π
    let F := normProductMap π f (a ≫ q)
    let τ := retainedNormParameterMap π (a ≫ q) jA a
      (congrArg (fun k => a ≫ k) (chart_toSpec R 0).symm)
    let M := tensorLineBundle _ LA (dualLineBundle _ (relativeCompactificationGraphLine π jA))
    let cA := twistedIdealSection _ (relativeCompactificationGraphLine π jA) LA
      (idealInclusion (compactificationGraph π jA)) bA
    let L := pullbackLineBundle τ (dualLineBundle _ M)
    let nφ := sectionDualFunctional _ c.N c.nS
    let dφ := sectionDualFunctional _ c.N c.dS
    let aφ := pullbackUnitMap τ (sectionDualFunctional _ M aA)
    let cφ := pullbackUnitMap τ (sectionDualFunctional _ M cA)
    let C₀ := originalCorrectionPairCompact q π f jA a
    let c' := originalCorrectionPairCompactMap q π f jA (chart_toSpec R 0) a
    let f' := originalCorrectionPairFiniteMap q π f a
    let I : LineBundle (C₀ 0) := ⟨idealModule (compactificationGraph π jA),
      (relativeCompactificationGraphLine π jA).property⟩
    let MC : LineBundle (C₀ 0) := LA
    let MA := tensorLineBundle (C₀ 0) MC (dualLineBundle (C₀ 0) I)
    let aSC : SheafOfModules.unit (C₀ 0).ringCatSheaf ⟶ MA.val := aA
    let bSC : SheafOfModules.unit (C₀ 0).ringCatSheaf ⟶ MC.val := bA
    let cSC := twistedIdealSection (C₀ 0) I MC
      (idealInclusion (compactificationGraph π jA)) bSC
    let NC : LineBundle (C₀ 1) := dualLineBundle _ c.N
    let nSC : NC.val ⟶ SheafOfModules.unit (C₀ 1).ringCatSheaf := nφ
    let dSC : NC.val ⟶ SheafOfModules.unit (C₀ 1).ringCatSheaf := dφ
    let aT := Hom.pullbackToUnit (sectionDualFunctional (C₀ 0) MA aSC) (c' 0)
    let cT := Hom.pullbackToUnit (sectionDualFunctional (C₀ 0) MA cSC) (c' 0)
    let nT := Hom.pullbackToUnit nSC (c' 1)
    let dT := Hom.pullbackToUnit dSC (c' 1)
    ∀ [_hT : IsIntegral T] (hn : Mono nφ) (hd' : Mono dφ)
      (haM : Mono aφ) (hcM : Mono cφ)
      (haT : Mono aT) (hcT : Mono cT) (hnT : Mono nT) (hdT : Mono dT),
    let := hn
    let := hd'
    let := haM
    let := hcM
    let := haT
    let := hcT
    let := hnT
    let := hdT
    let := pullbackUnitMap_id_mono nφ
    let := pullbackUnitMap_id_mono dφ
    ∀ (W : T.Opens) [Nonempty W] (r : Γ(T, W)),
    T.germToFunctionField W r =
        genericFiberLineRatioNorm (𝟙 T) L aφ cφ *
          genericFiberLineRatioNorm F (pullbackLineBundle (𝟙 _) (dualLineBundle _ c.N))
            (pullbackUnitMap (𝟙 _) nφ) (pullbackUnitMap (𝟙 _) dφ) →
      T.germToFunctionField W r =
        genericFiberLineRatioNorm (f' 0)
            (pullbackLineBundle (c' 0) (dualLineBundle (C₀ 0) MA)) aT cT *
          genericFiberLineRatioNorm (f' 1) (pullbackLineBundle (c' 1) NC) nT dT := by
  dsimp only
  intro hT hn hd' haM hcM haT hcT hnT hdT W hW r hg
  with_reducible
    simpa only [originalCorrectionPairFiniteMap, originalCorrectionPairCompactMap,
      originalCorrectionPairCompact, originalCorrectionPairChangedCompact,
      Fin.twoCases_zero, Fin.twoCases_one,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      relativeCompactificationGraphLine, pullbackUnitMap, Hom.pullbackToUnit] using hg

omit [IsClosedImmersion (z ≫ chart R 0)] [IsAffineHom dA] in
include hret hcover hpairA hvY hpV hrA hinfty hpuncture in
/-- The concrete original cycle identity. Normalization facts are supplied only
inside the public proof; all finite-pair geometry is internal to this lemma. -/
private theorem nativeCorrection_originalPair_relation [Nonempty A]
    (hfree : ∀ i : ULift.{u} (Fin 2),
      let : Algebra (Polynomial R) Γ(pullback f (chart R i), ⊤) :=
        (scalarMap (pullback.snd f (chart R i))).toAlgebra
      Module.Free (Polynomial R) Γ(pullback f (chart R i), ⊤)) :
    let π := ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))
    let q := boundaryLineProjection R
    let jA := chart R 0
    let X₀ := lambdaSourceSite k t π jA
    let A₀ := psiSourceSite k t q a
    let Q := relativeTargetSite k t π (u ≫ jA)
    let j₀ := retainedProductInclusion (jA ≫ π) π (u ≫ jA)
    let j₁ := retainedProductInclusion (a ≫ q) (f ≫ π) v
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
    let : SmoothOfRelativeDimension 1 (j₀ ≫ pullback.fst (jA ≫ π) π) :=
      retainedProduct_smooth (jA ≫ π) π (u ≫ jA)
    let : SmoothOfRelativeDimension 1 (j₁ ≫ pullback.fst (a ≫ q) (f ≫ π)) :=
      retainedProduct_smooth (a ≫ q) (f ≫ π) v
    let hcA := lambdaBoundary_retained_cover π jA z dA (u ≫ jA)
      (correction_target_small_cover jA dA z u hinfty hpuncture)
    let hcN := psiBoundary_retained_cover q (f ≫ π) j p hq a z s hs d v hcover
    let hbA := retainedProduct_structure (jA ≫ π) π (u ≫ jA) t
    let hbN := retainedProduct_structure_factor (a ≫ q) (f ≫ π) v t pV Q.hom
      (correctionSmallTarget_structure t π f j jA p hret u v vY hvY pV hpV)
    let T := pullback (a ≫ q) π
    let F := normProductMap π f (a ≫ q)
    let τ := retainedNormParameterMap π (a ≫ q) jA a
      (congrArg (fun k => a ≫ k) (chart_toSpec R 0).symm)
    let cA := twistedIdealSection _ (relativeCompactificationGraphLine π jA) LA
      (idealInclusion (compactificationGraph π jA)) bA
    let L := pullbackLineBundle τ (dualLineBundle _ M)
    let nφ := sectionDualFunctional _ c.N c.nS
    let dφ := sectionDualFunctional _ c.N c.dS
    let aφ := pullbackUnitMap τ (sectionDualFunctional _ M aA)
    let cφ := pullbackUnitMap τ (sectionDualFunctional _ M cA)
    let W := functionalNormProductUnitDomain F (dualLineBundle _ c.N)
      (dualLineBundle _ c.N) nφ dφ L L aφ cφ
    let jT₁ := retainedProductInclusion (a ≫ q) π (u ≫ jA)
    let gT₁ := pullback.snd (a ≫ q) ((u ≫ jA) ≫ π)
    let : IsAffine (retainedProduct (a ≫ q) π (u ≫ jA)) :=
      retainedProduct_affine (a ≫ q) π (u ≫ jA)
    let : SmoothOfRelativeDimension 1 (jT₁ ≫ pullback.fst (a ≫ q) π) :=
      retainedProduct_smooth (a ≫ q) π (u ≫ jA)
    let hbT₁ := retainedProduct_structure (a ≫ q) π (u ≫ jA) t
    ∀ [hT : IsIntegral T] [hTN : IsNoetherian T]
      [hn : Mono nφ] [hd' : Mono dφ] [haφ : Mono aφ] [hcφ : Mono cφ],
    let : Nonempty W := functionalNormProductUnitDomain_nonempty F (dualLineBundle _ c.N)
      (dualLineBundle _ c.N) nφ dφ L L aφ cφ
    ∀ (r : Γ(T, W)) (hr : IsUnit r)
      (hW₁ : (Set.range jT₁)ᶜ ⊆ (W : Set T)),
    T.germToFunctionField W r = genericFiberLineRatioNorm (𝟙 T) L aφ cφ *
      genericFiberLineRatioNorm F (dualLineBundle _ c.N) nφ dφ →
    ((show Cor.mk A₀ ⟶ Cor.mk X₀ from (Cor.graphFunctor k).map
        (originalCorrectionPairSiteMap t q π jA (chart_toSpec R 0) a 0)) ≫
      (Cor.boundarySection X₀ Q (fullBoundaryProductMap π jA dA z)
        (pullback.fst (jA ≫ π) π) j₀ M hcA
        (pullback.snd (jA ≫ π) ((u ≫ jA) ≫ π)) hbA aA -
      Cor.boundarySection X₀ Q (fullBoundaryProductMap π jA dA z)
        (pullback.fst (jA ≫ π) π) j₀ LA hcA
        (pullback.snd (jA ≫ π) ((u ≫ jA) ≫ π)) hbA bA)) -
      (Cor.boundarySection A₀ Q (psiBoundaryInclusion q (f ≫ π) j p hq a z s hs d)
          (pullback.fst (a ≫ q) (f ≫ π)) j₁ c.N hcN
          (pullback.snd (a ≫ q) (v ≫ (f ≫ π)) ≫ pV) hbN c.dS -
        Cor.boundarySection A₀ Q (psiBoundaryInclusion q (f ≫ π) j p hq a z s hs d)
          (pullback.fst (a ≫ q) (f ≫ π)) j₁ c.N hcN
          (pullback.snd (a ≫ q) (v ≫ (f ≫ π)) ≫ pV) hbN c.nS) -
      (show Cor.mk A₀ ⟶ Cor.mk Q from (Cor.graphFunctor k).map
        (correctionSmallParameterMap t q π jA (chart_toSpec R 0) a u rA hrA)) =
      PrincipalOrderCorrespondence.correspondence (X := A₀) (Y := Q)
        (pullback.fst (a ≫ q) π) jT₁ W hW₁ r hr gT₁ hbT₁ := by
  classical
  dsimp only
  intro hT hTN hn hd' haφ hcφ r hr hW₁ hg
  let π := ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))
  let q := boundaryLineProjection R
  let jA := chart R 0
  let X₀ := lambdaSourceSite k t π jA
  let A₀ := psiSourceSite k t q a
  let Q := relativeTargetSite k t π (u ≫ jA)
  let : IsAffine X₀.left := inferInstanceAs (IsAffine (Spec (.of (Polynomial R))))
  let : IsAffine A₀.left := ‹IsAffine A›
  let : IsIso (pullbackSectionMap (fullBoundaryProductMap π jA dA z) aA) := haA
  let := c.n_unit
  let := c.d_unit
  let : IsAffine (retainedProduct (jA ≫ π) π (u ≫ jA)) :=
    retainedProduct_affine (jA ≫ π) π (u ≫ jA)
  let : IsAffine (retainedProduct (a ≫ q) (f ≫ π) v) :=
    retainedProduct_affine (a ≫ q) (f ≫ π) v
  let : SmoothOfRelativeDimension 1
      (retainedProductInclusion (jA ≫ π) π (u ≫ jA) ≫ pullback.fst (jA ≫ π) π) :=
    retainedProduct_smooth (jA ≫ π) π (u ≫ jA)
  let : SmoothOfRelativeDimension 1
      (retainedProductInclusion (a ≫ q) (f ≫ π) v ≫ pullback.fst (a ≫ q) (f ≫ π)) :=
    retainedProduct_smooth (a ≫ q) (f ≫ π) v
  let T := pullback (a ≫ q) π
  let F := normProductMap π f (a ≫ q)
  let τ := retainedNormParameterMap π (a ≫ q) jA a
    (congrArg (fun k => a ≫ k) (chart_toSpec R 0).symm)
  let M := tensorLineBundle _ LA (dualLineBundle _ (relativeCompactificationGraphLine π jA))
  let cA := twistedIdealSection _ (relativeCompactificationGraphLine π jA) LA
    (idealInclusion (compactificationGraph π jA)) bA
  let L := pullbackLineBundle τ (dualLineBundle _ M)
  let nφ := sectionDualFunctional _ c.N c.nS
  let dφ := sectionDualFunctional _ c.N c.dS
  let aφ := pullbackUnitMap τ (sectionDualFunctional _ M aA)
  let cφ := pullbackUnitMap τ (sectionDualFunctional _ M cA)
  let W := functionalNormProductUnitDomain F (dualLineBundle _ c.N)
    (dualLineBundle _ c.N) nφ dφ L L aφ cφ
  let jT := retainedProductInclusion (a ≫ q) π jA
  let jT₁ := retainedProductInclusion (a ≫ q) π (u ≫ jA)
  let gT₁ : retainedProduct (a ≫ q) π (u ≫ jA) ⟶ Q.left :=
    pullback.snd (a ≫ q) ((u ≫ jA) ≫ π)
  have hbT₁ : jT₁ ≫ pullback.fst (a ≫ q) π ≫ A₀.hom = gT₁ ≫ Q.hom :=
    retainedProduct_structure (a ≫ q) π (u ≫ jA) t
  let := hT
  let := hTN
  let := hn
  let := hd'
  let := haφ
  let := hcφ
  let : Nonempty W := functionalNormProductUnitDomain_nonempty F (dualLineBundle _ c.N)
    (dualLineBundle _ c.N) nφ dφ L L aφ cφ
  let O := originalCorrectionPairSite t q π jA a
  let α := originalCorrectionPairSiteMap t q π jA (chart_toSpec R 0) a
  let C₀ := originalCorrectionPairCompact q π f jA a
  let U₀ := originalCorrectionPairRetained q π f j jA a
  let B₀ := originalCorrectionPairInfinity q π f jA a d dA
  let C' := originalCorrectionPairChangedCompact q π f a
  let U' := originalCorrectionPairChangedRetained q π f j jA a
  let B' := originalCorrectionPairChangedInfinity q π f a d dA
  let f' := originalCorrectionPairFiniteMap q π f a
  let i := originalCorrectionPairChangedInfinityInclusion q π f a d dA
  let j' := originalCorrectionPairChangedInclusion q π f j jA a
  let w := originalCorrectionPairRetainedFiniteMap q π f j jA p hret a
  let q₀ : ∀ i, C₀ i ⟶ (O i).left := originalCorrectionPairProjection q π f jA a
  let i₀ := originalCorrectionPairInfinityInclusion q π f jA a d dA
  let j₀ := originalCorrectionPairRetainedInclusion q π f j jA a
  let c' := originalCorrectionPairCompactMap q π f jA (chart_toSpec R 0) a
  let v' := originalCorrectionPairRetainedMap q π f j jA (chart_toSpec R 0) a
  let g : retainedProduct (a ≫ q) π jA ⟶ X₀.left := pullback.snd (a ≫ q) (jA ≫ π)
  let g₀ : ∀ i, U₀ i ⟶ X₀.left := originalCorrectionPairTargetMap q π f j jA p a
  let U₁ := originalCorrectionPairSmallRetained q π f jA a u v
  let B₁ := originalCorrectionPairFullBoundary q π f jA a d dA z
  let i₁ := originalCorrectionPairFullBoundaryInclusion q π f j jA p a d dA z s hq hs
  let j₁ := originalCorrectionPairSmallInclusion q π f jA a u v
  let v₁ := originalCorrectionPairSmallMap q π f j jA a u v vY hvY
  let g₁ : ∀ i, U₁ i ⟶ Q.left := originalCorrectionPairSmallTargetMap q π f jA a u v pV
  let vT := retainedSubopenMap (a ≫ q) π jA (u ≫ jA) u rfl
  let rsite := correctionSmallParameterMap t q π jA (chart_toSpec R 0) a u rA hrA
  let usite : Q ⟶ X₀ := SmoothSite.homMk u (by
    change u ≫ ((jA ≫ π) ≫ t) = ((u ≫ jA) ≫ π) ≫ t
    simp only [Category.assoc])
  let : IsOpenImmersion usite.left := inferInstanceAs (IsOpenImmersion u)
  let : IsAffine (retainedProduct (a ≫ q) π jA) := retainedProduct_affine (a ≫ q) π jA
  let : SmoothOfRelativeDimension 1 (jT ≫ pullback.fst (a ≫ q) π) :=
    retainedProduct_smooth (a ≫ q) π jA
  let : IsAffine (retainedProduct (a ≫ q) π (u ≫ jA)) :=
    retainedProduct_affine (a ≫ q) π (u ≫ jA)
  let : SmoothOfRelativeDimension 1 (jT₁ ≫ pullback.fst (a ≫ q) π) :=
    retainedProduct_smooth (a ≫ q) π (u ≫ jA)
  have hvT : vT ≫ jT = jT₁ := retainedSubopenMap_inclusion (a ≫ q) π jA (u ≫ jA) u rfl
  have hW : (Set.range jT)ᶜ ⊆ (W : Set T) := by
    intro x hx
    apply hW₁
    rintro ⟨y, hy⟩
    exact hx ⟨vT y, (congrArg (fun f => f y) hvT).trans hy⟩
  have hbase : (jT ≫ pullback.fst (a ≫ q) π) ≫ A₀.hom = g ≫ X₀.hom :=
    retainedProduct_structure (a ≫ q) π jA t
  have hpbase : p ≫ ((jA ≫ π) ≫ t) = (j ≫ (f ≫ π)) ≫ t := by
    simpa only [Category.assoc] using congrArg (fun f => f ≫ π ≫ t) hret.symm
  have hb₀ : ∀ i, (j₀ i ≫ q₀ i) ≫ (O i).hom = g₀ i ≫ X₀.hom := by
    intro i
    fin_cases i
    · exact retainedProduct_structure (jA ≫ π) π jA t
    · exact retainedProduct_structure_factor (a ≫ q) (f ≫ π) j t p X₀.hom hpbase
  have hb₁ : ∀ i, (j₁ i ≫ q₀ i) ≫ (O i).hom = g₁ i ≫ Q.hom := by
    intro i
    fin_cases i
    · exact retainedProduct_structure (jA ≫ π) π (u ≫ jA) t
    · exact retainedProduct_structure_factor (a ≫ q) (f ≫ π) v t pV Q.hom
        (correctionSmallTarget_structure t π f j jA p hret u v vY hvY pV hpV)
  have hguT₁ : gT₁ ≫ usite.left = vT ≫ g := by
    simp only [usite, SmoothSite.homMk_left, vT, g,
      retainedSubopenMap_snd, gT₁]
  have hru : rsite ≫ usite = α 0 ≫ 𝟙 X₀ := by
    ext1
    exact hrA
  let (x : T) : IsIntegrallyClosed (T.presheaf.stalk x) :=
    (nativeCorrectionParameter_normal R a).2.2 x
  have hnormal : ∀ (O : T.Opens), IsAffineOpen O → Nonempty O →
      IsIntegrallyClosed Γ(T, O) := by
    intro O hO hne
    let := hne
    exact T.isIntegrallyClosed_sections_of_isAffineOpen O hO
  have hcharts : ∀ x : ProjectiveSpace R (ULift.{u} (Fin 2)),
      ∃ i, x ∈ Set.range (chart R i) := by
    intro x
    have hx : x ∈ (⨆ i, (chart R i).opensRange) := by
      rw [iSup_chart_opensRange]
      trivial
    exact Opens.mem_iSup.mp hx
  have hfree' := originalCorrectionPairFiniteMap_free q π f a
    (fun _ : ULift.{u} (Fin 2) => CommRingCat.of (Polynomial R)) (chart R) hcharts hfree
  obtain ⟨haInf, hbInf, hIInf, hcInf, hnInf, hdInf, haTInf, hcTInf, hbTInf, hnTInf, hdTInf⟩ :=
    nativeCorrection_infinity_units R f j p hq a z s hs H e ha d hd c dA hdA
      LA aA bA hpairA
  let := haInf
  let := hbInf
  let := hIInf
  let := hcInf
  let := hnInf
  let := hdInf
  let := haTInf
  let := hcTInf
  let := hbTInf
  let := hnTInf
  let := hdTInf
  let : IsIso (pullbackSectionMap (i₁ 0) aA) := haA
  let : IsIso (pullbackSectionMap (i₁ 0) bA) := hbAUnit
  let : IsIso (pullbackSectionMap (i₁ 1) c.nS) := c.n_unit
  let : IsIso (pullbackSectionMap (i₁ 1) c.dS) := c.d_unit
  let : IsIso ((Modules.pullback (i₁ 1)).map nφ) :=
    sectionDualFunctional_pullback_map_isIso (i₁ 1) c.N c.nS
  let : IsIso ((Modules.pullback (i₁ 1)).map dφ) :=
    sectionDualFunctional_pullback_map_isIso (i₁ 1) c.N c.dS
  let := pullbackUnitMap_id_mono nφ
  let := pullbackUnitMap_id_mono dφ
  have hg' : T.germToFunctionField W r =
      genericFiberLineRatioNorm (𝟙 T) L aφ cφ *
        genericFiberLineRatioNorm F (pullbackLineBundle (𝟙 _) (dualLineBundle _ c.N))
          (pullbackUnitMap (𝟙 _) nφ) (pullbackUnitMap (𝟙 _) dφ) := by
    rw [genericFiberLineRatioNorm_pullback_id F (dualLineBundle _ c.N) nφ dφ]
    exact hg
  have hc := originalCorrectionPair_changedInfinity_cover q π f j jA a d dA s v
    vY hvY hinfty hcover
  have hc₀ := originalCorrectionPair_infinity_cover q π f j jA a d dA s v
    vY hvY hinfty hcover
  have hc₁ := originalCorrectionPair_fullBoundary_cover q π f j jA p a d dA z s hq hs
    u v hinfty hpuncture hcover
  let : IsClosedImmersion (compactificationGraph π jA) := by
    dsimp only [compactificationGraph]
    infer_instance
  let γ : (O 0).left ⟶ C₀ 0 := compactificationGraph π jA
  let δ : (O 0).left ⟶ U₀ 0 := originalCorrectionRetainedGraph π jA
  let φ : O 0 ⟶ X₀ := 𝟙 X₀
  have hδ : δ ≫ j₀ 0 = γ := originalCorrectionRetainedGraph_inclusion π jA
  have hproj : γ ≫ q₀ 0 = 𝟙 (O 0).left := by
    change compactificationGraph π jA ≫ pullback.fst (jA ≫ π) π =
      𝟙 (Spec (.of (Polynomial R)))
    simp only [compactificationGraph, pullback.lift_fst]
  have hφ : δ ≫ g₀ 0 = φ.left := originalCorrectionRetainedGraph_snd π jA
  let qT : T ⟶ A₀.left := pullback.fst (a ≫ q) π
  have hI : IsLocallyRankOne (C₀ 0) (idealModule (compactificationGraph π jA)) :=
    (relativeCompactificationGraphLine π jA).property
  let NC : LineBundle (C₀ 1) := dualLineBundle _ c.N
  have Hp : ∀ t, IsPullback (v' t) (j' t ≫ (f' t ≫ qT))
      (j₀ t ≫ q₀ t) (α t).left :=
    originalCorrectionPairRetainedMap_isPullback q π f j jA (chart_toSpec R 0) a
  let MC : LineBundle (C₀ 0) := LA
  let aSC : SheafOfModules.unit (C₀ 0).ringCatSheaf ⟶
      (tensorLineBundle (C₀ 0) MC
        (dualLineBundle (C₀ 0) ⟨idealModule γ, hI⟩)).val := aA
  let bSC : SheafOfModules.unit (C₀ 0).ringCatSheaf ⟶ MC.val := bA
  let cSC := twistedIdealSection (C₀ 0) ⟨idealModule γ, hI⟩ MC (idealInclusion γ) bSC
  have hcSC : IsIso (pullbackSectionMap (i₀ 0) cSC) := hcInf
  let nSC : NC.val ⟶ SheafOfModules.unit (C₀ 1).ringCatSheaf := nφ
  let dSC : NC.val ⟶ SheafOfModules.unit (C₀ 1).ringCatSheaf := dφ
  have haSmall : IsIso (pullbackSectionMap (i₁ 0) aSC) := haA
  have hbSmall : IsIso (pullbackSectionMap (i₁ 0) bSC) := hbAUnit
  have hgu₁ : ∀ i, g₁ i ≫ usite.left = v₁ i ≫ g₀ i :=
    originalCorrectionPairSmallTargetMap_comp q π f j jA p a u v vY hvY pV hpV
  obtain ⟨haMono, hcMono, hnMono, hdMono, haUnit, hcUnit, hnUnit, hdUnit, hbUnit⟩ :=
    nativeCorrection_functional_wrapper_properties R f j p hq a z s hs H e ha d hd c
      dA LA aA bA hn hd' haφ hcφ haTInf hcTInf hnTInf hdTInf hbTInf
  with_reducible
    have hgExact := nativeCorrection_germ_wrapper R f j p hq a z s hs H e ha d hd c
      LA aA bA hn hd' haφ hcφ haMono hcMono hnMono hdMono W r hg'
  with_reducible
    have hcor : @Eq (Cor.mk A₀ ⟶ Cor.mk Q) _ _ :=
      @Cor.originalPair_norm_product_marked_middle k inferInstance
        A₀ X₀ inferInstance O (fun _ => inferInstance) α (fun _ => inferInstance)
        T (retainedProduct (a ≫ q) π jA) hT hTN
        qT inferInstance jT inferInstance inferInstance inferInstance
        C' U' B' C₀ U₀ B₀ f' (fun _ => inferInstance)
        i j' (fun _ => inferInstance) (fun _ => inferInstance) (fun _ => inferInstance)
        w (originalCorrectionPairRetainedFiniteMap_inclusion q π f j jA p hret a)
        q₀ (fun _ => inferInstance) i₀ j₀
        (fun _ => inferInstance) (fun _ => inferInstance) (fun _ => inferInstance)
        c' v'
        (originalCorrectionPairRetainedMap_inclusion q π f j jA (chart_toSpec R 0) a)
        Hp
        γ inferInstance
        hI
        δ hδ hproj MC aSC bSC
        inferInstance inferInstance inferInstance
        hcSC
        NC nSC dSC inferInstance inferInstance hc hc₀ g hbase g₀ hb₀
        (originalCorrectionPairRetainedMap_target q π f j jA p hret a (chart_toSpec R 0))
        φ hφ hnormal hfree' W inferInstance hW r hr Q usite inferInstance
        U₁ B₁ i₁ j₁ (fun _ => inferInstance) (fun _ => inferInstance) (fun _ => inferInstance)
        v₁ (originalCorrectionPairSmallMap_inclusion q π f j jA a u v vY hvY) hc₁
        haSmall hbSmall inferInstance inferInstance g₁ hb₁
        hgu₁
        rsite hru (retainedProduct (a ≫ q) π (u ≫ jA)) jT₁
        inferInstance inferInstance inferInstance vT hvT hW₁ gT₁ hbT₁ hguT₁
        haMono hcMono hnMono hdMono
        haUnit hcUnit hnUnit hdUnit hbUnit hgExact
  have hmiddle := Cor.nativeCorrection_canonical_to_middle (R := R) (f := f) (j := j)
    (p := p) (hq := hq) (hret := hret) (a := a) (z := z) (s := s) (hs := hs)
    (H := H) (e := e) (ha := ha) (d := d) (hd := hd) (c := c) (v := v)
    (hcover := hcover) (dA := dA) (LA := LA) (aA := aA) (bA := bA)
    (t := t) (u := u) (vY := vY) (hvY := hvY) (pV := pV) (hpV := hpV)
    (rA := rA) (hrA := hrA) (hinfty := hinfty) (hpuncture := hpuncture)
  exact hmiddle.trans hcor

include hret hcover hbI hbE hFa hFb hpairA hPst hvY hpV hrA hinfty hpuncture in
/-- The actual target pair acts as the original correction pair plus the actual
small graph. All normalization data are constructed from these same sections.
The empty parameter case uses the zero correspondence, not a nonempty premise. -/
theorem transfer_nativeCorrection_originalPairs
    (hfree : ∀ i : ULift.{u} (Fin 2),
      let : Algebra (Polynomial R) Γ(pullback f (chart R i), ⊤) :=
        (scalarMap (pullback.snd f (chart R i))).toAlgebra
      Module.Free (Polynomial R) Γ(pullback f (chart R i), ⊤)) :
    let π := ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))
    let q := boundaryLineProjection R
    let jA := chart R 0
    let X₀ := lambdaSourceSite k t π jA
    let A₀ := psiSourceSite k t q a
    let Q := relativeTargetSite k t π (u ≫ jA)
    let j₀ := retainedProductInclusion (jA ≫ π) π (u ≫ jA)
    let j₁ := retainedProductInclusion (a ≫ q) (f ≫ π) v
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
    let : SmoothOfRelativeDimension 1 (j₀ ≫ pullback.fst (jA ≫ π) π) :=
      retainedProduct_smooth (jA ≫ π) π (u ≫ jA)
    let : SmoothOfRelativeDimension 1 (j₁ ≫ pullback.fst (a ≫ q) (f ≫ π)) :=
      retainedProduct_smooth (a ≫ q) (f ≫ π) v
    let hcA := lambdaBoundary_retained_cover π jA z dA (u ≫ jA)
      (correction_target_small_cover jA dA z u hinfty hpuncture)
    let hcN := psiBoundary_retained_cover q (f ≫ π) j p hq a z s hs d v hcover
    let hbA := retainedProduct_structure (jA ≫ π) π (u ≫ jA) t
    let hbN := retainedProduct_structure_factor (a ≫ q) (f ≫ π) v t pV Q.hom
      (correctionSmallTarget_structure t π f j jA p hret u v vY hvY pV hpV)
    Pst.transfer ((Cor.graphFunctor k).map
        (originalCorrectionPairSiteMap t q π jA (chart_toSpec R 0) a 0) ≫
      (Cor.boundarySection X₀ Q (fullBoundaryProductMap π jA dA z)
        (pullback.fst (jA ≫ π) π) j₀ M hcA
        (pullback.snd (jA ≫ π) ((u ≫ jA) ≫ π)) hbA aA -
      Cor.boundarySection X₀ Q (fullBoundaryProductMap π jA dA z)
        (pullback.fst (jA ≫ π) π) j₀ LA hcA
        (pullback.snd (jA ≫ π) ((u ≫ jA) ≫ π)) hbA bA)) =
      Pst.transfer
        (Cor.boundarySection A₀ Q (psiBoundaryInclusion q (f ≫ π) j p hq a z s hs d)
          (pullback.fst (a ≫ q) (f ≫ π)) j₁ c.N hcN
          (pullback.snd (a ≫ q) (v ≫ (f ≫ π)) ≫ pV) hbN c.dS -
        Cor.boundarySection A₀ Q (psiBoundaryInclusion q (f ≫ π) j p hq a z s hs d)
          (pullback.fst (a ≫ q) (f ≫ π)) j₁ c.N hcN
          (pullback.snd (a ≫ q) (v ≫ (f ≫ π)) ≫ pV) hbN c.nS) +
      Pst.transfer (show Cor.mk A₀ ⟶ Cor.mk Q from (Cor.graphFunctor k).map
        (correctionSmallParameterMap t q π jA (chart_toSpec R 0) a u rA hrA)) := by
  classical
  let π := ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))
  let q := boundaryLineProjection R
  let jA := chart R 0
  let X₀ := lambdaSourceSite k t π jA
  let A₀ := psiSourceSite k t q a
  let Q := relativeTargetSite k t π (u ≫ jA)
  let : IsAffine X₀.left := inferInstanceAs (IsAffine (Spec (.of (Polynomial R))))
  let : IsAffine A₀.left := ‹IsAffine A›
  let : IsIso (pullbackSectionMap (fullBoundaryProductMap π jA dA z) aA) := haA
  let := c.n_unit
  let := c.d_unit
  let : IsAffine (retainedProduct (jA ≫ π) π (u ≫ jA)) :=
    retainedProduct_affine (jA ≫ π) π (u ≫ jA)
  let : IsAffine (retainedProduct (a ≫ q) (f ≫ π) v) :=
    retainedProduct_affine (a ≫ q) (f ≫ π) v
  let : SmoothOfRelativeDimension 1
      (retainedProductInclusion (jA ≫ π) π (u ≫ jA) ≫ pullback.fst (jA ≫ π) π) :=
    retainedProduct_smooth (jA ≫ π) π (u ≫ jA)
  let : SmoothOfRelativeDimension 1
      (retainedProductInclusion (a ≫ q) (f ≫ π) v ≫ pullback.fst (a ≫ q) (f ≫ π)) :=
    retainedProduct_smooth (a ≫ q) (f ≫ π) v
  by_cases hA : Nonempty A
  swap
  · let : IsEmpty A := not_nonempty_iff.mp hA
    let : IsEmpty (Cor.mk A₀).toSmoothSite.left := ‹IsEmpty A›
    let : IsEmpty ((Cor.graphFunctor k).obj A₀).toSmoothSite.left := ‹IsEmpty A›
    simp only [Cor.hom_eq_zero_of_isEmpty_source k, transfer_zero, zero_add]
  let := hA
  let : IsIntegral A := isIntegral_of_isOpenImmersion a
  let : IsIntegral A₀.left := ‹IsIntegral A›
  let T := pullback (a ≫ q) π
  let F := normProductMap π f (a ≫ q)
  let τ := retainedNormParameterMap π (a ≫ q) jA a
    (congrArg (fun k => a ≫ k) (chart_toSpec R 0).symm)
  let M := tensorLineBundle _ LA (dualLineBundle _ (relativeCompactificationGraphLine π jA))
  let cA := twistedIdealSection _ (relativeCompactificationGraphLine π jA) LA
    (idealInclusion (compactificationGraph π jA)) bA
  let L := pullbackLineBundle τ (dualLineBundle _ M)
  let nφ := sectionDualFunctional _ c.N c.nS
  let dφ := sectionDualFunctional _ c.N c.dS
  let aφ := pullbackUnitMap τ (sectionDualFunctional _ M aA)
  let cφ := pullbackUnitMap τ (sectionDualFunctional _ M cA)
  let W := functionalNormProductUnitDomain F (dualLineBundle _ c.N)
    (dualLineBundle _ c.N) nφ dφ L L aφ cφ
  let jT₁ := retainedProductInclusion (a ≫ q) π (u ≫ jA)
  let gT₁ := pullback.snd (a ≫ q) ((u ≫ jA) ≫ π)
  have hbT₁ : jT₁ ≫ pullback.fst (a ≫ q) π ≫ A₀.hom = gT₁ ≫ Q.hom :=
    retainedProduct_structure (a ≫ q) π (u ≫ jA) t
  obtain ⟨hT, hTN, hn, hd', haφ, hcφ, r, β, _hβ, hr, hbd, hg, _hb, hzero⟩ :=
    exists_nativeCorrectionPrincipalAction_zero R f j p hq hret a z s hs H hsK e ha
      d hd c v hcover dA hdA bI hbI bE hbE LA aA bA iA hFa hFb hpairA
      Pst hPst t Q u hinfty hpuncture gT₁ hbT₁ hfree
  let := hT
  let := hTN
  let := hn
  let := hd'
  let := haφ
  let := hcφ
  let : Nonempty W := functionalNormProductUnitDomain_nonempty F (dualLineBundle _ c.N)
    (dualLineBundle _ c.N) nφ dφ L L aφ cφ
  have hW₁ : (Set.range jT₁)ᶜ ⊆ (W : Set T) :=
    PrincipalOrderCorrespondence.canonical_boundary_cover jT₁ W β hbd
  have hcor := nativeCorrection_originalPair_relation R f j p hq hret a z s hs H e ha
    d hd c v hcover dA hdA LA aA bA hpairA t u vY hvY pV hpV rA hrA hinfty hpuncture
    hfree r hr hW₁ hg
  have he := congrArg (fun ξ : Cor.mk A₀ ⟶ Cor.mk Q => Pst.transfer ξ) hcor
  rw [transfer_sub, transfer_sub, sub_sub] at he
  exact sub_eq_zero.mp (he.trans hzero)

include hret hcover hbI hbE hFa hFb hpairA hPst hvY hpV hrA hinfty hpuncture in
/-- The correction in the actual native comparison is the literal `psi` of the
same original section tuple, postcomposed with its actual small-target map. -/
theorem transfer_nativeCorrection_originalPsi
    {B : Scheme.{u}} [IsAffine B]
    (α : B ⟶ Y) [Smooth α] (β : B ⟶ A) [Flat β] (h : α ≫ p = β ≫ a)
    (φ : B ⟶ V) (hφ : φ ≫ v = α ≫ j)
    (hfree : ∀ i : ULift.{u} (Fin 2),
      let : Algebra (Polynomial R) Γ(pullback f (chart R i), ⊤) :=
        (scalarMap (pullback.snd f (chart R i))).toAlgebra
      Module.Free (Polynomial R) Γ(pullback f (chart R i), ⊤)) :
    let π := ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))
    let q := boundaryLineProjection R
    let jA := chart R 0
    let X₀ := lambdaSourceSite k t π jA
    let A₀ := psiSourceSite k t q a
    let Q := relativeTargetSite k t π (u ≫ jA)
    let j₀ := retainedProductInclusion (jA ≫ π) π (u ≫ jA)
    let M := tensorLineBundle _ LA (dualLineBundle _ (relativeCompactificationGraphLine π jA))
    let : IsIso (pullbackSectionMap (fullBoundaryProductMap π jA dA z) aA) := haA
    let : IsAffine X₀.left := inferInstanceAs (IsAffine (Spec (.of (Polynomial R))))
    let : IsAffine (retainedProduct (jA ≫ π) π (u ≫ jA)) :=
      retainedProduct_affine (jA ≫ π) π (u ≫ jA)
    let : SmoothOfRelativeDimension 1 (j₀ ≫ pullback.fst (jA ≫ π) π) :=
      retainedProduct_smooth (jA ≫ π) π (u ≫ jA)
    let hcA := lambdaBoundary_retained_cover π jA z dA (u ≫ jA)
      (correction_target_small_cover jA dA z u hinfty hpuncture)
    let hbA := retainedProduct_structure (jA ≫ π) π (u ≫ jA) t
    Pst.transfer ((Cor.graphFunctor k).map
        (originalCorrectionPairSiteMap t q π jA (chart_toSpec R 0) a 0) ≫
      (Cor.boundarySection X₀ Q (fullBoundaryProductMap π jA dA z)
        (pullback.fst (jA ≫ π) π) j₀ M hcA
        (pullback.snd (jA ≫ π) ((u ≫ jA) ≫ π)) hbA aA -
      Cor.boundarySection X₀ Q (fullBoundaryProductMap π jA dA z)
        (pullback.fst (jA ≫ π) π) j₀ LA hcA
        (pullback.snd (jA ≫ π) ((u ≫ jA) ≫ π)) hbA bA)) =
      Pst.transfer (show Cor.mk A₀ ⟶ Cor.mk Q from
        (BoundarySectionData.toData k t q (f ≫ π) j p hq a α β h
        z s hs H e ha d hd c v hcover φ hφ).psi ≫
          (Cor.graphFunctor k).map
            (correctionSmallTargetMap t π f j jA p hret u v vY hvY pV hpV)) +
      Pst.transfer (show Cor.mk A₀ ⟶ Cor.mk Q from (Cor.graphFunctor k).map
        (correctionSmallParameterMap t q π jA (chart_toSpec R 0) a u rA hrA)) := by
  let π := ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))
  let q := boundaryLineProjection R
  let jA := chart R 0
  let Q := relativeTargetSite k t π (u ≫ jA)
  have hact := transfer_nativeCorrection_originalPairs R f j p hq hret a z s hs H hsK e ha
    d hd c v hcover dA hdA bI hbI bE hbE LA aA bA iA hFa hFb hpairA
    Pst hPst t u vY hvY pV hpV rA hrA hinfty hpuncture hfree
  have hpsi := BoundarySectionData.psi_comp_graph_dictionary k t q (f ≫ π) j p hq
    a α β h z s hs H e ha d hd c v hcover φ hφ Q
    (correctionSmallTargetMap t π f j jA p hret u v vY hvY pV hpV)
  dsimp only at hact hpsi ⊢
  rw [hpsi]
  exact hact

end Motivic.PresheafWithTransfers
