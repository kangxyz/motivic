/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.Presheaf.Actions.Pencils.NativeSectionPairTransferAction
public import Motivic.Transfers.Presheaf.Actions.Pencils.NativeOriginalPairTransferAction
public import Motivic.Transfers.Presheaf.Actions.Pencils.NativeOriginalComponentActions
public import Motivic.Transfers.Presheaf.Actions.Pencils.OriginalTargetLambda
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Norm.OriginalNormParameterTargetMap
/-! # Canonical action types for the unchanged native section pair

This conversion retains the original sections and maps and uses the same
smoothness instance as the checked correspondence identity.
-/
open _root_.AlgebraicGeometry.Scheme (SmoothSite)

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Scheme Scheme.Hom Scheme.Modules Scheme.Modules.Invertible RelativeProjectiveLine
open Scheme.RelativeAffineLineEtaleCompactification Scheme.RelativeCurvePencil
open AlgebraicGeometry.FiniteSchemeNormBaseChange
universe u w

namespace Motivic.PresheafWithTransfers
open Motivic.Cor

attribute [local instance] Cor.instSmoothOfSmoothOfRelativeDimensionOfNatNat

variable (R₀ : Type u) [CommRing R₀] [IsDomain R₀] [IsIntegrallyClosed R₀]
  [IsNoetherianRing R₀] {Y₀ : Scheme.{u}} [IsAffine Y₀]
  (p₀ : Y₀ ⟶ Spec (.of (Polynomial R₀))) [Etale p₀] [QuasiCompact p₀] [IsSeparated p₀]
  (O₀ : (Spec (.of R₀)).Opens) [IsAffine O₀.toScheme]
  (V₀ : (Spec Γ(O₀.toScheme, ⊤)).Opens) [IsAffine V₀.toScheme]

variable (R : Type u) [CommRing R]

variable {A Z C D V : Scheme.{u}} [IsAffine A] [IsAffine V]
  [SmoothOfRelativeDimension 1 (boundaryLineProjection R)] [SmoothOfRelativeDimension 1 ((chart R
    0) ≫ (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))))]
  (f : C ⟶ (ProjectiveSpace R (ULift.{u} (Fin 2))))
  [IsProper (f ≫ ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))] (j : (finalOriginalSource R₀ p₀
    O₀ V₀) ⟶ C) [IsOpenImmersion j]
  [SmoothOfRelativeDimension 1 (j ≫ (f ≫ (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))))]
  (p : (finalOriginalSource R₀ p₀ O₀ V₀) ⟶ (Spec (CommRingCat.of (Polynomial R)))) [Flat p] (hq
    : j ≫ (f ≫
    (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))) = p ≫ (boundaryLineProjection R))
  (hret : j ≫ f = p ≫ (chart R 0))
  (a : A ⟶ (Spec (CommRingCat.of (Polynomial R)))) [IsOpenImmersion a]
  (z : Z ⟶ (Spec (CommRingCat.of (Polynomial R))))
  (s : Z ⟶ (finalOriginalSource R₀ p₀ O₀ V₀)) (hs : s ≫ p = z) (H : IsPullback s (𝟙 Z) p z)
  (e : SheafOfModules.unit (pullback (boundaryLineProjection R) (z ≫ (boundaryLineProjection
    R))).ringCatSheaf ≅
    Hom.idealModule (Hom.boundaryGraphTarget (boundaryLineProjection R) z))
  (ha : Disjoint (Set.range a) (Set.range z))
  (d : D ⟶ C) (hd : Disjoint (Set.range j) (Set.range d))
  (c : BoundarySectionData (boundaryLineProjection R) (f ≫ (ProjectiveSpace.toSpec R (ULift.{u}
    (Fin 2)))) j p hq a z s hs H e ha d hd)
  (vB : V ⟶ finalOriginalSource R₀ p₀ O₀ V₀) [IsOpenImmersion vB]
  (vA : V ⟶ A) (hsmall : vB ≫ p = vA ≫ a)
  [SmoothOfRelativeDimension 1 ((vB ≫ j) ≫
    (f ≫ ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))))]
  (hcover : ∀ x : C, x ∈ Set.range (vB ≫ j) ∨ x ∈ Set.range d ∨
    x ∈ Set.range (s ≫ j))
  {DA : Scheme.{u}} (dA : DA ⟶ (ProjectiveSpace R (ULift.{u} (Fin 2))))
  (LA : LineBundle (pullback ((chart R 0) ≫ (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))))
    (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))))
  (aA : SheafOfModules.unit (pullback ((chart R 0) ≫ (ProjectiveSpace.toSpec R (ULift.{u} (Fin
    2)))) (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))).ringCatSheaf ⟶
    (tensorLineBundle _ LA (dualLineBundle _ (Hom.relativeCompactificationGraphLine
      (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) (chart R 0)))).val)
  (bA : SheafOfModules.unit (pullback ((chart R 0) ≫ (ProjectiveSpace.toSpec R (ULift.{u} (Fin
    2)))) (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))).ringCatSheaf ⟶ LA.val)
  [IsIso (pullbackSectionMap
    (coprod.desc (Hom.infinityProductMap (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) (chart R
      0) dA) (Hom.graphBoundaryRestriction (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) (chart
      R 0) z)) aA)]

variable [IsIso (pullbackSectionMap
  (Hom.fullBoundaryProductMap (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))
    (chart R 0) dA z) bA)]


variable {B : Scheme.{u}} [IsAffine B]
  (αorig : B ⟶ finalOriginalSource R₀ p₀ O₀ V₀) [Smooth αorig]
  (βorig : B ⟶ A) [Flat βorig] (horig : αorig ≫ p = βorig ≫ a)
  (φorig : B ⟶ V) (hφorig : φorig ≫ (vB ≫ j) = αorig ≫ j)
  (hcoverA : ∀ x : ProjectiveSpace R (ULift.{u} (Fin 2)),
    x ∈ Set.range (a ≫ chart R 0) ∨ x ∈ Set.range dA ∨ x ∈ Set.range (z ≫ chart R 0))
  {k : Type u} [Field k] (Pst : PresheafWithTransfers.{w} k)
  (t : Spec (.of R) ⟶ Spec (.of k)) [Smooth t]

/-- The relative-dimension instance used in this module. -/
local instance nativeSectionPairActionConversionSmoothRelativeDimension
    : SmoothOfRelativeDimension 1 ((a ≫ chart R 0) ≫
    ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) := by
  rw [Category.assoc]
  exact inferInstanceAs (SmoothOfRelativeDimension (0 + 1) _)

/-- Convert the canonical action spelling without changing any native data. -/
theorem nativeSectionPair_action_of_canonical_action
    (i : (nativeSectionPairParameterComponentCover R₀ p₀ O₀ V₀).I₀)
    (hCanonical :
    let π := ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))
    let α := (nativeSectionPairParameterComponentCover R₀ p₀ O₀ V₀).f i
    let pSite : (lambdaSourceSite k t (f ≫ π) j) ⟶
        (lambdaSourceSite k t π (chart R 0)) := SmoothSite.homMk p (by
      change p ≫ (((chart R 0) ≫ π) ≫ t) = (j ≫ (f ≫ π)) ≫ t
      simpa only [Category.assoc] using congrArg (fun m => m ≫ π ≫ t) hret.symm)
    let vASite : (relativeTargetSite k t (f ≫ π) (vB ≫ j)) ⟶
        (relativeTargetSite k t π (a ≫ chart R 0)) := SmoothSite.homMk vA (by
      change vA ≫ (((a ≫ chart R 0) ≫ π) ≫ t) = ((vB ≫ j) ≫ (f ≫ π)) ≫ t
      rw [Category.assoc, Category.assoc, ← Category.assoc vA a, ← hsmall]
      simpa only [Category.assoc] using congrArg (fun m => vB ≫ m ≫ π ≫ t) hret.symm)
    let data := c.toData k t (boundaryLineProjection R) (f ≫ π) j p hq a
      αorig βorig horig z s hs H e ha d hd (vB ≫ j) hcover φorig hφorig
    let : IsIso (pullbackSectionMap (fullBoundaryProductMap π (chart R 0) dA z) aA) :=
      inferInstanceAs (IsIso (pullbackSectionMap
        (coprod.desc (infinityProductMap π (chart R 0) dA)
          (graphBoundaryRestriction π (chart R 0) z)) aA))
    Pst.transfer (((graphFunctor k).map (relativeAlpha k t (f ≫ π) j α) ≫
      (data.lam ≫ (graphFunctor k).map vASite)) :
        Cor.mk (relativeCommonSite k t (f ≫ π) j α) ⟶
          Cor.mk (relativeTargetSite k t π (a ≫ chart R 0))) =
    Pst.transfer (((graphFunctor k).map (relativeAlpha k t (f ≫ π) j α ≫ pSite) ≫
      originalTargetLambda k t π (chart R 0) z dA a hcoverA LA aA bA) :
        Cor.mk (relativeCommonSite k t (f ≫ π) j α) ⟶
          Cor.mk (relativeTargetSite k t π (a ≫ chart R 0)))) :
    let π := ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))
    let α := (nativeSectionPairParameterComponentCover R₀ p₀ O₀ V₀).f i
    let Ksite := relativeCommonSite k t (f ≫ π) j α
    let Ysite := lambdaSourceSite k t (f ≫ π) j
    let Xsite := lambdaSourceSite k t π (chart R 0)
    let Qsite := relativeTargetSite k t π (a ≫ chart R 0)
    let Vsite := relativeTargetSite k t (f ≫ π) (vB ≫ j)
    let pSite : Ysite ⟶ Xsite := SmoothSite.homMk p (by
      change p ≫ (((chart R 0) ≫ π) ≫ t) = (j ≫ (f ≫ π)) ≫ t
      simpa only [Category.assoc] using congrArg (fun m => m ≫ π ≫ t) hret.symm)
    let vASite : Vsite ⟶ Qsite := SmoothSite.homMk vA (by
      change vA ≫ (((a ≫ chart R 0) ≫ π) ≫ t) = ((vB ≫ j) ≫ (f ≫ π)) ≫ t
      rw [Category.assoc, Category.assoc, ← Category.assoc vA a, ← hsmall]
      simpa only [Category.assoc] using congrArg (fun m => vB ≫ m ≫ π ≫ t) hret.symm)
    let data := c.toData k t (boundaryLineProjection R) (f ≫ π) j p hq a
      αorig βorig horig z s hs H e ha d hd (vB ≫ j) hcover φorig hφorig
    let : IsIso (pullbackSectionMap (fullBoundaryProductMap π (chart R 0) dA z) aA) :=
      inferInstanceAs (IsIso (pullbackSectionMap
        (coprod.desc (infinityProductMap π (chart R 0) dA)
          (graphBoundaryRestriction π (chart R 0) z)) aA))
    Pst.transfer (((graphFunctor k).map (relativeAlpha k t (f ≫ π) j α) ≫
      (data.lam ≫ (graphFunctor k).map vASite)) : Cor.mk Ksite ⟶ Cor.mk Qsite) =
    Pst.transfer (((graphFunctor k).map (relativeAlpha k t (f ≫ π) j α ≫ pSite) ≫
      originalTargetLambda k t π (chart R 0) z dA a hcoverA LA aA bA) :
        Cor.mk Ksite ⟶ Cor.mk Qsite) := by
  intro π α Ksite Ysite Xsite Qsite Vsite pSite vASite data haBoundary
  exact hCanonical

end Motivic.PresheafWithTransfers
