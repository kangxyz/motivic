/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Data.OriginalMiddleInput
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Correction.OriginalTargetSectionWitnesses
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Correction.OriginalCorrectionActionGeometry

/-! # Native original middle input

The native coordinate geometry retains the original source datum and one target
choice. Its geometric specialization fixes the free input and its sites once.
Current consumers are the original localization input, native restriction sites
and the transfer-action extensions of this same record.

Intended upstream module:
`Aglib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.
NativeOriginalMiddleInput`.

The exact hypotheses are the record fields and declaration signatures below.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Scheme Scheme.Hom Scheme.Modules Scheme.Modules.Invertible RelativeProjectiveLine
open Scheme.RelativeCurvePencil
universe u

namespace AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification

/-- The smoothness instance used in this module. -/
local instance nativeOriginalMiddleInputSmooth
    {X Y : Scheme.{u}} (f : X ⟶ Y) [SmoothOfRelativeDimension 1 f] :
    Smooth f := SmoothOfRelativeDimension.smooth 1 f

/-- The relative-dimension instance used in this module. -/
local instance nativeOriginalMiddleInputSmoothRelativeDimension1 (R : Type u) [CommRing R] :
    SmoothOfRelativeDimension 1 (boundaryLineProjection R) :=
  Scheme.AffineLineEtaleCompactification.polynomialProjection_smooth_one R

/-- The relative-dimension instance used in this module. -/
local instance nativeOriginalMiddleInputSmoothRelativeDimension2 (R : Type u) [CommRing R] :
    SmoothOfRelativeDimension 1 (chart R 0 ≫ ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) := by
  rw [chart_toSpec]
  infer_instance

/-- Native-coordinate geometry with exactly the existing E5 witnesses.
The one map to the free input fixes the coordinate schemes definitionally. -/
structure NativeOriginalMiddleInput (k : Type u) [Field k] where
  /-- The original R input. -/
  R : Type u
  /-- The original commRing input. -/
  [commRing : CommRing R]
  /-- The original domain input. -/
  [domain : IsDomain R]
  /-- The original integrallyClosed input. -/
  [integrallyClosed : IsIntegrallyClosed R]
  /-- The original noetherian input. -/
  [noetherian : IsNoetherianRing R]
  /-- The original Y input. -/
  Y : Scheme.{u}
  /-- The original A input. -/
  A : Scheme.{u}
  /-- The original Z input. -/
  Z : Scheme.{u}
  /-- The original C input. -/
  C : Scheme.{u}
  /-- The original D input. -/
  D : Scheme.{u}
  /-- The original V input. -/
  V : Scheme.{u}
  /-- The original WA input. -/
  WA : Scheme.{u}
  /-- The original DA input. -/
  DA : Scheme.{u}
  /-- The original B input. -/
  B : Scheme.{u}
  /-- The original affineY input. -/
  [affineY : IsAffine Y]
  /-- The original affineA input. -/
  [affineA : IsAffine A]
  /-- The original affineV input. -/
  [affineV : IsAffine V]
  /-- The original affineB input. -/
  [affineB : IsAffine B]
  /-- The original F input. -/
  F : C ⟶ (ProjectiveSpace R (ULift.{u} (Fin 2)))
  /-- The original finiteF input. -/
  [finiteF : IsFinite F]
  /-- The original j input. -/
  j : Y ⟶ C
  /-- The original openJ input. -/
  [openJ : IsOpenImmersion j]
  /-- The original smoothJ input. -/
  [smoothJ : SmoothOfRelativeDimension 1 (j ≫ (F ≫ (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))))]
  /-- The original p input. -/
  p : Y ⟶ (Spec (.of (Polynomial R)))
  /-- The original flatP input. -/
  [flatP : Flat p]
  /-- The original hq input. -/
  hq : j ≫ (F ≫ (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))) = p ≫ (boundaryLineProjection R)
  /-- The original hret input. -/
  hret : j ≫ F = p ≫ (chart R 0)
  /-- The original a input. -/
  a : A ⟶ (Spec (.of (Polynomial R)))
  /-- The original openA input. -/
  [openA : IsOpenImmersion a]
  /-- The original z input. -/
  z : Z ⟶ (Spec (.of (Polynomial R)))
  /-- The original closedZChart input. -/
  [closedZChart : IsClosedImmersion (z ≫ (chart R 0))]
  /-- The original s input. -/
  s : Z ⟶ Y
  /-- The original hs input. -/
  hs : s ≫ p = z
  /-- The original H input. -/
  H : IsPullback s (𝟙 _) p z
  /-- The original hsK input. -/
  hsK : (s ≫ j) ≫ F = z ≫ (chart R 0)
  /-- The original e input. -/
  e : SheafOfModules.unit (pullback (boundaryLineProjection R) (z ≫ (boundaryLineProjection
    R))).ringCatSheaf ≅
    idealModule (boundaryGraphTarget (boundaryLineProjection R) z)
  /-- The original ha input. -/
  ha : Disjoint (Set.range a) (Set.range z)
  /-- The original d input. -/
  d : D ⟶ C
  /-- The original hd input. -/
  hd : Disjoint (Set.range j) (Set.range d)
  /-- The original source input. -/
  source : BoundarySectionData (boundaryLineProjection R) (F ≫ (ProjectiveSpace.toSpec R
    (ULift.{u} (Fin 2)))) j p hq a z s hs H e ha d hd
  /-- The original vB input. -/
  vB : V ⟶ Y
  /-- The original openVB input. -/
  [openVB : IsOpenImmersion vB]
  /-- The original vA input. -/
  vA : V ⟶ A
  /-- The original hsmall input. -/
  hsmall : vB ≫ p = vA ≫ a
  /-- The original hcover input. -/
  hcover : ∀ x : C, x ∈ Set.range (vB ≫ j) ∨
    x ∈ Set.range d ∨ x ∈ Set.range (s ≫ j)
  /-- The original dA input. -/
  dA : DA ⟶ (ProjectiveSpace R (ULift.{u} (Fin 2)))
  /-- The original affineDA input. -/
  [affineDA : IsAffineHom dA]
  /-- The original hdA input. -/
  hdA : Disjoint (Set.range (chart R 0)) (Set.range dA)
  /-- The original bI input. -/
  bI : pullback F dA ⟶ D
  /-- The original hbI input. -/
  hbI : bI ≫ d = pullback.fst F dA
  /-- The original bE input. -/
  bE : (Scheme.residualMarkedFiberOpen F j (z ≫ (chart R 0)) s hsK).toScheme ⟶ D
  /-- The original hbE input. -/
  hbE : bE ≫ d = Scheme.residualMarkedFiberMap F j (z ≫ (chart R 0)) s hsK
  /-- The original iA input. -/
  iA : WA ⟶ pullback ((chart R 0) ≫ (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))))
    (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))
  /-- The original openIA input. -/
  [openIA : IsOpenImmersion iA]
  /-- The unchanged target choice, held once in its shared free schema. -/
  target : Scheme.RelativeAffineLineEtaleCompactification.OriginalTargetSectionWitnesses
    R z e dA hdA iA
  /-- The original αorig input. -/
  αorig : B ⟶ Y
  /-- The original smoothAlpha input. -/
  [smoothAlpha : Smooth αorig]
  /-- The original βorig input. -/
  βorig : B ⟶ A
  /-- The original flatBeta input. -/
  [flatBeta : Flat βorig]
  /-- The original horig input. -/
  horig : αorig ≫ p = βorig ≫ a
  /-- The original φorig input. -/
  φorig : B ⟶ V
  /-- The original hφorig input. -/
  hφorig : φorig ≫ (vB ≫ j) = αorig ≫ j
  /-- The original hcoverA input. -/
  hcoverA : ∀ x : (ProjectiveSpace R (ULift.{u} (Fin 2))), x ∈ Set.range (a ≫ (chart R 0)) ∨
    x ∈ Set.range dA ∨ x ∈ Set.range (z ≫ (chart R 0))
  /-- The original t input. -/
  t : (Spec (.of R)) ⟶ Spec (.of k)
  /-- The original smoothT input. -/
  [smoothT : Smooth t]
  /-- The original hpuncture input. -/
  hpuncture : (Set.range a)ᶜ ⊆ Set.range z
  /-- The original hfree input. -/
  hfree : ∀ i : ULift.{u} (Fin 2),
    let : Algebra (Polynomial R) Γ(pullback F (chart R i), ⊤) :=
      (AlgebraicGeometry.FiniteSchemeNormBaseChange.scalarMap
        (pullback.snd F (chart R i))).toAlgebra
    Module.Free (Polynomial R) Γ(pullback F (chart R i), ⊤)

namespace NativeOriginalMiddleInput

attribute [local instance] commRing domain integrallyClosed noetherian affineY affineA affineV
  affineB finiteF openJ smoothJ flatP openA closedZChart openVB affineDA openIA
  smoothAlpha flatBeta smoothT

variable {k : Type u} [Field k] (N : NativeOriginalMiddleInput k)

/-- The original target line bundle, projected without a new choice. -/
abbrev LA := N.target.LA
/-- The original target numerator section. -/
abbrev aA := N.target.aA
/-- The original target denominator section. -/
abbrev bA := N.target.bA

/-- The unchanged original hFa proof, from the shared target choice. -/
theorem hFa : CoherentGraph.SectionDivisorFiniteFlat (pullback.fst ((chart N.R 0) ≫
    (ProjectiveSpace.toSpec N.R (ULift.{u} (Fin 2)))) (ProjectiveSpace.toSpec N.R (ULift.{u} (Fin
    2)))) N.iA
    (tensorLineBundle _ N.LA (dualLineBundle _ (relativeCompactificationGraphLine
      (ProjectiveSpace.toSpec N.R (ULift.{u} (Fin 2))) (chart N.R 0)))) N.aA :=
  N.target.hFa

/-- The unchanged original hFb proof, from the shared target choice. -/
theorem hFb : CoherentGraph.SectionDivisorFiniteFlat (pullback.fst ((chart N.R 0) ≫
    (ProjectiveSpace.toSpec N.R (ULift.{u} (Fin 2)))) (ProjectiveSpace.toSpec N.R (ULift.{u} (Fin
    2)))) N.iA N.LA N.bA :=
  N.target.hFb

/-- The unchanged original hpairA proof, from the shared target choice. -/
theorem hpairA : pullbackSectionMap (fullBoundaryProductMap (ProjectiveSpace.toSpec N.R
    (ULift.{u} (Fin
    2))) (chart N.R 0) N.dA N.z) N.aA ≫
      pullbackTensorMap (fullBoundaryProductMap (ProjectiveSpace.toSpec N.R (ULift.{u} (Fin 2)))
        (chart N.R 0) N.dA N.z) N.LA.val
        (dualLineBundle _ (relativeCompactificationGraphLine (ProjectiveSpace.toSpec N.R (ULift.{u}
          (Fin 2))) (chart N.R 0))).val =
    tensorUnitSection (pullbackSectionMap (fullBoundaryProductMap (ProjectiveSpace.toSpec N.R
      (ULift.{u} (Fin 2))) (chart N.R 0) N.dA N.z) N.bA)
      (relativeFullBoundaryFrame (boundaryLineProjection N.R) (ProjectiveSpace.toSpec N.R (ULift.{u}
        (Fin 2))) (chart N.R 0) (𝟙 _)
        ((chart_toSpec N.R 0).trans (Category.id_comp (boundaryLineProjection N.R)).symm)
        N.z N.z (Category.comp_id N.z) (IsPullback.id_vert N.z) N.e N.dA N.hdA).inv :=
  N.target.hpairA

/-- The unchanged original unitA proof, from the shared target choice. -/
theorem unitA : IsIso (pullbackSectionMap (fullBoundaryProductMap (ProjectiveSpace.toSpec N.R
    (ULift.{u}
    (Fin 2))) (chart N.R 0) N.dA N.z) N.aA) :=
  N.target.unitA

/-- The unchanged original unitB proof, from the shared target choice. -/
theorem unitB : IsIso (pullbackSectionMap (fullBoundaryProductMap (ProjectiveSpace.toSpec N.R
    (ULift.{u}
    (Fin 2))) (chart N.R 0) N.dA N.z) N.bA) :=
  N.target.unitB

attribute [local instance] unitA unitB


/-- Native puncture smoothness, derived rather than assumed as an action input. -/
theorem smoothA : SmoothOfRelativeDimension 1 ((N.a ≫ chart N.R 0) ≫
    ProjectiveSpace.toSpec N.R (ULift.{u} (Fin 2))) := by
  rw [Category.assoc]
  exact inferInstanceAs (SmoothOfRelativeDimension (0 + 1) _)

/-- Native retained-source smoothness. -/
theorem smoothVB : SmoothOfRelativeDimension 1 ((N.vB ≫ N.j) ≫
    (N.F ≫ ProjectiveSpace.toSpec N.R (ULift.{u} (Fin 2)))) := by
  rw [Category.assoc]
  exact inferInstanceAs (SmoothOfRelativeDimension (0 + 1) _)

attribute [local instance] smoothA smoothVB

/-- Package the actual native inputs once; all later endpoints use this same input. -/
def toInput : OriginalMiddleInput k where
  S := Spec (.of N.R)
  X := Spec (.of (Polynomial N.R))
  P := ProjectiveSpace N.R (ULift.{u} (Fin 2))
  C := N.C
  Y := N.Y
  A := N.A
  V := N.V
  B := N.B
  Z := N.Z
  DB := N.D
  DA := N.DA
  affineS := inferInstance
  affineX := inferInstance
  affineY := N.affineY
  affineA := N.affineA
  affineV := N.affineV
  affineB := N.affineB
  t := N.t
  smoothT := N.smoothT
  qX := boundaryLineProjection N.R
  separatedQX := inferInstance
  smoothQX := inferInstance
  π := ProjectiveSpace.toSpec N.R (ULift.{u} (Fin 2))
  properPi := inferInstance
  F := N.F
  finiteF := N.finiteF
  jB := N.j
  openJB := N.openJ
  smoothJB := N.smoothJ
  jA := chart N.R 0
  openJA := inferInstance
  smoothJA := inferInstance
  p := N.p
  flatP := N.flatP
  hret := N.hret
  hbase := N.hq
  a := N.a
  openA := N.openA
  vB := N.vB
  openVB := N.openVB
  vA := N.vA
  hsmall := N.hsmall
  smoothVB := N.smoothVB
  smoothA := N.smoothA
  αorig := N.αorig
  smoothAlpha := N.smoothAlpha
  βorig := N.βorig
  flatBeta := N.flatBeta
  horig := N.horig
  φorig := N.φorig
  hφorig := N.hφorig
  z := N.z
  s := N.s
  hs := N.hs
  H := N.H
  e := N.e
  ha := N.ha
  dB := N.d
  hdB := N.hd
  dA := N.dA
  hcoverB := N.hcover
  hcoverA := N.hcoverA
  source := N.source
  LA := N.LA
  aA := N.aA
  bA := N.bA
  unitA := N.unitA
  unitB := N.unitB

/-- The original puncture-to-lambda source map on the shared input sites. -/
def aSite : N.toInput.siteA ⟶ N.toInput.siteX :=
  originalCorrectionPairSiteMap N.t (boundaryLineProjection N.R)
    (ProjectiveSpace.toSpec N.R (ULift.{u} (Fin 2))) (chart N.R 0)
    (chart_toSpec N.R 0) N.a 0

/-- The original parameter map to the same retained target. -/
def delta : N.toInput.siteA ⟶ N.toInput.siteQ :=
  correctionSmallParameterMap N.t (boundaryLineProjection N.R)
    (ProjectiveSpace.toSpec N.R (ULift.{u} (Fin 2))) (chart N.R 0)
    (chart_toSpec N.R 0) N.a N.a (𝟙 _) (Category.id_comp N.a)


end NativeOriginalMiddleInput
end AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification
