/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Data.BoundarySectionData
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.CorrespondenceSites

/-! # Original relative-curve input and its sites

The original geometric and section input owns its five smooth sites and three
restriction maps. It has no correspondence, transfer-action or lifting fields.
Its current consumer is the native affine-line middle-input specialization.

Intended upstream module:
`Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Data.OriginalMiddleInput`.

The exact hypotheses are the record fields and declaration signatures below.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Scheme Scheme.Hom Scheme.Modules Scheme.Modules.Invertible
open Scheme.RelativeCurvePencil
universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

local instance {X Y : Scheme.{u}} (f : X ⟶ Y) [SmoothOfRelativeDimension 1 f] :
    Smooth f := SmoothOfRelativeDimension.smooth 1 f

/-- Existing geometry and the same source and target sections, with no action conclusion. -/
structure OriginalMiddleInput (k : Type u) [Field k] where
  /-- The original S scheme. -/
  S : Scheme.{u}
  /-- The original C scheme. -/
  C : Scheme.{u}
  /-- The original P scheme. -/
  P : Scheme.{u}
  /-- The original X scheme. -/
  X : Scheme.{u}
  /-- The original Y scheme. -/
  Y : Scheme.{u}
  /-- The original A scheme. -/
  A : Scheme.{u}
  /-- The original V scheme. -/
  V : Scheme.{u}
  /-- The original B scheme. -/
  B : Scheme.{u}
  /-- The original Z scheme. -/
  Z : Scheme.{u}
  /-- The original DB scheme. -/
  DB : Scheme.{u}
  /-- The original DA scheme. -/
  DA : Scheme.{u}
  /-- The original affineS input. -/
  [affineS : IsAffine S]
  /-- The original affineX input. -/
  [affineX : IsAffine X]
  /-- The original affineY input. -/
  [affineY : IsAffine Y]
  /-- The original affineA input. -/
  [affineA : IsAffine A]
  /-- The original affineV input. -/
  [affineV : IsAffine V]
  /-- The original affineB input. -/
  [affineB : IsAffine B]
  /-- The original t input. -/
  t : S ⟶ Spec (.of k)
  /-- The original smoothT input. -/
  [smoothT : Smooth t]
  /-- The original qX input. -/
  qX : X ⟶ S
  /-- The original separatedQX input. -/
  [separatedQX : IsSeparated qX]
  /-- The original smoothQX input. -/
  [smoothQX : SmoothOfRelativeDimension 1 qX]
  /-- The original π input. -/
  π : P ⟶ S
  /-- The original properPi input. -/
  [properPi : IsProper π]
  /-- The original F input. -/
  F : C ⟶ P
  /-- The original finiteF input. -/
  [finiteF : IsFinite F]
  /-- The original jB input. -/
  jB : Y ⟶ C
  /-- The original openJB input. -/
  [openJB : IsOpenImmersion jB]
  /-- The original smoothJB input. -/
  [smoothJB : SmoothOfRelativeDimension 1 (jB ≫ (F ≫ π))]
  /-- The original jA input. -/
  jA : X ⟶ P
  /-- The original openJA input. -/
  [openJA : IsOpenImmersion jA]
  /-- The original smoothJA input. -/
  [smoothJA : SmoothOfRelativeDimension 1 (jA ≫ π)]
  /-- The original p input. -/
  p : Y ⟶ X
  /-- The original flatP input. -/
  [flatP : Flat p]
  /-- The original hret input. -/
  hret : jB ≫ F = p ≫ jA
  /-- The original hbase input. -/
  hbase : jB ≫ (F ≫ π) = p ≫ qX
  /-- The original a input. -/
  a : A ⟶ X
  /-- The original openA input. -/
  [openA : IsOpenImmersion a]
  /-- The original vB input. -/
  vB : V ⟶ Y
  /-- The original openVB input. -/
  [openVB : IsOpenImmersion vB]
  /-- The original vA input. -/
  vA : V ⟶ A
  /-- The original hsmall input. -/
  hsmall : vB ≫ p = vA ≫ a
  /-- The original smoothVB input. -/
  [smoothVB : SmoothOfRelativeDimension 1 ((vB ≫ jB) ≫ (F ≫ π))]
  /-- The original smoothA input. -/
  [smoothA : SmoothOfRelativeDimension 1 ((a ≫ jA) ≫ π)]
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
  hφorig : φorig ≫ (vB ≫ jB) = αorig ≫ jB
  /-- The original z input. -/
  z : Z ⟶ X
  /-- The original s input. -/
  s : Z ⟶ Y
  /-- The original hs input. -/
  hs : s ≫ p = z
  /-- The original H input. -/
  H : IsPullback s (𝟙 _) p z
  /-- The original e input. -/
  e : SheafOfModules.unit (pullback qX (z ≫ qX)).ringCatSheaf ≅
    idealModule (boundaryGraphTarget qX z)
  /-- The original ha input. -/
  ha : Disjoint (Set.range a) (Set.range z)
  /-- The original dB input. -/
  dB : DB ⟶ C
  /-- The original hdB input. -/
  hdB : Disjoint (Set.range jB) (Set.range dB)
  /-- The original dA input. -/
  dA : DA ⟶ P
  /-- The original hcoverB input. -/
  hcoverB : ∀ x : C, x ∈ Set.range (vB ≫ jB) ∨
    x ∈ Set.range dB ∨ x ∈ Set.range (s ≫ jB)
  /-- The original hcoverA input. -/
  hcoverA : ∀ x : P, x ∈ Set.range (a ≫ jA) ∨
    x ∈ Set.range dA ∨ x ∈ Set.range (z ≫ jA)
  /-- The original source input. -/
  source : BoundarySectionData qX (F ≫ π) jB p hbase a z s hs H e ha dB hdB
  /-- The original LA input. -/
  LA : LineBundle (pullback (jA ≫ π) π)
  /-- The original aA input. -/
  aA : SheafOfModules.unit (pullback (jA ≫ π) π).ringCatSheaf ⟶
    (tensorLineBundle _ LA (dualLineBundle _ (relativeCompactificationGraphLine π jA))).val
  /-- The original bA input. -/
  bA : SheafOfModules.unit (pullback (jA ≫ π) π).ringCatSheaf ⟶ LA.val
  /-- The original unitA input. -/
  [unitA : IsIso (pullbackSectionMap (fullBoundaryProductMap π jA dA z) aA)]
  /-- The original unitB input. -/
  [unitB : IsIso (pullbackSectionMap (fullBoundaryProductMap π jA dA z) bA)]

namespace OriginalMiddleInput

attribute [local instance] affineS affineX affineY affineA affineV affineB
  smoothT separatedQX smoothQX properPi finiteF openJB smoothJB openJA smoothJA
  flatP openA openVB smoothVB smoothA smoothAlpha flatBeta unitA unitB

variable {k : Type u} [Field k] (G : OriginalMiddleInput k)

/-- The shared target-lambda source site. -/
def siteX := lambdaSourceSite k G.t G.π G.jA
/-- The shared source-lambda source site. -/
def siteY := lambdaSourceSite k G.t (G.F ≫ G.π) G.jB
/-- The shared correction source site. -/
def siteA := psiSourceSite k G.t G.qX G.a
/-- The shared target retained site. -/
def siteQ := relativeTargetSite k G.t G.π (G.a ≫ G.jA)
/-- The shared source retained site. -/
def siteV := relativeTargetSite k G.t (G.F ≫ G.π) (G.vB ≫ G.jB)

/-- The original map between lambda sources. -/
def pSite : G.siteY ⟶ G.siteX := SmoothSite.homMk G.p (by
  change G.p ≫ ((G.jA ≫ G.π) ≫ G.t) = (G.jB ≫ (G.F ≫ G.π)) ≫ G.t
  simpa only [Category.assoc] using congrArg (fun m => m ≫ G.π ≫ G.t) G.hret.symm)

/-- The original map between retained sites. -/
def wSite : G.siteV ⟶ G.siteQ := SmoothSite.homMk G.vA (by
  change G.vA ≫ (((G.a ≫ G.jA) ≫ G.π) ≫ G.t) =
    ((G.vB ≫ G.jB) ≫ (G.F ≫ G.π)) ≫ G.t
  rw [Category.assoc, Category.assoc, ← Category.assoc G.vA G.a, ← G.hsmall]
  simpa only [Category.assoc] using
    congrArg (fun m => G.vB ≫ m ≫ G.π ≫ G.t) G.hret.symm)

/-- The original retained-source inclusion on the shared sites. -/
def uSite : G.siteV ⟶ G.siteY := SmoothSite.homMk G.vB (by
  change G.vB ≫ ((G.jB ≫ (G.F ≫ G.π)) ≫ G.t) =
    ((G.vB ≫ G.jB) ≫ (G.F ≫ G.π)) ≫ G.t
  simp only [Category.assoc])

end OriginalMiddleInput
end AlgebraicGeometry.Scheme.RelativeCurvePencil
