/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.NativeOriginalMiddleInput
public import Motivic.Transfers.Presheaf.Actions.Pencils.Restriction
public import Motivic.Transfers.Presheaf.Actions.Pencils.OriginalLambdaDifference
public import Motivic.Transfers.Presheaf.Actions.Pencils.NativeCorrectionTransferAction
public import Motivic.Transfers.Presheaf.Actions.Pencils.OriginalTargetLambda

/-! # Transfer actions on the original middle input

On one `OriginalMiddleInput`, define the original target lambda, source lambda
and correction arrows, together with `rawDifference` and `arrowDifference`.
The two difference definitions agree on that same input. Their action interfaces
retain a coefficient universe independent of the base field.

`MiddleRelations` groups the E2/E4 restrictions, difference-zero E3 action and
E5 target-lambda/correction/parameter relation on those same arrows. The HI
restriction and native E5 suppliers feed
`middleRelations_of_rawDifference_zero`, whose raw zero-action premise remains
explicit.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Scheme Scheme.Hom Scheme.Modules Scheme.Modules.Invertible
open Scheme.RelativeAffineLineEtaleCompactification Scheme.RelativeCurvePencil
open RelativeProjectiveLine AlgebraicGeometry.FiniteSchemeNormBaseChange
open Motivic Motivic.PresheafWithTransfers
universe u v w

local instance {X Y : Scheme.{u}} (f : X ⟶ Y) [SmoothOfRelativeDimension 1 f] :
    Smooth f := SmoothOfRelativeDimension.smooth 1 f

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil.OriginalMiddleInput

attribute [local instance] affineS affineX affineY affineA affineV affineB
  smoothT separatedQX smoothQX properPi finiteF openJB smoothJB openJA smoothJA
  flatP openA openVB smoothVB smoothA smoothAlpha flatBeta unitA unitB

variable {k : Type u} [Field k] (G : OriginalMiddleInput k)

/-- The one original source section data construction. -/
def data := G.source.toData k G.t G.qX (G.F ≫ G.π) G.jB G.p G.hbase G.a
  G.αorig G.βorig G.horig G.z G.s G.hs G.H G.e G.ha G.dB G.hdB
  (G.vB ≫ G.jB) G.hcoverB G.φorig G.hφorig

/-- The original three arrows, on the shared sites of one input. -/
structure Arrows where
  /-- The unchanged target lambda. -/
  target : Cor.mk G.siteX ⟶ Cor.mk G.siteQ
  /-- The unchanged source lambda. -/
  source : Cor.mk G.siteY ⟶ Cor.mk G.siteV
  /-- The unchanged source correction. -/
  correction : Cor.mk G.siteA ⟶ Cor.mk G.siteV

/-- The unique arrow producer for this input, with no new choice. -/
def arrows : G.Arrows where
  target := originalTargetLambda k G.t G.π G.jA G.z G.dA G.a G.hcoverA G.LA G.aA G.bA
  source := G.data.lam
  correction := G.data.psi

/-- The actual original difference, supplied by the existing geometric theorem. -/
def rawDifference : Cor.mk G.siteY ⟶ Cor.mk G.siteQ :=
  Cor.originalLambdaDifference
    (t := G.t) (qX := G.qX) (π := G.π) (F := G.F) (jB := G.jB) (jA := G.jA)
    (p := G.p) (hret := G.hret) (hbase := G.hbase) (a := G.a)
    (vB := G.vB) (vA := G.vA) (hsmall := G.hsmall)
    (αorig := G.αorig) (βorig := G.βorig) (horig := G.horig)
    (φorig := G.φorig) (hφorig := G.hφorig) (z := G.z) (s := G.s) (hs := G.hs)
    (H := G.H) (e := G.e) (ha := G.ha) (dB := G.dB) (hdB := G.hdB) (dA := G.dA)
    (hcoverB := G.hcoverB) (hcoverA := G.hcoverA) (source := G.source)
    (LA := G.LA) (aA := G.aA) (bA := G.bA)

/-- The signed difference of the same arrows, not a newly selected correspondence. -/
def arrowDifference : Cor.mk G.siteY ⟶ Cor.mk G.siteQ :=
  Sub.sub (α := Cor.mk G.siteY ⟶ Cor.mk G.siteQ)
    (G.arrows.source ≫ (Cor.graphFunctor k).map G.wSite)
    ((Cor.graphFunctor k).map G.pSite ≫ G.arrows.target)

/-- Definition agreement is proved over one shared input, before specialization. -/
theorem rawDifference_eq_arrowDifference : G.rawDifference = G.arrowDifference := by
  rfl

/-- Convert the actual raw zero action, without assuming any desired arrow relation. -/
theorem transfer_arrowDifference_zero (Pst : PresheafWithTransfers.{v} k)
    (hRaw : Pst.transfer G.rawDifference = 0) :
    Pst.transfer G.arrowDifference = 0 := by
  rw [← G.rawDifference_eq_arrowDifference]
  exact hRaw
/-- The original source lambda acts by identity after the retained inclusion. -/
theorem transfer_source_comp_uSite (Pst : PresheafWithTransfers.{v} k)
    (hPst : Pst.IsA1Invariant) :
    Pst.transfer (G.arrows.source ≫ (Cor.graphFunctor k).map G.uSite) =
      Pst.transfer ((Cor.graphFunctor k).map (𝟙 G.siteY)) := by
  let := G.source.a_unit
  let := G.source.b_unit
  let := G.source.n_unit
  let := G.source.d_unit
  exact transfer_dataOfBoundarySections_lam_comp_graph_eq_id
    k G.t G.qX (G.F ≫ G.π) G.jB G.p G.hbase G.a G.αorig G.βorig G.horig
    G.z G.s G.hs G.H G.e G.ha G.dB G.hdB (G.vB ≫ G.jB) G.hcoverB
    G.source.T G.source.N G.source.aS G.source.bS G.source.nS G.source.dS
    G.source.hA G.source.hN G.φorig G.hφorig G.vB rfl Pst hPst

/-- The original correction acts by zero after the retained inclusion. -/
theorem transfer_correction_comp_uSite (Pst : PresheafWithTransfers.{v} k)
    (hPst : Pst.IsA1Invariant) :
    Pst.transfer (G.arrows.correction ≫ (Cor.graphFunctor k).map G.uSite) = 0 := by
  let := G.source.a_unit
  let := G.source.b_unit
  let := G.source.n_unit
  let := G.source.d_unit
  exact transfer_dataOfBoundarySections_psi_comp_graph_eq_zero
    k G.t G.qX (G.F ≫ G.π) G.jB G.p G.hbase G.a G.αorig G.βorig G.horig
    G.z G.s G.hs G.H G.e G.ha G.dB G.hdB (G.vB ≫ G.jB) G.hcoverB
    G.source.T G.source.N G.source.aS G.source.bS G.source.nS G.source.dS
    G.source.hA G.source.hN G.φorig G.hφorig G.vB rfl Pst hPst

/-- E2, E4, difference-zero E3 and E5 for the same shared original arrows. -/
def MiddleRelations (aSite : G.siteA ⟶ G.siteX) (delta : G.siteA ⟶ G.siteQ)
    (Pst : PresheafWithTransfers.{v} k) : Prop :=
  Pst.transfer (G.arrows.source ≫ (Cor.graphFunctor k).map G.uSite) =
      Pst.transfer ((Cor.graphFunctor k).map (𝟙 G.siteY)) ∧
    Pst.transfer (G.arrows.correction ≫
      (Cor.graphFunctor k).map G.uSite) = 0 ∧
    Pst.transfer G.arrowDifference = 0 ∧
    Pst.transfer ((Cor.graphFunctor k).map aSite ≫ G.arrows.target) =
      Pst.transfer (show Cor.mk G.siteA ⟶ Cor.mk G.siteQ from
        G.arrows.correction ≫ (Cor.graphFunctor k).map G.wSite) +
      Pst.transfer (show Cor.mk G.siteA ⟶ Cor.mk G.siteQ from
        (Cor.graphFunctor k).map delta)


end AlgebraicGeometry.Scheme.RelativeCurvePencil.OriginalMiddleInput

namespace AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification
/-- The relative-dimension instance used in this module. -/
local instance pencilsOriginalMiddleInputSmoothRelativeDimension1 (R : Type u) [CommRing R] :
    SmoothOfRelativeDimension 1 (boundaryLineProjection R) :=
  Scheme.AffineLineEtaleCompactification.polynomialProjection_smooth_one R

/-- The relative-dimension instance used in this module. -/
local instance pencilsOriginalMiddleInputSmoothRelativeDimension2 (R : Type u) [CommRing R] :
    SmoothOfRelativeDimension 1 (chart R 0 ≫ ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) := by
  rw [chart_toSpec]
  infer_instance

namespace NativeOriginalMiddleInput

attribute [local instance] commRing domain integrallyClosed noetherian affineY affineA affineV
  affineB finiteF openJ smoothJ flatP openA closedZChart openVB affineDA openIA
  smoothAlpha flatBeta smoothT

variable {k : Type u} [Field k] (N : NativeOriginalMiddleInput k)


attribute [local instance] unitA unitB smoothA smoothVB
/-- The actual native E5 supplier, expressed on the one shared input. -/
theorem transfer_originalPsi (Pst : PresheafWithTransfers.{v} k)
    (hPst : Pst.IsA1Invariant) :
    Pst.transfer ((Cor.graphFunctor k).map N.aSite ≫ N.toInput.arrows.target) =
      Pst.transfer (show Cor.mk N.toInput.siteA ⟶ Cor.mk N.toInput.siteQ from
        N.toInput.arrows.correction ≫ (Cor.graphFunctor k).map N.toInput.wSite) +
      Pst.transfer (show Cor.mk N.toInput.siteA ⟶ Cor.mk N.toInput.siteQ from
        (Cor.graphFunctor k).map N.delta) := by
  have hinfty : (Set.range (chart N.R 0))ᶜ ⊆ Set.range N.dA :=
    retained_complement_subset_infinity (chart N.R 0) (N.a ≫ chart N.R 0) N.a rfl
      N.z N.dA N.hcoverA
  let : IsIso (pullbackSectionMap
      (coprod.desc
        (infinityProductMap (ProjectiveSpace.toSpec N.R (ULift.{u} (Fin 2)))
          (chart N.R 0) N.dA)
        (graphBoundaryRestriction (ProjectiveSpace.toSpec N.R (ULift.{u} (Fin 2)))
          (chart N.R 0) N.z)) N.aA) := N.unitA
  have hnative := transfer_nativeCorrection_originalPsi N.R N.F N.j N.p N.hq N.hret
    N.a N.z N.s N.hs N.H N.hsK N.e N.ha N.d N.hd N.source
    (N.vB ≫ N.j) N.hcover N.dA N.hdA N.bI N.hbI N.bE N.hbE
    N.LA N.aA N.bA N.iA N.hFa N.hFb N.hpairA
    Pst hPst N.t N.a N.vB rfl N.vA N.hsmall.symm
    (𝟙 _) (Category.id_comp N.a) hinfty N.hpuncture
    N.αorig N.βorig N.horig N.φorig N.hφorig N.hfree
  have hw : correctionSmallTargetMap N.t
      (ProjectiveSpace.toSpec N.R (ULift.{u} (Fin 2))) N.F N.j (chart N.R 0)
      N.p N.hret N.a (N.vB ≫ N.j) N.vB rfl N.vA N.hsmall.symm =
      N.toInput.wSite := by
    apply MorphismProperty.Over.Hom.ext
    rfl
  change Pst.transfer ((Cor.graphFunctor k).map N.aSite ≫ N.toInput.arrows.target) =
    Pst.transfer (show Cor.mk N.toInput.siteA ⟶ Cor.mk N.toInput.siteQ from
      N.toInput.arrows.correction ≫ (Cor.graphFunctor k).map
        (correctionSmallTargetMap N.t
          (ProjectiveSpace.toSpec N.R (ULift.{u} (Fin 2))) N.F N.j (chart N.R 0)
          N.p N.hret N.a (N.vB ≫ N.j) N.vB rfl N.vA N.hsmall.symm)) +
    Pst.transfer (show Cor.mk N.toInput.siteA ⟶ Cor.mk N.toInput.siteQ from
      (Cor.graphFunctor k).map N.delta) at hnative
  rw [hw] at hnative
  exact hnative

/-- Assemble the proved components; the raw zero action remains an explicit input
that the native-history supplier must prove before whole-cylinder application. -/
theorem middleRelations_of_rawDifference_zero (Pst : PresheafWithTransfers.{v} k)
    (hPst : Pst.IsA1Invariant) (hRaw : Pst.transfer N.toInput.rawDifference = 0) :
    N.toInput.MiddleRelations N.aSite N.delta Pst := by
  exact ⟨N.toInput.transfer_source_comp_uSite Pst hPst,
    N.toInput.transfer_correction_comp_uSite Pst hPst,
    N.toInput.transfer_arrowDifference_zero Pst hRaw,
    N.transfer_originalPsi Pst hPst⟩

end NativeOriginalMiddleInput
end AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification
