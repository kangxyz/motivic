/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.Sheafification.NativeActionLifting
public import Motivic.Transfers.Presheaf.Actions.Norm.NativeRefinement.OriginalHistoryRestrictions
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.AffineLine.NativeMiddleInput
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.AffineLine.NativeOriginalBase
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.AffineLine.NativeOriginalCylinder

/-! # Whole-cylinder lifting on the original history

For an HI `P : PresheafWithTransfers.{u + 1} k` over a field, join the fixed
original history and its boundary, source and target witnesses to the original
matching image representatives. The displayed affine coefficient/source
refinements and the whole marked scheme with its pullback square are retained.

The native source and puncture restrictions and the original cylinder
comparison transport the given Nisnevich cover into the lifting adapter.
`wholeCylinder_lift` returns an image section on the whole cylinder over
`nativeOriginalBaseSite`, retaining the composite original base inclusion and
its sheafification-unit equation.
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
universe u
open AlgebraicGeometry.FiniteSchemeNormBaseChange
open AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates

open Motivic.PresheafWithTransfers.OriginalHistorySiteLifting

attribute [local instance] OriginalRepresentativeGeometry.affineU
  OriginalRepresentativeGeometry.affineA OriginalRepresentativeGeometry.openA
  OriginalRepresentativeGeometry.affineB OriginalRepresentativeGeometry.affineW
  OriginalRepresentativeGeometry.affineO OriginalHistoryData.affineV

namespace Motivic.PresheafWithTransfers.NativeOwnedOriginalHistorySiteLifting
variable {k : Type u} [Field k] (D : OriginalHistoryData k)

/-- Package the rich suppliers and lift representatives over one abstract history. -/
theorem wholeCylinder_lift
    (B : D.history.BoundaryWitnesses)
    (hSource : D.history.SourceSections B) (hTarget : D.history.TargetSections)
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant)
    {X Borig : SmoothSite (Spec (.of k))} (jU : D.U ⟶ X) [IsOpenImmersion jU.left]
    (bAorig : Borig ⟶ D.A) (bYorig : Borig ⟶ D.Y) (HB : IsPullback bAorig bYorig
      D.a D.p)
    (g : ((nisnevichSheafify k).obj P).obj.sections
      ((Cor.graphFunctor k).obj (SmoothSite.a1Cylinder (.of k) X)))
    (sA : (nisnevichImage P).sections ((Cor.graphFunctor k).obj D.A))
    (sY : (nisnevichImage P).sections ((Cor.graphFunctor k).obj D.Y))
    (hm : (nisnevichImage P).transfer ((Cor.graphFunctor k).map bAorig) sA =
      (nisnevichImage P).transfer ((Cor.graphFunctor k).map bYorig) sY)
    (hgA : (nisnevichImageι P).hom.app (op ((Cor.graphFunctor k).obj D.A)) sA =
      ((nisnevichSheafify k).obj P).obj.transfer
        ((Cor.graphFunctor k).map (D.a ≫ D.eT.hom ≫ SmoothSite.a1Map (.of k) jU)) g)
    (hgY : (nisnevichImageι P).hom.app (op ((Cor.graphFunctor k).obj D.Y)) sY =
      ((nisnevichSheafify k).obj P).obj.transfer
        ((Cor.graphFunctor k).map (D.p ≫ D.eT.hom ≫ SmoothSite.a1Map (.of k) jU)) g) :
    let U₂ := SmoothSite.nativeOriginalBaseSite D.U D.B₀ D.O D.V
    let l := SmoothSite.nativeOriginalBaseInclusion D.U D.B₀ D.O D.V
    IsOpenImmersion (l ≫ jU).left ∧ Nonempty U₂.left ∧
      ∃ t : (nisnevichImage P).sections
        ((Cor.graphFunctor k).obj (SmoothSite.a1Cylinder (.of k) U₂)),
        (nisnevichImageι P).hom.app
          (op ((Cor.graphFunctor k).obj (SmoothSite.a1Cylinder (.of k) U₂))) t =
          ((nisnevichSheafify k).obj P).obj.transfer
            ((Cor.graphFunctor k).map (SmoothSite.a1Map (.of k) (l ≫ jU))) g := by
  classical
  obtain ⟨source⟩ := D.history.nonempty_sourceWitnesses B hSource
  obtain ⟨target⟩ := D.history.nonemptyTargetWitnesses hTarget
  let C : OriginalHistoryContext k :=
    { data := D, boundary := B, source := source, target := target }
  let t₂ := C.fieldMap
  let N := C.native
  let m := (OriginalHistoryNativeLine.ownedLineRestriction C)
  let e := (OriginalHistoryNativeLine.ownedCylinderIso C)
  let rA := (OriginalHistoryNativeSiteAssembly.punctureRestriction C)
  let rY := (OriginalHistoryNativeSiteAssembly.sourceRestriction C)
  let D := (OriginalHistoryNativeSiteAssembly.transport C)
  have hD := (OriginalHistoryNativeSiteAssembly.transport_compatible C)
  let U₂ := SmoothSite.nativeOriginalBaseSite C.data.U C.data.B₀ C.data.O C.data.V
  let l := SmoothSite.nativeOriginalBaseInclusion C.data.U C.data.B₀ C.data.O C.data.V
  let : IsOpenImmersion l.left := inferInstance
  have hU₂ : Nonempty U₂.left :=
    SmoothSite.nativeOriginalBaseSite_nonempty C.data.U C.data.B₀ C.data.O C.data.V
      C.boundary.x C.boundary.hxV
  let h := SmoothSite.nativeOriginalWholeCylinderMap C.data.U C.data.Tc C.data.eT C.data.B₀
    C.data.O C.data.V
  have he : h ≫ C.data.eT.hom = SmoothSite.a1Map (.of k) l :=
    SmoothSite.nativeOriginalWholeCylinderMap_comp C.data.U C.data.Tc C.data.eT C.data.B₀
      C.data.O C.data.V
  let i' := N.aSite ≫ e.hom
  let v' := N.toInput.pSite ≫ e.hom
  have hline : e.hom ≫ h = m :=
    (OriginalHistoryNativeLine.ownedCylinderIso_comp C)
  have hA : rA ≫ C.data.a = N.aSite ≫ m :=
    (OriginalHistoryNativeSiteAssembly.punctureRestriction_comp C)
  have hY : rY ≫ C.data.p = N.toInput.pSite ≫ m :=
    (OriginalHistoryNativeSiteAssembly.sourceRestriction_comp C)
  have hi' : rA ≫ C.data.a = i' ≫ h :=
    hA.trans ((congrArg (fun f => N.aSite ≫ f) hline.symm).trans
      (Category.assoc N.aSite e.hom h).symm)
  have hv' : rY ≫ C.data.p = v' ≫ h :=
    hY.trans ((congrArg (fun f => N.toInput.pSite ≫ f) hline.symm).trans
      (Category.assoc N.toInput.pSite e.hom h).symm)
  let H := C.data.history
  have hp := OriginalHistoryEndpointEqualities.native_p_eq_history C
  let : Etale N.p := by
    rw [hp]
    exact OriginalLocalizationHistory.sourceEtale H
  have hcover' : Sieve.ofTwoArrows i' v' ∈
      SmoothSite.nisnevichTopology (Spec (.of k)) (SmoothSite.a1Cylinder (.of k) U₂) :=
    N.nativeCover_mem_nisnevichTopology e
  exact C.source.wholeCylinder_lift C.target t₂ P hP jU l hU₂ C.data.eT h he
    C.data.a C.data.p bAorig bYorig HB i' v' rA rY hi' hv' hcover'
    D.sourceComparison D.punctureComparison D.cylinderComparison
    D.sourceRestriction D.parameterRestriction
    hD.source hD.puncture hD.sourceRestriction hD.parameterRestriction hD.overlap
    g sA sY hm hgA hgY

end Motivic.PresheafWithTransfers.NativeOwnedOriginalHistorySiteLifting
