/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.Presheaf.Actions.Norm.NativeRefinement.OriginalHistory
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.AffineLine.LocalizationHistory
public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.OriginalLocalizationInput
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.AffineLine.NativeMiddleInput
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.AffineLine.NativeOriginalCylinder

/-! # The original history coefficient line

Over a field, for the fixed history and its boundary, source and target witnesses,
`ownedLineIso` identifies the native middle-input line with
`nativeOriginalLineSite` over the final coefficient base. The source-map
comparison keeps the same original history map.

`ownedCylinderIso` uses the original cylinder isomorphism, and
`ownedLineRestriction` gives the one line-to-original-target map used by both
restriction diagrams. Their displayed equations retain the original affine
base restrictions and fixed witnesses.
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

namespace Motivic.PresheafWithTransfers.OriginalHistoryEndpointEqualities
variable {k : Type u} [Field k] (C : OriginalHistoryContext k)

/-- The variable history has the same final original coefficient line. -/
theorem ownedLineSite_eq : C.native.nativeLineSite =
    SmoothSite.nativeOriginalLineSite C.data.U C.data.B₀ C.data.O C.data.V := by
  exact C.source.toNative_lineSite_eq C.target C.fieldMap

/-- The native source is the stored source map of this same history. -/
theorem native_p_eq_history : C.native.p = C.data.history.p₂ :=
  C.source.toNative_sourceMap_eq C.target C.fieldMap

end Motivic.PresheafWithTransfers.OriginalHistoryEndpointEqualities

namespace Motivic.PresheafWithTransfers.OriginalHistoryNativeLine
variable {k : Type u} [Field k] (C : OriginalHistoryContext k)

/-- Compare the native input line with the final original coefficient line. -/
def ownedLineIso :
    (C.native).toInput.siteX ≅
      SmoothSite.nativeOriginalLineSite C.data.U C.data.B₀ C.data.O C.data.V := by
  exact (C.native).nativeLineSiteIso
    ≪≫
    eqToIso (OriginalHistoryEndpointEqualities.ownedLineSite_eq C)

/-- The chosen cylinder comparison uses the original cylinder isomorphism. -/
def ownedCylinderIso :=
  (ownedLineIso C) ≪≫
    SmoothSite.nativeOriginalCylinderIso C.data.U C.data.Tc C.data.eT C.data.B₀ C.data.O C.data.V

/-- One line-to-original-target map is shared by both restriction squares. -/
def ownedLineRestriction :=
  (ownedLineIso C).hom ≫
    SmoothSite.nativeOriginalLineRestriction C.data.U C.data.Tc C.data.eT C.data.B₀ C.data.O
      C.data.V

/-- The original whole-cylinder map agrees with the one shared line restriction. -/
theorem ownedCylinderIso_comp :
    (ownedCylinderIso C).hom ≫
      SmoothSite.nativeOriginalWholeCylinderMap C.data.U C.data.Tc C.data.eT C.data.B₀ C.data.O
        C.data.V =
    ownedLineRestriction C := by
  change ((ownedLineIso C).hom ≫
    (SmoothSite.nativeOriginalCylinderIso C.data.U C.data.Tc C.data.eT C.data.B₀ C.data.O
      C.data.V).hom) ≫
    ((SmoothSite.nativeOriginalCylinderIso C.data.U C.data.Tc C.data.eT C.data.B₀ C.data.O
      C.data.V).inv ≫
      SmoothSite.nativeOriginalLineRestriction C.data.U C.data.Tc C.data.eT C.data.B₀ C.data.O
        C.data.V) = _
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rfl

/-- The actual ancestry coefficient chain is the shared original line restriction. -/
theorem ancestryLineRestriction_eq :
  let D := C.ancestry
  D.lineToSeed ≫ nativeAffineLineRestriction Γ(C.data.U.left, ⊤) C.data.B₀.ι ≫
      (originalCylinderNativeIso C.data.U C.data.Tc C.data.eT).inv =
    (ownedLineRestriction C).left := by
  intro D
  let N := C.native
  let hline := (OriginalHistoryEndpointEqualities.ownedLineSite_eq C)
  change _ = (N.nativeLineSiteIso ≪≫ eqToIso hline).hom.left ≫
    (SmoothSite.nativeOriginalLineRestriction C.data.U C.data.Tc C.data.eT C.data.B₀ C.data.O
      C.data.V).left
  rw [N.nativeLineSiteIso_transport_hom_left hline]
  let τV := nativeAffineLineRestriction Γ(C.data.O.toScheme, ⊤) C.data.V.ι
  let τO := nativeAffineLineRestriction Γ(C.data.B₀.toScheme, ⊤) C.data.O.ι
  let τB := nativeAffineLineRestriction Γ(C.data.U.left, ⊤) C.data.B₀.ι
  let eN := originalCylinderNativeIso C.data.U C.data.Tc C.data.eT
  change (τV ≫ τO) ≫ τB ≫ eN.inv = (𝟙 _) ≫ ((τV ≫ τO ≫ τB) ≫ eN.inv)
  simp only [Category.id_comp, Category.assoc]

end Motivic.PresheafWithTransfers.OriginalHistoryNativeLine
