/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.Presheaf.Actions.Norm.NativeRefinement.OriginalHistoryLine
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.AffineLine.NativeMiddleInput
public import Motivic.Transfers.Presheaf.Actions.Norm.NativeRefinement.NativeOriginalRefinedSource

/-! # Original-history restriction assembly

Over a field, construct the original source and puncture scheme restrictions from the
ancestry maps of one fixed history. Their commutation with the same
`ownedLineRestriction` equips them with the actual native smooth-site
morphisms `sourceRestriction` and `punctureRestriction`.

The resulting `transport` satisfies the five literal compatibility laws used
by the lifting adapter. The original affine coefficient opens, full marked
data and boundary/source/target witnesses remain fixed throughout.
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

namespace Motivic.PresheafWithTransfers.OriginalHistoryNativeRestrictions
variable {k : Type u} [Field k] (C : OriginalHistoryContext k)

/-- The original source restriction for one variable history. -/
def sourceRestrictionScheme :
    (C.native).Y ⟶ C.data.Y.left :=
  (C.ancestry).sourceToSeed ≫ C.data.W.ι

/-- The original source representative is restricted along the shared coefficient line. -/
theorem sourceRestrictionScheme_square :
  let N := C.native
  (sourceRestrictionScheme C) ≫ C.data.p.left =
    N.p ≫ (OriginalHistoryNativeLine.ownedLineRestriction C).left := by
  intro N
  let D := C.ancestry
  let τB := nativeAffineLineRestriction Γ(C.data.U.left, ⊤) C.data.B₀.ι
  let eN := originalCylinderNativeIso C.data.U C.data.Tc C.data.eT
  have hB : D.seedP ≫ τB = C.data.W.ι ≫ C.data.p.left ≫ eN.hom :=
    Scheme.originalAffineRefinedNativeMap_coordinate Γ(C.data.U.left, ⊤) eN
      (originalRepresentativeCoefficientMap C.data.U C.data.Tc C.data.eT)
      (originalCylinderNativeIso_projection C.data.U C.data.Tc C.data.eT) C.data.B₀
        C.data.p.left C.data.W C.data.hW
  have hcat := SmoothSite.threeRestrictionSquares N.p D.seedP D.seedP C.data.p.left
    D.sourceToSeed (𝟙 _) C.data.W.ι D.lineToSeed (𝟙 _) τB eN (Iso.refl _)
    D.sourceSquare (by simp only [Category.comp_id, Category.id_comp]) hB
  have hs : (D.sourceToSeed ≫ C.data.W.ι) ≫ C.data.p.left =
      N.p ≫ (D.lineToSeed ≫ τB ≫ eN.inv) := by
    simpa only [Category.assoc, Category.id_comp, Category.comp_id,
      Iso.refl_hom, Iso.refl_inv] using hcat
  exact hs.trans (congrArg (fun f => N.p ≫ f)
    (OriginalHistoryNativeLine.ancestryLineRestriction_eq C))

end Motivic.PresheafWithTransfers.OriginalHistoryNativeRestrictions

namespace Motivic.PresheafWithTransfers.OriginalHistoryNativePunctureRestrictions
variable {k : Type u} [Field k] (C : OriginalHistoryContext k)

/-- The original puncture restriction for one variable history. -/
def punctureRestrictionScheme :
    (C.native).A ⟶ C.data.A.left :=
  (C.ancestry).punctureToSeed ≫
    ((C.data.a.left ≫ originalRepresentativeCoefficientMap C.data.U C.data.Tc C.data.eT) ⁻¹ᵁ
      C.data.B₀).ι

/-- The original puncture representative is restricted along the shared coefficient line. -/
theorem punctureRestrictionScheme_square :
  let N := C.native
  (punctureRestrictionScheme C) ≫ C.data.a.left =
    N.a ≫ (OriginalHistoryNativeLine.ownedLineRestriction C).left := by
  intro N
  let D := C.ancestry
  let τB := nativeAffineLineRestriction Γ(C.data.U.left, ⊤) C.data.B₀.ι
  let eN := originalCylinderNativeIso C.data.U C.data.Tc C.data.eT
  let q := originalRepresentativeCoefficientMap C.data.U C.data.Tc C.data.eT
  let i₀ := ((C.data.a.left ≫ q) ⁻¹ᵁ C.data.B₀).ι
  have hB : D.seedAmap ≫ τB = i₀ ≫ C.data.a.left ≫ eN.hom := by
    have hc : (Scheme.originalAffineRefinedTargetIso Γ(C.data.U.left, ⊤) eN q
        (originalCylinderNativeIso_projection C.data.U C.data.Tc C.data.eT) C.data.B₀).hom ≫ τB =
        (q ⁻¹ᵁ C.data.B₀).ι ≫ eN.hom :=
      Scheme.originalAffineRefinedTargetIso_coordinate Γ(C.data.U.left, ⊤) eN q
        (originalCylinderNativeIso_projection C.data.U C.data.Tc C.data.eT) C.data.B₀
    have hr := morphismRestrict_ι C.data.a.left (q ⁻¹ᵁ C.data.B₀)
    exact (Category.assoc (C.data.a.left ∣_ (q ⁻¹ᵁ C.data.B₀))
      (Scheme.originalAffineRefinedTargetIso Γ(C.data.U.left, ⊤) eN q
        (originalCylinderNativeIso_projection C.data.U C.data.Tc C.data.eT) C.data.B₀).hom τB).trans
      ((congrArg (fun m => (C.data.a.left ∣_ (q ⁻¹ᵁ C.data.B₀)) ≫ m) hc).trans
        ((Category.assoc (C.data.a.left ∣_ (q ⁻¹ᵁ C.data.B₀)) (q ⁻¹ᵁ C.data.B₀).ι eN.hom).symm.trans
          ((congrArg (fun m => m ≫ eN.hom) hr).trans
            (Category.assoc i₀ C.data.a.left eN.hom))))
  have hcat := SmoothSite.threeRestrictionSquares N.a D.seedAmap D.seedAmap C.data.a.left
    D.punctureToSeed (𝟙 _) i₀ D.lineToSeed (𝟙 _) τB eN (Iso.refl _)
    D.punctureSquare (by simp only [Category.comp_id, Category.id_comp]) hB
  have hs : (D.punctureToSeed ≫ i₀) ≫ C.data.a.left =
      N.a ≫ (D.lineToSeed ≫ τB ≫ eN.inv) := by
    simpa only [Category.assoc, Category.id_comp, Category.comp_id,
      Iso.refl_hom, Iso.refl_inv] using hcat
  exact hs.trans (congrArg (fun f => N.a ≫ f)
    (OriginalHistoryNativeLine.ancestryLineRestriction_eq C))

end Motivic.PresheafWithTransfers.OriginalHistoryNativePunctureRestrictions

namespace Motivic.PresheafWithTransfers.OriginalHistoryNativeSiteAssembly
variable {k : Type u} [Field k] (C : OriginalHistoryContext k)

/-- Package the source restriction in the actual smooth site. -/
def sourceRestriction : (C.native).toInput.siteY ⟶ C.data.Y :=
  (C.native).sourceRestrictionOfSquare C.data.p
    (OriginalHistoryNativeLine.ownedLineRestriction C)
      (OriginalHistoryNativeRestrictions.sourceRestrictionScheme C)
      (OriginalHistoryNativeRestrictions.sourceRestrictionScheme_square C)

/-- The source restriction square uses the one shared original line map. -/
theorem sourceRestriction_comp :
  let N := C.native
  (sourceRestriction C) ≫ C.data.p = N.toInput.pSite
      ≫ (OriginalHistoryNativeLine.ownedLineRestriction C) := by
  intro N
  exact N.sourceRestrictionOfSquare_comp C.data.p (OriginalHistoryNativeLine.ownedLineRestriction C)
      (OriginalHistoryNativeRestrictions.sourceRestrictionScheme C)
      (OriginalHistoryNativeRestrictions.sourceRestrictionScheme_square C)

/-- The original puncture restriction, with its genuine native site structure. -/
def punctureRestriction : (C.native).toInput.siteA ⟶ C.data.A :=
  (C.native).punctureRestrictionOfSquare C.data.a
    (OriginalHistoryNativeLine.ownedLineRestriction C)
      (OriginalHistoryNativePunctureRestrictions.punctureRestrictionScheme C)
      (OriginalHistoryNativePunctureRestrictions.punctureRestrictionScheme_square C)

/-- The puncture restriction square uses the one shared original line map. -/
theorem punctureRestriction_comp :
  let N := C.native
  (punctureRestriction C) ≫ C.data.a = N.aSite ≫
      (OriginalHistoryNativeLine.ownedLineRestriction C) := by
  intro N
  exact N.punctureRestrictionOfSquare_comp C.data.a
    (OriginalHistoryNativeLine.ownedLineRestriction C)
      (OriginalHistoryNativePunctureRestrictions.punctureRestrictionScheme C)
      (OriginalHistoryNativePunctureRestrictions.punctureRestrictionScheme_square C)

/-- The existing five-map transport on the actual native source and puncture. -/
def transport :=
  (C.native).nativeTransport
    (OriginalHistoryNativeLine.ownedCylinderIso C) (punctureRestriction C) (sourceRestriction C)

/-- All five actual transport laws follow from the proved original restriction squares. -/
theorem transport_compatible :
  let N := C.native
  let e := (OriginalHistoryNativeLine.ownedCylinderIso C)
  (transport C).Compatible C.data.a C.data.p
      (N.aSite ≫ e.hom) (N.toInput.pSite ≫ e.hom)
    (punctureRestriction C) (sourceRestriction C) := by
  intro N e
  exact N.nativeTransport_compatible C.data.a C.data.p
    (OriginalHistoryNativeLine.ownedLineRestriction C) e
    (punctureRestriction C) (sourceRestriction C)
    (punctureRestriction_comp C) (sourceRestriction_comp C)

end Motivic.PresheafWithTransfers.OriginalHistoryNativeSiteAssembly
