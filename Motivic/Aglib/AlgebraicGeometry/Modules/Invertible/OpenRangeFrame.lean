/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.OriginalAffinePrescribedNeighborhood
public import Aglib.AlgebraicGeometry.Modules.Pullback.OpenRestriction

/-! # Original prescribed frames on their actual open ranges -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules.Invertible

/-- Transport the actual pulled-back frame to the over-site of the same open
range, using only the canonical open-immersion equivalence. -/
def overFrameOnOpensRange {P U : Scheme.{u}} (v : U ⟶ P) [IsOpenImmersion v]
    (M : P.Modules)
    (d : (Modules.pullback v).obj M ≅ SheafOfModules.unit U.ringCatSheaf) :
    M.over v.opensRange ≅ SheafOfModules.unit (P.ringCatSheaf.over v.opensRange) :=
  (Modules.overEquiv v.opensRange).functor.preimageIso
    ((Modules.overFunctorEquiv v.opensRange).app M ≪≫
      (Modules.restrictFunctorIsoPullback v.opensRange.ι).app M ≪≫
      ((Modules.pullbackCongr v.isoOpensRange_inv_comp).app M).symm ≪≫
      ((Modules.pullbackComp v.isoOpensRange.inv v).app M).symm ≪≫
      (Modules.pullback v.isoOpensRange.inv).mapIso d ≪≫
      pullbackUnitIso v.isoOpensRange.inv ≪≫ (Modules.overUnitIso v.opensRange).symm)

/-- Actual extension data retain the original boundary map and exact prescribed
frame equation, rather than only remembering that some trivialization exists. -/
structure PrescribedAffineFrameExtension {P B : Scheme.{u}} (A : P.affineOpens)
    (b : B ⟶ A.val.toScheme) (L : LineBundle P)
    (e : (Modules.pullback b).obj (pullbackLineBundle A.val.ι L).val ≅
      SheafOfModules.unit B.ringCatSheaf) where
  /-- The actual affine neighborhood produced by the principal construction. -/
  neighborhood : Scheme.{u}
  /-- Affineness of that neighborhood. -/
  affine : IsAffine neighborhood
  /-- Its original inclusion into the given affine chart. -/
  inclusion : neighborhood ⟶ A.val.toScheme
  /-- The inclusion is an open immersion, not a replacement cover. -/
  openImmersion : IsOpenImmersion inclusion
  /-- The entire original boundary factors through the neighborhood. -/
  boundaryLift : B ⟶ neighborhood
  /-- The factorization retains the original boundary map. -/
  boundary_eq : boundaryLift ≫ inclusion = b
  /-- The actual extended frame of the original pulled-back line. -/
  frame : (Modules.pullback inclusion).obj (pullbackLineBundle A.val.ι L).val ≅
    SheafOfModules.unit neighborhood.ringCatSheaf
  /-- Restriction recovers the exact given frame through the native comparisons. -/
  frame_eq : ((Modules.pullbackCongr boundary_eq).app
        (pullbackLineBundle A.val.ι L).val).symm ≪≫
      ((Modules.pullbackComp boundaryLift inclusion).app
        (pullbackLineBundle A.val.ι L).val).symm ≪≫
      (Modules.pullback boundaryLift).mapIso frame ≪≫ pullbackUnitIso boundaryLift = e

/-- The original affine producer constructs all extension data and their exact
boundary equation internally. -/
theorem nonempty_prescribedAffineFrameExtension {P B : Scheme.{u}}
    (A : P.affineOpens) (b : B ⟶ A.val.toScheme) [IsClosedImmersion b]
    (L : LineBundle P)
    (e : (Modules.pullback b).obj (pullbackLineBundle A.val.ι L).val ≅
      SheafOfModules.unit B.ringCatSheaf) :
    Nonempty (PrescribedAffineFrameExtension A b L e) := by
  have : IsAffine A.val.toScheme := A.property
  have : IsAffine B := isAffine_of_isAffineHom b
  obtain ⟨U, hU, v, hv, c, hc, d, hd⟩ :=
    exists_original_affine_open_prescribed_frame b (pullbackLineBundle A.val.ι L) e
  exact ⟨⟨U, hU, v, hv, c, hc, d, hd⟩⟩

namespace PrescribedAffineFrameExtension

variable {P B : Scheme.{u}} {A : P.affineOpens} {b : B ⟶ A.val.toScheme}
  {L : LineBundle P}
  {e : (Modules.pullback b).obj (pullbackLineBundle A.val.ι L).val ≅
    SheafOfModules.unit B.ringCatSheaf}
  (E : PrescribedAffineFrameExtension A b L e)

instance : IsAffine E.neighborhood := E.affine
instance : IsOpenImmersion E.inclusion := E.openImmersion

/-- The unchanged inclusion into the original compact ambient scheme. -/
def ambientInclusion : E.neighborhood ⟶ P := E.inclusion ≫ A.val.ι

instance : IsOpenImmersion E.ambientInclusion := by
  dsimp only [ambientInclusion]
  infer_instance

/-- The frame of the original line, before any open-range transport. -/
def ambientFrame : (Modules.pullback E.ambientInclusion).obj L.val ≅
    SheafOfModules.unit E.neighborhood.ringCatSheaf :=
  ((Modules.pullbackComp E.inclusion A.val.ι).app L.val).symm ≪≫ E.frame

/-- The actual affine open in the original ambient scheme. -/
def affineOpen : P.affineOpens :=
  ⟨E.ambientInclusion.opensRange, isAffineOpen_opensRange E.ambientInclusion⟩

/-- The over-site frame used by the native order-cancellation construction. -/
def overFrame : L.val.over E.affineOpen.val ≅
    SheafOfModules.unit (P.ringCatSheaf.over E.affineOpen.val) :=
  overFrameOnOpensRange E.ambientInclusion L.val E.ambientFrame

/-- No point or thickened component of the prescribed boundary is removed. -/
theorem boundary_range_subset : Set.range (b ≫ A.val.ι) ⊆ (E.affineOpen.val : Set P) := by
  rintro _ ⟨x, rfl⟩
  change (b ≫ A.val.ι) x ∈ Set.range E.ambientInclusion
  refine ⟨E.boundaryLift x, ?_⟩
  change (E.boundaryLift ≫ E.ambientInclusion) x = (b ≫ A.val.ι) x
  rw [ambientInclusion, ← Category.assoc, E.boundary_eq]

/-- In the nonempty-boundary branch the very same frame open is nonempty. -/
instance [Nonempty B] : Nonempty E.affineOpen.val := by
  obtain ⟨x⟩ := ‹Nonempty B›
  exact ⟨⟨(b ≫ A.val.ι) x, E.boundary_range_subset ⟨x, rfl⟩⟩⟩

end PrescribedAffineFrameExtension

end AlgebraicGeometry.Scheme.Modules.Invertible
