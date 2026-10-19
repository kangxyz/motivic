/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Source.NativeParameter
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Target.NativeGeometry
/-! # The unchanged target retained puncture maps to the original native puncture

Only redundant whole-open intersections and the already existing marked-open
comparison are removed. The retained scheme and its original target sections
are not replaced or chosen again.

Intended upstream module:
`Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Source.NativePunctureTransport`.

The exact hypotheses are the section variables and declaration signatures below.
This is a standalone API with no current direct import consumer.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme Scheme.Hom
universe u
namespace AlgebraicGeometry.RelativeProjectiveLine
variable (R : Type u) [CommRing R] (O : (Spec (.of R)).Opens) [IsAffine O.toScheme]
  {A : Scheme.{u}} (a : A ⟶ Spec (.of (Polynomial R)))

/-- Remove the redundant intersection with the entire original line. -/
def sourceWholeCoverIso :
    (boundaryBaseCoverOpen (boundaryLineProjection R) a ⊤ O).toScheme ≅
      ((a ≫ boundaryLineProjection R) ⁻¹ᵁ O).toScheme :=
  A.isoOfEq (by simp only [boundaryBaseCoverOpen, boundaryBaseSourceOpen,
    top_inf_eq, Hom.comp_preimage])

omit [IsAffine O.toScheme] in
@[reassoc (attr := simp)]
theorem sourceWholeCoverIso_hom_ι :
    (sourceWholeCoverIso R O a).hom ≫ (a ⁻¹ᵁ boundaryLineProjection R ⁻¹ᵁ O).ι =
      (boundaryBaseCoverOpen (boundaryLineProjection R) a ⊤ O).ι :=
  Scheme.isoOfEq_hom_ι _ _

/-- The same puncture map has the same native coordinates on both presentations. -/
@[reassoc]
theorem sourceWholeCoverIso_native :
    (sourceWholeCoverIso R O a).hom ≫ targetNativeMarked R O a =
      sourceNativeCoverMap R O a := by
  unfold targetNativeMarked sourceNativeCoverMap sourceNativeParameterIso
  simp only [Iso.trans_hom, Iso.symm_hom, ← Category.assoc]
  congr 1
  apply (cancel_mono ((boundaryLineProjection R) ⁻¹ᵁ O).ι).mp
  simp only [Category.assoc, morphismRestrict_ι, sourceWholeParameterIso_hom_ι,
    boundaryBaseCoverMap]
  simpa only [Category.assoc, Hom.comp_preimage] using
    congrArg (fun g => g ≫ a) (sourceWholeCoverIso_hom_ι R O a)

/-- The original target Serre retained scheme is canonically the native puncture. -/
def nativePunctureTransport :
    (((a ≫ chart R 0) ≫ ((𝟙 _) ≫ ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))))
      ⁻¹ᵁ O).toScheme ≅
    (boundaryBaseCoverOpen (boundaryLineProjection R) a ⊤ O).toScheme :=
  (targetMarkedOpenIso R O a).symm ≪≫ (sourceWholeCoverIso R O a).symm

/-- The actual target retained arrow factors through the same native puncture. -/
@[reassoc]
theorem nativePunctureTransport_chart :
    (nativePunctureTransport R O a).hom ≫ sourceNativeCoverMap R O a ≫
      chart Γ(O.toScheme, ⊤) 0 = targetNativeRetained R O (a ≫ chart R 0) := by
  rw [← sourceWholeCoverIso_native R O a]
  simp only [nativePunctureTransport, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id_assoc]
  rw [targetNativeMarked_chart]
  simp only [Iso.inv_hom_id_assoc, targetNativeRetained,
    boundaryBaseRetainedTarget]

end AlgebraicGeometry.RelativeProjectiveLine
