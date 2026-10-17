/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.PresheavesWithTransfers.ContractionSheaf

/-!
# Consumers of actual HI Nisnevich contraction

The field and coefficient universes are independent. These consumers retain
the literal Laurent quotient and unit-section kernel, actual product maps and
signed exterior transfers. No transfer sheafification or cohomology assumption
is supplied.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Motivic

universe v u

namespace MotivicTest.Transfers.ContractionSheaf

variable {k : Type u} [Field k]

/-- All genuine parameter sections of a transfer sheaf remain Nisnevich. -/
theorem parameter_sections_sheaf (F : SheafWithTransfers.{v} k)
    (T : SmoothSite (Spec (.of k))) [GeometricallyIntegral T.hom] :
    PresheafWithTransfers.IsNisnevichSheaf k
      (PresheafWithTransfers.withParameter F.obj T) :=
  PresheafWithTransfers.withParameter_isNisnevichSheaf F.obj F.property T

/-- Ordinary restrictions use exactly the literal product of the original map. -/
theorem parameter_graph_restriction (F : SheafWithTransfers.{v} k)
    (T : SmoothSite (Spec (.of k))) [GeometricallyIntegral T.hom]
    {X Y : SmoothSite (Spec (.of k))} (f : X ⟶ Y) :
    ((PresheafWithTransfers.toPresheaf k).obj
      (PresheafWithTransfers.withParameter F.obj T)).map f.op =
      ((SheafWithTransfers.toSheaf k).obj F).obj.map
        (SmoothSite.productMap f (𝟙 T)).op := by
  change PresheafWithTransfers.transfer F.obj
      ((Cor.parameterProduct T).map ((Cor.graphFunctor k).map f)) = _
  rw [Cor.parameterProduct_graph]
  rfl

/-- The original cokernel presheaf itself satisfies the sheaf condition. -/
theorem literal_contraction_is_sheaf (F : SheafWithTransfers.{v} k)
    (hF : F.obj.IsA1Invariant) :
    PresheafWithTransfers.IsNisnevichSheaf k
      (PresheafWithTransfers.contraction F.obj) :=
  PresheafWithTransfers.contraction_isNisnevichSheaf F.obj F.property hF

/-- Bundling the sheaf condition keeps the original presheaf and coefficient universe. -/
theorem literal_underlying_presheaf (F : SheafWithTransfers.{v} k)
    (hF : F.obj.IsA1Invariant) :
    (SheafWithTransfers.contraction F hF).obj =
      PresheafWithTransfers.contraction F.obj := rfl

/-- Section values remain the literal Laurent quotient, without sheafifying the quotient. -/
def actual_sections_quotient (F : SheafWithTransfers.{v} k)
    (hF : F.obj.IsA1Invariant) (X : Cor k) :
    PresheafWithTransfers.sections (SheafWithTransfers.contraction F hF).obj X ≅
      AddCommGrpCat.of (PresheafWithTransfers.sections
        (PresheafWithTransfers.torusSections F.obj) X ⧸
          ((PresheafWithTransfers.contractionRestriction F.obj).hom.app (op X)).hom.range) :=
  PresheafWithTransfers.contractionSectionsIsoQuotient F.obj X

/-- The same sections are the kernel of restriction along the actual unit section. -/
def actual_sections_unit_kernel (F : SheafWithTransfers.{v} k)
    (hF : F.obj.IsA1Invariant) (X : Cor k) :
    PresheafWithTransfers.sections (SheafWithTransfers.contraction F hF).obj X ≅
      kernel (PresheafWithTransfers.transfer F.obj ((Cor.graphFunctor k).map
        (SmoothSite.torusUnitSection (.of k) X.toSmoothSite))) :=
  PresheafWithTransfers.contractionSectionsIsoUnitKernel F.obj hF X

/-- Signed transfer actions on quotient representatives are still the actual exterior actions. -/
theorem signed_transfer_on_representative (F : SheafWithTransfers.{v} k)
    (hF : F.obj.IsA1Invariant) {X Y : Cor k} (α β : X ⟶ Y)
    (s : PresheafWithTransfers.sections (PresheafWithTransfers.torusSections F.obj) Y) :
    PresheafWithTransfers.transfer (SheafWithTransfers.contraction F hF).obj
        ((-2 : ℤ) • (α - β)) ((PresheafWithTransfers.toContraction F.obj).hom.app (op Y) s) =
      (PresheafWithTransfers.toContraction F.obj).hom.app (op X)
        (PresheafWithTransfers.transfer F.obj
          (FiniteCorrespondence.exteriorIdentity (X := X.toSmoothSite) (Y := Y.toSmoothSite)
            (SmoothSite.torus (.of k)) ((-2 : ℤ) • (α - β))) s) :=
  PresheafWithTransfers.contraction_transfer_apply F.obj _ s

/-- Actual homotopy invariance survives on the constructed sheaf's original graph restrictions. -/
theorem actual_projection_isIso (F : SheafWithTransfers.{v} k)
    (hF : F.obj.IsA1Invariant) (X : SmoothSite (Spec (.of k))) :
    IsIso (((SheafWithTransfers.toSheaf k).obj
      (SheafWithTransfers.contraction F hF)).obj.map
        (SmoothSite.a1Projection (.of k) X).op) :=
  SheafWithTransfers.contraction_isA1Invariant F hF X

end MotivicTest.Transfers.ContractionSheaf
