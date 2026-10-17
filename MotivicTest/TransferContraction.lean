/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.PresheavesWithTransfers.ContractionNaturality

/-! Consumers of contraction use genuine Laurent restriction and signed exterior transfers. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Motivic Motivic.PresheafWithTransfers

universe v u

variable {k : Type u} [Field k]

example (P : PresheafWithTransfers.{v} k) (X : Cor k) :
    (contractionRestriction P).hom.app (op X) =
      transfer P ((Cor.graphFunctor k).map
        (SmoothSite.contractionOpen (.of k) X.toSmoothSite)) := rfl

example (P : PresheafWithTransfers.{v} k) {X Y : Cor k} (α β : X ⟶ Y) :
    transfer (contraction P) (α - β) =
      transfer (contraction P) α - transfer (contraction P) β := transfer_sub _ _ _

example (P : PresheafWithTransfers.{v} k) {X Y : Cor k} (n : ℤ) (α : X ⟶ Y) :
    transfer (contraction P) (n • α) = n • transfer (contraction P) α :=
  transfer_zsmul _ _ _

example (P : PresheafWithTransfers.{v} k) {X Y : Cor k} (α : X ⟶ Y)
    (s : sections (torusSections P) Y) :
    transfer (contraction P) α ((toContraction P).hom.app (op Y) s) =
      (toContraction P).hom.app (op X)
        (transfer P (FiniteCorrespondence.exteriorIdentity
          (X := X.toSmoothSite) (Y := Y.toSmoothSite) (SmoothSite.torus (.of k)) α) s) :=
  contraction_transfer_apply P α s

example (P : PresheafWithTransfers.{v} k) (X : Cor k) :
    sections (contraction P) X ≅ AddCommGrpCat.of
      (sections (torusSections P) X ⧸
        ((contractionRestriction P).hom.app (op X)).hom.range) :=
  contractionSectionsIsoQuotient P X

example (P : PresheafWithTransfers.{v} k) (hP : IsA1Invariant P) :
    contraction P ≅ contractionKernel P := contractionIsoKernel P hP

example (P : PresheafWithTransfers.{v} k) (hP : IsA1Invariant P) :
    (contractionIsoKernel P hP).inv.hom =
      kernel.ι (torusUnit P).hom ≫ (toContraction P).hom :=
  contractionIsoKernel_inv_quotient P hP

example (P : PresheafWithTransfers.{v} k) (X : Cor k) :
    (torusUnit P).hom.app (op X) ≫
      transfer P ((Cor.graphFunctor k).map (SmoothSite.productBaseIso (.of k) X.toSmoothSite).inv) =
    transfer P ((Cor.graphFunctor k).map (SmoothSite.torusUnitSection (.of k) X.toSmoothSite)) :=
  torusUnit_app_actual P X

example (P : PresheafWithTransfers.{v} k) (hP : IsA1Invariant P) (X : Cor k) :
    sections (contraction P) X ≅
      kernel (transfer P ((Cor.graphFunctor k).map
        (SmoothSite.torusUnitSection (.of k) X.toSmoothSite))) :=
  contractionSectionsIsoUnitKernel P hP X

example (P : PresheafWithTransfers.{v} k) (hP : IsA1Invariant P) :
    (torusUnit P).hom ≫ (torusConstant P).hom +
      (toContraction P).hom ≫ (contractionIsoKernel P hP).hom.hom ≫
        kernel.ι (torusUnit P).hom = 𝟙 (torusSections P).obj :=
  contraction_split_identity P hP

example {P Q : PresheafWithTransfers.{v} k} (η : P ⟶ Q)
    (hP : IsA1Invariant P) (hQ : IsA1Invariant Q) :
    contractionMap η ≫ (contractionIsoKernel Q hQ).hom =
      (contractionIsoKernel P hP).hom ≫ contractionKernelMap η :=
  contractionIsoKernel_hom_naturality η hP hQ
