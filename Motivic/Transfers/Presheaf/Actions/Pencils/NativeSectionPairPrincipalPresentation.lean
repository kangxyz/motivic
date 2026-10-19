/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Transfers.Presheaf.Actions.Pencils.NativeSectionPairTransferAction
public import Motivic.Transfers.Presheaf.Actions.Pencils.NativeOriginalPairTransferAction

/-! # The two actual E3 principal presentations

Only proof and smooth-site instance presentations differ. The original schemes,
arrows, open, function, and its unit witness remain fixed.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Scheme Scheme.Hom Scheme.RelativeCurvePencil
open AlgebraicGeometry.FiniteSchemeNormBaseChange
universe u
namespace Motivic.PresheafWithTransfers
attribute [local instance] Cor.instSmoothOfSmoothOfRelativeDimensionOfNatNat

variable {k : Type u} [Field k] {S C P X Y K A : Scheme.{u}}
  [IsAffine S] [IsAffine Y] [IsAffine K] [IsAffine A]
  (t : S ⟶ Spec (.of k)) [Smooth t]
  (π : P ⟶ S) [IsProper π] (f : C ⟶ P)
  (j : Y ⟶ C) [SmoothOfRelativeDimension 1 (j ≫ (f ≫ π))]
  (α : K ⟶ Y) [Smooth α]
  (jA : X ⟶ P) [IsOpenImmersion jA]
  (a : A ⟶ X) [IsOpenImmersion a]
  [SmoothOfRelativeDimension 1 ((a ≫ jA) ≫ π)]

local notation "b" => (α ≫ j ≫ f ≫ π)
local notation "T" => (pullback b π : Scheme)
local notation "q" => (pullback.fst b π)
local notation "jT" => (retainedProductInclusion b π (a ≫ jA))
local notation "g" => (pullback.snd b ((a ≫ jA) ≫ π))
local notation "siteK" => (relativeCommonSite k t (f ≫ π) j α)
local notation "siteQ" => (relativeTargetSite k t π (a ≫ jA))

local instance : IsAffine (retainedProduct b π (a ≫ jA)) :=
  retainedProduct_affine b π (a ≫ jA)
local instance : SmoothOfRelativeDimension 1 (jT ≫ q) :=
  retainedProduct_smooth b π (a ≫ jA)
local instance : IsAffine (siteK).left := inferInstanceAs (IsAffine K)

/-- The actual native-zero witness and the canonical Cor RHS define the same
principal correspondence; no equality of correspondences is an input. -/
theorem sectionPair_principal_native_eq_canonical
    [IsIntegral T] [IsNoetherian T]
    (W : (T).Opens) [Nonempty W] (r : Γ(T, W)) (hr : IsUnit r)
    (hNative hCor : (Set.range jT)ᶜ ⊆ (W : Set T))
    (hbNative hbCor : jT ≫ q ≫ (b ≫ t) = g ≫ (((a ≫ jA) ≫ π) ≫ t)) :
    (letI : ∀ {B D : Scheme.{u}} (v : B ⟶ D)
        [SmoothOfRelativeDimension 1 v], Smooth v :=
      @Motivic.PresheafWithTransfers.instSmoothOfSmoothOfRelativeDimensionOfNatNat_1
     (PrincipalOrderCorrespondence.correspondence
       (X := relativeCommonSite k t (f ≫ π) j α)
       (Y := relativeTargetSite k t π (a ≫ jA))
       q jT W hNative r hr g hbNative : Cor.mk siteK ⟶ Cor.mk siteQ)) =
    (PrincipalOrderCorrespondence.correspondence
      (X := siteK) (Y := siteQ) q jT W hCor r hr g hbCor :
        Cor.mk siteK ⟶ Cor.mk siteQ) := by
  rfl

end Motivic.PresheafWithTransfers
