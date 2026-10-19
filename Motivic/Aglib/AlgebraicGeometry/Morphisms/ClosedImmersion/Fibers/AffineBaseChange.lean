/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Morphisms.ClosedImmersion.Fibers.AffinePresentation
public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.EtaleComparison.AffinePrincipalDivisorChart

/-! # Base change of the original affine closed fiber -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The quotient by the extended ideal presents the original closed fiber after
any affine base change, in particular after a principal localization. -/
theorem exists_quotient_isPullback_of_kernel_of_map_eq
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (U : X.Opens) (hU : IsAffineOpen U) (I : Ideal Γ(X, U))
    (hI : RingHom.ker (i.app U).hom = I)
    {B : Type u} [CommRing B] (f : Γ(X, U) →+* B)
    (J : Ideal B) (hJ : I.map f = J) :
    ∃ j : Spec (.of (B ⧸ J)) ⟶ Z,
      IsPullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) j
        (Spec.map (CommRingCat.ofHom f) ≫ hU.fromSpec) i := by
  obtain ⟨j, hj⟩ := exists_quotient_isPullback_of_kernel i U hU I hI
  obtain ⟨q, hq⟩ := Scheme.exists_isPullback_Spec_quotient_of_map_eq f I J hJ
  exact ⟨q ≫ j, hq.paste_vert hj⟩

end AlgebraicGeometry.Scheme.Hom
