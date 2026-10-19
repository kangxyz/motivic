/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Affine.Coordinates
public import Motivic.Aglib.RingTheory.Smooth.Normal

/-! # Actual coefficient rings after a nonzero principal restriction

All normal-domain and smoothness evidence comes from the original affine integral
smooth base. No normality or smoothness of a replacement base is supplied.


Intended upstream module: `Aglib.AlgebraicGeometry.Sites.Smooth.Affine.PrincipalCoefficient`.
Incoming project consumers: `Motivic.Transfers.Presheaf.Actions.Norm.RefinedNormalization`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates
variable {k : Type u} [Field k]
  (U : SmoothSite (Spec (.of k))) [IsAffine U.left]
attribute [local instance] sectionsAlgebra

/-- The actual principal coefficient open, with its original scheme type. -/
abbrev principalCoefficientOpen (r : Γ(U.left, ⊤)) : (Spec Γ(U.left, ⊤)).Opens :=
  PrimeSpectrum.basicOpen r

/-- The literal principal open of the original coefficient spectrum as a smooth object. -/
def principalCoefficientSite (r : Γ(U.left, ⊤)) : SmoothSite (Spec (.of k)) := by
  let : IsAffine (principalCoefficientOpen U r).toScheme :=
    IsAffineOpen.Spec_basicOpen (R := Γ(U.left, ⊤)) r
  exact SmoothSite.mk ((principalCoefficientOpen U r).ι ≫ U.left.isoSpec.inv ≫ U.hom)

instance principalCoefficientSite_affine (r : Γ(U.left, ⊤)) :
    IsAffine (principalCoefficientSite U r).left :=
  by
    change IsAffineOpen (principalCoefficientOpen U r)
    exact IsAffineOpen.Spec_basicOpen (R := Γ(U.left, ⊤)) r

/-- A nonzero principal restriction retains the generic point of the original base. -/
theorem principalCoefficientSite_integral [IsIntegral U.left]
    (r : Γ(U.left, ⊤)) (hr : r ≠ 0) : IsIntegral (principalCoefficientSite U r).left := by
  have hη : genericPoint (Spec Γ(U.left, ⊤)) ∈ PrimeSpectrum.basicOpen r := by
    rw [genericPoint_eq_bot_of_affine]
    change r ∉ (⊥ : Ideal Γ(U.left, ⊤))
    simpa only [Ideal.mem_bot] using hr
  let : Nonempty (principalCoefficientOpen U r).toScheme := ⟨⟨_, hη⟩⟩
  change IsIntegral (principalCoefficientOpen U r).toScheme
  exact isIntegral_of_isOpenImmersion (principalCoefficientOpen U r).ι

/-- Exact native Γ(D(r)) inputs required by the final normalization constructor. -/
theorem principalCoefficientRing_properties [IsIntegral U.left]
    (r : Γ(U.left, ⊤)) (hr : r ≠ 0) :
    IsDomain Γ((principalCoefficientSite U r).left, ⊤) ∧
      IsIntegrallyClosed Γ((principalCoefficientSite U r).left, ⊤) ∧
      IsNoetherianRing Γ((principalCoefficientSite U r).left, ⊤) := by
  let : IsIntegral (principalCoefficientSite U r).left :=
    principalCoefficientSite_integral U r hr
  exact ⟨inferInstance, _root_.Algebra.Smooth.isIntegrallyClosed_of_smooth_field k _, inferInstance⟩

/-- The actual native coefficient structure map remains smooth. -/
instance principalCoefficient_native_smooth (r : Γ(U.left, ⊤)) :
    Smooth ((principalCoefficientSite U r).left.isoSpec.inv ≫
      (principalCoefficientOpen U r).ι ≫ U.left.isoSpec.inv ≫ U.hom) := by
  change Smooth ((principalCoefficientSite U r).left.isoSpec.inv ≫
    (principalCoefficientSite U r).hom)
  infer_instance

end AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates
