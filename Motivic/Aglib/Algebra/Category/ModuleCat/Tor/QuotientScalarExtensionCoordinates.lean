/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Category.ModuleCat.Tor.QuotientScalarExtension

/-!
# Coordinates of quotient scalar extension

The quotient-versus-ambient scalar-extension comparison retains pure tensors.
These formulas expose the maps needed for naturality and restriction coherence.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct ChangeOfRings

universe u

namespace ModuleCat.TorComparison

variable {R S : Type u} [CommRing R] [CommRing S]

/-- The inverse comparison is the literal quotient projection on the first tensor factor. -/
@[simp] theorem quotientScalarExtensionIso_inv_tmul (f : R →+* S) (I : Ideal R)
    (M : ModuleCat.{u} R) (hM : I ≤ Module.annihilator R M) (s : S) (m : M) :
    letI := quotientModuleAction I M hM
    (quotientScalarExtensionIso f I M hM).inv (s ⊗ₜ[R,f] m) =
      Ideal.Quotient.mk (I.map f) s ⊗ₜ[R ⧸ I,supportQuotientMap f I]
        (m : quotientModule I M hM) := by
  let := f.toAlgebra
  let := quotientModuleAction I M hM
  let : Algebra (R ⧸ I) (S ⧸ I.map f) :=
    inferInstanceAs (Algebra (R ⧸ I) (S ⧸ I.map (algebraMap R S)))
  let : IsScalarTower R (R ⧸ I) (S ⧸ I.map f) :=
    inferInstanceAs (IsScalarTower R (R ⧸ I) (S ⧸ I.map (algebraMap R S)))
  let : Algebra.IsPushout R S (R ⧸ I) (S ⧸ I.map f) := quotientScalarSquareIsPushout I
  let : IsScalarTower R (R ⧸ I) M :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  change (TensorProduct.congr
    (SupportModules.regularBaseEquiv (R ⧸ I) (S ⧸ I.map f))
    (LinearEquiv.refl (R ⧸ I) M)).symm
      ((Algebra.IsPushout.cancelBaseChange R S (R ⧸ I) (S ⧸ I.map f) M).symm
        ((TensorProduct.congr (SupportModules.regularBaseEquiv R S)
          (LinearEquiv.refl R M)) (s ⊗ₜ[R,f] m))) = _
  have h₂ : (TensorProduct.congr (SupportModules.regularBaseEquiv R S)
      (LinearEquiv.refl R M)) (s ⊗ₜ[R,f] m) = s ⊗ₜ[R] m := rfl
  rw [h₂, Algebra.IsPushout.cancelBaseChange_symm_tmul]
  rfl

/-- The forward comparison takes a quotient scalar representative to its ambient tensor. -/
@[simp] theorem quotientScalarExtensionIso_hom_tmul (f : R →+* S) (I : Ideal R)
    (M : ModuleCat.{u} R) (hM : I ≤ Module.annihilator R M) (s : S) (m : M) :
    letI := quotientModuleAction I M hM
    (quotientScalarExtensionIso f I M hM).hom
      (Ideal.Quotient.mk (I.map f) s ⊗ₜ[R ⧸ I,supportQuotientMap f I]
        (m : quotientModule I M hM)) = s ⊗ₜ[R,f] m := by
  let := quotientModuleAction I M hM
  have h := congrArg (quotientScalarExtensionIso f I M hM).hom
    (quotientScalarExtensionIso_inv_tmul f I M hM s m)
  exact h.symm.trans (ModuleCat.hom_inv_apply (quotientScalarExtensionIso f I M hM)
    (s ⊗ₜ[R,f] m))

/-- Quotient-versus-ambient scalar extension is natural in every actual ambient-linear map. -/
@[reassoc] theorem quotientScalarExtensionIso_hom_naturality (f : R →+* S) (I : Ideal R)
    (M N : ModuleCat.{u} R) (hM : I ≤ Module.annihilator R M)
    (hN : I ≤ Module.annihilator R N) (φ : M ⟶ N) :
    (ModuleCat.extendScalars (supportQuotientMap f I)).map (quotientLinearMap I hM hN φ) ≫
        (quotientScalarExtensionIso f I N hN).hom =
      (quotientScalarExtensionIso f I M hM).hom ≫
        quotientLinearMap (I.map f)
          (map_support_le_annihilator_extendScalars f I M hM)
          (map_support_le_annihilator_extendScalars f I N hN)
          ((ModuleCat.extendScalars f).map φ) := by
  let := quotientModuleAction I M hM
  let := quotientModuleAction I N hN
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  change (quotientScalarExtensionIso f I N hN).hom
      ((1 : S ⧸ I.map f) ⊗ₜ[R ⧸ I,supportQuotientMap f I] (φ m : quotientModule I N hN)) =
    ((ModuleCat.extendScalars f).map φ)
      ((quotientScalarExtensionIso f I M hM).hom
        ((1 : S ⧸ I.map f) ⊗ₜ[R ⧸ I,supportQuotientMap f I] (m : quotientModule I M hM)))
  have h₁ := quotientScalarExtensionIso_hom_tmul f I M hM 1 m
  have h₂ := quotientScalarExtensionIso_hom_tmul f I N hN 1 (φ m)
  simp only [map_one] at h₁ h₂
  rw [h₁, h₂]
  rfl

end ModuleCat.TorComparison
