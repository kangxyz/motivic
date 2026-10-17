/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.TorComparison.FlatBaseChangeQuotient
public import Motivic.Algebra.Homology.TorComparison.SupportModulesAlgebra
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Quotient scalar extension versus ambient scalar extension

The actual quotient square is a pushout. Its cancellation comparison identifies
extension over the induced support-quotient ring map with extension over the
ambient ring map, equipped with the constructed support action. No flatness
is required for this change-of-scalars identification.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct ChangeOfRings

universe u

namespace Motivic.TorComparison

variable {R S : Type u} [CommRing R] [CommRing S]

private theorem addEquiv_smul_add {X Y : Type u} [AddCommGroup X] [AddCommGroup Y]
    [Module S X] [Module S Y] (a : X ≃+ Y) (s : S) (x y : X)
    (hx : a (s • x) = s • a x) (hy : a (s • y) = s • a y) :
    a (s • (x + y)) = s • a (x + y) := by
  rw [smul_add, map_add, hx, hy, map_add, smul_add]

/-- The literal quotient of the ambient scalar-extension square is a pushout. -/
instance quotientScalarSquareIsPushout [Algebra R S] (I : Ideal R) :
    Algebra.IsPushout R S (R ⧸ I) (S ⧸ I.map (algebraMap R S)) where
  out := IsBaseChange.of_equiv
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S I).symm.toLinearEquiv (by
      intro x
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
      simp [Algebra.smul_def])

/-- The actual induced ring map on the scheme-theoretic support quotients. -/
def supportQuotientMap (f : R →+* S) (I : Ideal R) : R ⧸ I →+* S ⧸ I.map f :=
  Ideal.quotientMap (I.map f) f Ideal.le_comap_map

/-- The induced quotient map commutes with the two literal quotient projections. -/
@[simp] theorem supportQuotientMap_mk (f : R →+* S) (I : Ideal R) (r : R) :
    supportQuotientMap f I (Ideal.Quotient.mk I r) = Ideal.Quotient.mk (I.map f) (f r) :=
  rfl

/-- Support-quotient scalar extension agrees with ambient scalar extension as an
ambient target-ring module, by the actual quotient pushout. -/
def quotientScalarExtensionAmbientIso (f : R →+* S) (I : Ideal R)
    (M : ModuleCat.{u} R) (hM : I ≤ Module.annihilator R M) :
    (ModuleCat.restrictScalars (Ideal.Quotient.mk (I.map f))).obj
      ((ModuleCat.extendScalars (supportQuotientMap f I)).obj (quotientModule I M hM)) ≅
    (ModuleCat.extendScalars f).obj M := by
  letI := f.toAlgebra
  letI := quotientModuleAction I M hM
  letI : Algebra (R ⧸ I) (S ⧸ I.map f) :=
    inferInstanceAs (Algebra (R ⧸ I) (S ⧸ I.map (algebraMap R S)))
  letI : IsScalarTower R (R ⧸ I) (S ⧸ I.map f) :=
    inferInstanceAs (IsScalarTower R (R ⧸ I) (S ⧸ I.map (algebraMap R S)))
  letI : Algebra.IsPushout R S (R ⧸ I) (S ⧸ I.map f) :=
    quotientScalarSquareIsPushout I
  letI : IsScalarTower R (R ⧸ I) M :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let X : ModuleCat.{u} S :=
    (ModuleCat.restrictScalars (Ideal.Quotient.mk (I.map f))).obj
      ((ModuleCat.extendScalars (supportQuotientMap f I)).obj (quotientModule I M hM))
  let Y : ModuleCat.{u} S := (ModuleCat.extendScalars f).obj M
  let e := Algebra.IsPushout.cancelBaseChange R S (R ⧸ I) (S ⧸ I.map f) M
  let a₁ : X ≃+ ((S ⧸ I.map f) ⊗[R ⧸ I] M) := (TensorProduct.congr
    (SupportModules.regularBaseEquiv (R ⧸ I) (S ⧸ I.map f))
    (LinearEquiv.refl (R ⧸ I) M)).toAddEquiv
  let a₂ : Y ≃+ (S ⊗[R] M) := (TensorProduct.congr (SupportModules.regularBaseEquiv R S)
    (LinearEquiv.refl R M)).toAddEquiv
  let a : X ≃+ Y := a₁.trans (e.toAddEquiv.trans a₂.symm)
  let e' : X ≃ₗ[S] Y :=
    { __ := a
      map_smul' := by
        intro s x
        apply a₂.injective
        have ha (z : X) : a₂ (a z) = e (a₁ z) :=
          a₂.apply_symm_apply (e (a₁ z))
        change a₂ (a (s • x)) = a₂ (s • a x)
        rw [ha]
        have h₁ : a₁ (s • x) = s • a₁ x := by
          induction x using TensorProduct.inductionOn with
          | tmul b m =>
            change S ⧸ I.map f at b
            change M at m
            change (Ideal.Quotient.mk (I.map f) s * b) ⊗ₜ[R ⧸ I] m =
              s • (b ⊗ₜ[R ⧸ I] m)
            rw [TensorProduct.smul_tmul', Algebra.smul_def]
            rfl
          | add x y hx hy => exact addEquiv_smul_add a₁ s (x : X) y hx hy
        have h₂ : ∀ y : Y, a₂ (s • y) = s • a₂ y := by
          intro y
          induction y using TensorProduct.inductionOn with
          | tmul t m => rfl
          | add x y hx hy => exact addEquiv_smul_add a₂ s (x : Y) y hx hy
        rw [h₁, h₂, e.map_smul, ha] }
  exact e'.toModuleIso

/-- The quotient-linear comparison between the two actual scalar extensions. -/
def quotientScalarExtensionIso (f : R →+* S) (I : Ideal R)
    (M : ModuleCat.{u} R) (hM : I ≤ Module.annihilator R M) :
    (ModuleCat.extendScalars (supportQuotientMap f I)).obj (quotientModule I M hM) ≅
    quotientModule (I.map f) ((ModuleCat.extendScalars f).obj M)
      (map_support_le_annihilator_extendScalars f I M hM) := by
  let X : ModuleCat.{u} (S ⧸ I.map f) :=
    (ModuleCat.extendScalars (supportQuotientMap f I)).obj (quotientModule I M hM)
  let Y : ModuleCat.{u} (S ⧸ I.map f) :=
    quotientModule (I.map f) ((ModuleCat.extendScalars f).obj M)
    (map_support_le_annihilator_extendScalars f I M hM)
  let e := (quotientScalarExtensionAmbientIso f I M hM).toLinearEquiv
  let a : X ≃+ Y := e.toAddEquiv
  let e' : X ≃ₗ[S ⧸ I.map f] Y :=
    { __ := a
      map_smul' := by
        intro s x
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective s
        exact e.map_smul r x }
  exact e'.toModuleIso

end Motivic.TorComparison
