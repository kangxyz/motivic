/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Category.ModuleCat.Tor.SupportModules

/-!
# Support modules with a prescribed algebra structure

Scalar extension along an algebra map agrees with the module of the literal
base-changed quotient ring, with its existing algebra structure retained.
This avoids replacing a geometric coordinate ring by a definitionally different
choice of induced algebra instance.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open scoped TensorProduct ChangeOfRings

universe u

namespace ModuleCat.TorComparison.SupportModules

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

/-- Restriction of the regular target module agrees with its given algebra action. -/
def regularBaseEquiv :
    (ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S) ≃ₗ[R] S where
  __ := AddEquiv.refl S
  map_smul' r s := by
    change algebraMap R S r * (show S from s) = r • (show S from s)
    exact (Algebra.smul_def r (show S from s)).symm

/-- Scalar extension of a quotient module is the actual base-changed quotient
ring for the specified algebra, with the action of the literal left inclusion. -/
def extendQuotientAlgebraIso (I : Ideal R) :
    (ModuleCat.extendScalars (algebraMap R S)).obj (ModuleCat.of R (R ⧸ I)) ≅
      (ModuleCat.restrictScalars
        (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[R] (R ⧸ I))).obj
        (ModuleCat.of (S ⊗[R] (R ⧸ I)) (S ⊗[R] (R ⧸ I))) := by
  let e : (ModuleCat.extendScalars (algebraMap R S)).obj (ModuleCat.of R (R ⧸ I)) ≃+
      (ModuleCat.restrictScalars
        (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[R] (R ⧸ I))).obj
        (ModuleCat.of (S ⊗[R] (R ⧸ I)) (S ⊗[R] (R ⧸ I))) :=
    (TensorProduct.congr (regularBaseEquiv R S) (LinearEquiv.refl R (R ⧸ I))).toAddEquiv
  refine LinearEquiv.toModuleIso
    (X₁ := (ModuleCat.extendScalars (algebraMap R S)).obj (ModuleCat.of R (R ⧸ I)))
    (X₂ := (ModuleCat.restrictScalars
      (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[R] (R ⧸ I))).obj
      (ModuleCat.of (S ⊗[R] (R ⧸ I)) (S ⊗[R] (R ⧸ I))))
    { e with map_smul' := ?_ }
  intro s x
  change e (s • x) = s • e x
  induction x using TensorProduct.inductionOn with
  | tmul t m =>
    change S at t
    change R ⧸ I at m
    change (s * t) ⊗ₜ[R] m = (s ⊗ₜ[R] (1 : R ⧸ I)) * (t ⊗ₜ[R] m)
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

/-- The comparison keeps the literal scalar-extension coordinates. -/
@[simp] theorem extendQuotientAlgebraIso_hom_tmul (I : Ideal R) (s : S) (m : R ⧸ I) :
    (extendQuotientAlgebraIso R S I).hom (s ⊗ₜ[R,algebraMap R S] m) = s ⊗ₜ[R] m := rfl

end ModuleCat.TorComparison.SupportModules
