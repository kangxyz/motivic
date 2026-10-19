/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Category.ModuleCat.Tor.ExteriorModuleFunctor
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The actual module structures on affine support coordinate rings

The exterior tensor of two quotient modules is identified with their tensor
product ring restricted along the tensor of the quotient maps. The proof checks
the action of every pure ambient tensor on every pure coefficient tensor.
Scalar extension of a quotient module is also identified with the corresponding
scalar-extension ring, restricted along its literal left inclusion. No flatness
of the quotient supports or of an ambient map is assumed.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open scoped TensorProduct ChangeOfRings

universe u

namespace ModuleCat.TorComparison.SupportModules

variable (k U V : Type u) [CommRing k] [CommRing U] [CommRing V]
  [Algebra k U] [Algebra k V] (I : Ideal U) (J : Ideal V)

/-- The literal coordinate map of the product of two quotient supports. -/
def quotientTensorMap : U ⊗[k] V →ₐ[k] (U ⧸ I) ⊗[k] (V ⧸ J) :=
  Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k I) (Ideal.Quotient.mkₐ k J)

/-- The quotient product map acts componentwise on pure tensors. -/
@[simp] theorem quotientTensorMap_tmul (a : U) (b : V) :
    quotientTensorMap k U V I J (a ⊗ₜ[k] b) =
      Ideal.Quotient.mk I a ⊗ₜ[k] Ideal.Quotient.mk J b := rfl

/-- The induced base action on a quotient module equals its quotient algebra action. -/
def quotientBaseEquiv :
    (ModuleCat.restrictScalars (algebraMap k U)).obj (ModuleCat.of U (U ⧸ I)) ≃ₗ[k]
      (U ⧸ I) where
  __ := AddEquiv.refl (U ⧸ I)
  map_smul' r x := by
    change (algebraMap k U r • (show U ⧸ I from x) : U ⧸ I) =
      r • (show U ⧸ I from x)
    exact IsScalarTower.algebraMap_smul U r (show U ⧸ I from x)

/-- The exterior quotient module has the actual tensor-quotient ring action.
The map on underlying pure tensors is the identity, but scalar compatibility
uses both quotient maps and the literal exterior representation. -/
def exteriorQuotientIso :
    ExteriorModule.obj k U V (ModuleCat.of U (U ⧸ I)) (ModuleCat.of V (V ⧸ J)) ≅
      (ModuleCat.restrictScalars (quotientTensorMap k U V I J).toRingHom).obj
        (ModuleCat.of ((U ⧸ I) ⊗[k] (V ⧸ J)) ((U ⧸ I) ⊗[k] (V ⧸ J))) := by
  let e : ExteriorModule.obj k U V (ModuleCat.of U (U ⧸ I)) (ModuleCat.of V (V ⧸ J)) ≃+
      (ModuleCat.restrictScalars (quotientTensorMap k U V I J).toRingHom).obj
        (ModuleCat.of ((U ⧸ I) ⊗[k] (V ⧸ J)) ((U ⧸ I) ⊗[k] (V ⧸ J))) :=
    (TensorProduct.congr (quotientBaseEquiv k U I) (quotientBaseEquiv k V J)).toAddEquiv
  refine LinearEquiv.toModuleIso
    (X₁ := ExteriorModule.obj k U V (ModuleCat.of U (U ⧸ I)) (ModuleCat.of V (V ⧸ J)))
    (X₂ := (ModuleCat.restrictScalars (quotientTensorMap k U V I J).toRingHom).obj
      (ModuleCat.of ((U ⧸ I) ⊗[k] (V ⧸ J)) ((U ⧸ I) ⊗[k] (V ⧸ J))))
    { e with map_smul' := ?_ }
  intro p x
  change e (p • x) = p • e x
  induction p using TensorProduct.inductionOn with
  | tmul a b =>
    induction x using TensorProduct.inductionOn with
    | tmul m n =>
      change (a • m) ⊗ₜ[k] (b • n) =
        (Ideal.Quotient.mk I a ⊗ₜ[k] Ideal.Quotient.mk J b) * (m ⊗ₜ[k] n)
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      simp only [Algebra.smul_def, Ideal.Quotient.algebraMap_eq]
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  | add p q hp hq => simp only [add_smul, map_add, hp, hq]

/-- The support comparison preserves pure quotient tensors literally. -/
theorem exteriorQuotientIso_hom_tmul (m : U ⧸ I) (n : V ⧸ J) :
    (exteriorQuotientIso k U V I J).hom
      (@TensorProduct.tmul k _ (U ⧸ I) (V ⧸ J) _ _
        (ExteriorModule.baseModule k U (ModuleCat.of U (U ⧸ I)))
        (ExteriorModule.baseModule k V (ModuleCat.of V (V ⧸ J))) m n) =
      m ⊗ₜ[k] n := rfl

section ScalarExtension

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (K : Ideal R)

/-- Extension of a quotient module is the literal scalar-extension coordinate
ring, viewed as an S-module by its actual left-inclusion ring map. -/
def extendQuotientIso :
    letI : Algebra R S := f.toAlgebra
    (ModuleCat.extendScalars f).obj (ModuleCat.of R (R ⧸ K)) ≅
      (ModuleCat.restrictScalars
        (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[R] (R ⧸ K))).obj
        (ModuleCat.of (S ⊗[R] (R ⧸ K)) (S ⊗[R] (R ⧸ K))) := by
  letI : Algebra R S := f.toAlgebra
  exact LinearEquiv.toModuleIso
    (X₁ := (ModuleCat.extendScalars f).obj (ModuleCat.of R (R ⧸ K)))
    (X₂ := (ModuleCat.restrictScalars
      (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[R] (R ⧸ K))).obj
      (ModuleCat.of (S ⊗[R] (R ⧸ K)) (S ⊗[R] (R ⧸ K))))
    { __ := AddEquiv.refl (S ⊗[R] (R ⧸ K))
      map_smul' := by
        intro s x
        simp only [AddEquiv.toFun_eq_coe, RingHom.id_apply]
        induction x using TensorProduct.inductionOn with
        | tmul t m =>
          change S at t
          change R ⧸ K at m
          change (s * t) ⊗ₜ[R] m = (s ⊗ₜ[R] (1 : R ⧸ K)) * (t ⊗ₜ[R] m)
          rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
        | add x y hx hy => simp only [smul_add, map_add, hx, hy] }

/-- Scalar-extension coordinates preserve the coefficient and quotient element. -/
@[simp] theorem extendQuotientIso_hom_tmul (s : S) (m : R ⧸ K) :
    letI : Algebra R S := f.toAlgebra
    (extendQuotientIso f K).hom (s ⊗ₜ[R,f] m) = s ⊗ₜ[R] m := rfl

end ScalarExtension

end ModuleCat.TorComparison.SupportModules
