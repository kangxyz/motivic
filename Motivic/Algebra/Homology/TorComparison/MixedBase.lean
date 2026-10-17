/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.TorComparison.ExteriorModuleFunctor

/-!
# The mixed-base tensor comparison

Extension of the literal exterior module along a ring map from the tensor
product algebra is naturally the tensor product of the two scalar extensions.
All scalar maps are induced by that ring map. No flatness is used.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory TensorProduct
open scoped ChangeOfRings Motivic.TorComparison.ExteriorModule

universe u

namespace Motivic.TorComparison.MixedBase

variable (k U V Q : Type u) [CommRing k] [CommRing U] [CommRing V] [CommRing Q]
  [Algebra k U] [Algebra k V]

/-- The scalar map on the left factor, induced by the ambient map. -/
def leftMap (μ : U ⊗[k] V →+* Q) : U →+* Q :=
  μ.comp Algebra.TensorProduct.includeLeftRingHom

/-- The scalar map on the right factor, induced by the ambient map. -/
def rightMap (μ : U ⊗[k] V →+* Q) : V →+* Q :=
  μ.comp Algebra.TensorProduct.includeRight.toRingHom

variable {k U V Q}

/-- Both induced maps give the same base action; no algebra structure on `Q`
is an extra assumption. -/
theorem base_compatible (μ : U ⊗[k] V →+* Q) (r : k) :
    leftMap k U V Q μ (algebraMap k U r) =
      rightMap k U V Q μ (algebraMap k V r) := by
  change μ (algebraMap k (U ⊗[k] V) r) = μ (1 ⊗ₜ[k] algebraMap k V r)
  rw [Algebra.TensorProduct.algebraMap_apply']

/-- The ambient map on pure algebra tensors is the product of the two maps. -/
theorem map_tmul (μ : U ⊗[k] V →+* Q) (a : U) (b : V) :
    μ (a ⊗ₜ[k] b) = leftMap k U V Q μ a * rightMap k U V Q μ b := by
  change μ (a ⊗ₜ[k] b) = μ (a ⊗ₜ[k] 1) * μ (1 ⊗ₜ[k] b)
  rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

set_option backward.isDefEq.respectTransparency false in
/-- Balancing in an actual extension-of-scalars object, with its specified ring map. -/
theorem extension_tmul_smul {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (M : ModuleCat.{u} R) (s : S) (r : R) (m : M) :
    (s ⊗ₜ[R,f] (r • m) : (ModuleCat.extendScalars f).obj M) =
      (f r * s) ⊗ₜ[R,f] m := by
  rw [← TensorProduct.smul_tmul]
  rfl

variable (k U V Q) (μ : U ⊗[k] V →+* Q)

/-- The source is extension of the actual exterior module. -/
abbrev source (M : ModuleCat.{u} U) (N : ModuleCat.{u} V) : ModuleCat.{u} Q :=
  (ModuleCat.extendScalars μ).obj (ExteriorModule.obj k U V M N)

/-- The target uses precisely the two ring maps induced by `μ`. -/
abbrev target (M : ModuleCat.{u} U) (N : ModuleCat.{u} V) : ModuleCat.{u} Q :=
  ModuleCat.of Q (((ModuleCat.extendScalars (leftMap k U V Q μ)).obj M) ⊗[Q]
    ((ModuleCat.extendScalars (rightMap k U V Q μ)).obj N))

attribute [local instance] ExteriorModule.baseModule ExteriorModule.baseScalarTower

variable {k U V Q} (M : ModuleCat.{u} U) (N : ModuleCat.{u} V)

/-- The raw forward pure-tensor expression. -/
def forwardPure (q : Q) (m : M) (n : N) : target k U V Q μ M N :=
  (q ⊗ₜ[U,leftMap k U V Q μ] m) ⊗ₜ[Q]
    ((1 : Q) ⊗ₜ[V,rightMap k U V Q μ] n)

set_option backward.isDefEq.respectTransparency false in
/-- The forward expression is balanced over the base ring. -/
theorem forwardPure_balanced (q : Q) (r : k) (m : M) (n : N) :
    forwardPure μ M N q (r • m) n = forwardPure μ M N q m (r • n) := by
  unfold forwardPure
  rw [← IsScalarTower.algebraMap_smul U r m, ← IsScalarTower.algebraMap_smul V r n,
    extension_tmul_smul, extension_tmul_smul, mul_one]
  rw [← ModuleCat.ExtendScalars.smul_tmul, TensorProduct.smul_tmul,
    base_compatible μ, ModuleCat.ExtendScalars.smul_tmul, mul_one]

set_option backward.isDefEq.respectTransparency false in
/-- Moving a scalar from the left input into the common coefficient. -/
theorem forwardPure_smul_left (q : Q) (a : U) (m : M) (n : N) :
    forwardPure μ M N q (a • m) n =
      forwardPure μ M N (leftMap k U V Q μ a * q) m n := by
  unfold forwardPure
  rw [extension_tmul_smul]

set_option backward.isDefEq.respectTransparency false in
/-- Moving a scalar from the right input into the common coefficient. -/
theorem forwardPure_smul_right (q : Q) (b : V) (m : M) (n : N) :
    forwardPure μ M N q m (b • n) =
      forwardPure μ M N (rightMap k U V Q μ b * q) m n := by
  unfold forwardPure
  rw [extension_tmul_smul, ← ModuleCat.ExtendScalars.smul_tmul,
    ← TensorProduct.smul_tmul, ModuleCat.ExtendScalars.smul_tmul]

/-- The forward map on the exterior tensor, before imposing ambient balancing. -/
def forwardInner (q : Q) : (M ⊗[k] N) →+ target k U V Q μ M N :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun m ↦ AddMonoidHom.mk' (forwardPure μ M N q m)
      (by intro n n'; simp [forwardPure, tmul_add]))
      (by intro m m'; ext n; simp [forwardPure, tmul_add, add_tmul]))
    (forwardPure_balanced μ M N q)

/-- Evaluation before ambient balancing. -/
@[simp] theorem forwardInner_tmul (q : Q) (m : M) (n : N) :
    forwardInner μ M N q (m ⊗ₜ[k] n) = forwardPure μ M N q m n := rfl

/-- The additive coefficient-dependent forward map. -/
def forwardBilinear : Q →+ ((M ⊗[k] N) →+ target k U V Q μ M N) :=
  AddMonoidHom.mk' (forwardInner μ M N) (by
    intro q q'
    ext x
    induction x with
    | tmul m n =>
      change forwardPure μ M N (q + q') m n =
        forwardPure μ M N q m n + forwardPure μ M N q' m n
      simp only [forwardPure, add_tmul]
    | add x y hx hy => simp only [map_add, AddMonoidHom.add_apply] at *; rw [hx, hy])

set_option backward.isDefEq.respectTransparency false in
/-- Balancing for the full exterior algebra. -/
theorem forwardBilinear_balanced (p : U ⊗[k] V) (q : Q) (x : M ⊗[k] N) :
    forwardBilinear μ M N (μ p * q) x = forwardBilinear μ M N q (p • x) := by
  change forwardInner μ M N (μ p * q) x = forwardInner μ M N q (p • x)
  induction p with
  | tmul a b =>
    induction x with
    | tmul m n =>
      change forwardPure μ M N (μ (a ⊗ₜ[k] b) * q) m n =
        forwardPure μ M N q (a • m) (b • n)
      rw [forwardPure_smul_left, forwardPure_smul_right, map_tmul,
        mul_assoc, mul_left_comm]
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  | add p p' hp hp' =>
    change forwardBilinear μ M N (μ (p + p') * q) x = _
    rw [map_add, add_mul, map_add, AddMonoidHom.add_apply]
    rw [add_smul, map_add]
    exact congrArg₂ (· + ·) hp hp'

/-- The genuine forward comparison, linear over the destination ring. -/
def forward : source k U V Q μ M N →ₗ[Q] target k U V Q μ M N := by
  letI : Module (U ⊗[k] V) Q := Module.compHom Q μ
  let f : source k U V Q μ M N →+ target k U V Q μ M N :=
    TensorProduct.liftAddHom (forwardBilinear μ M N) (forwardBilinear_balanced μ M N)
  refine { f with map_smul' := ?_ }
  intro q x
  change f (q • x) = q • f x
  induction x using TensorProduct.inductionOn with
  | tmul q' x =>
    change Q at q'
    change M ⊗[k] N at x
    change forwardInner μ M N (q * q') x = q • forwardInner μ M N q' x
    induction x with
    | tmul m n => rfl
    | add x y hx hy => simp only [map_add, hx, hy, smul_add]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

/-- The forward comparison has the required literal pure-tensor formula. -/
@[simp] theorem forward_tmul (q : Q) (m : M) (n : N) :
    forward μ M N (q ⊗ₜ[U ⊗[k] V,μ] (m ⊗ₜ[k] n)) =
      ((q ⊗ₜ[U,leftMap k U V Q μ] m) ⊗ₜ[Q]
        ((1 : Q) ⊗ₜ[V,rightMap k U V Q μ] n) : target k U V Q μ M N) := rfl

/-- The universal scalar-extension map, in a form with its pure-tensor formula. -/
def extensionLift {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (A : ModuleCat.{u} R) (B : ModuleCat.{u} S)
    (g : A →+ B) (h : ∀ r a, g (r • a) = f r • g a) :
    (ModuleCat.extendScalars f).obj A →ₗ[S] B :=
  ((ModuleCat.ExtendRestrictScalarsAdj.homEquiv f).symm
    (ModuleCat.ofHom (Y := (ModuleCat.restrictScalars f).obj B)
      { toFun := g, map_add' := g.map_add, map_smul' := h })).hom

/-- Scalar-extension maps evaluate by scalar multiplication. -/
@[simp] theorem extensionLift_tmul {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (A : ModuleCat.{u} R) (B : ModuleCat.{u} S)
    (g : A →+ B) (h : ∀ r a, g (r • a) = f r • g a) (s : S) (a : A) :
    extensionLift f A B g h (s ⊗ₜ[R,f] a) = s • g a := rfl

/-- The seed for the inverse in the right module variable. -/
def inverseRightSeed (m : M) : N →+ source k U V Q μ M N :=
  AddMonoidHom.mk' (fun n ↦ (1 : Q) ⊗ₜ[U ⊗[k] V,μ] (m ⊗ₜ[k] n))
    (by intro n n'; simp only [tmul_add])

/-- Right scalar balancing for the inverse seed. -/
theorem inverseRightSeed_smul (m : M) (b : V) (n : N) :
    inverseRightSeed μ M N m (b • n) =
      rightMap k U V Q μ b • inverseRightSeed μ M N m n := by
  have h : ((1 : U) ⊗ₜ[k] b) • (m ⊗ₜ[k] n) = m ⊗ₜ[k] (b • n) := by
    rw [ExteriorModule.smul_tmul, one_smul]
  change ((1 : Q) ⊗ₜ[U ⊗[k] V,μ] (m ⊗ₜ[k] (b • n)) : source k U V Q μ M N) =
    μ (1 ⊗ₜ[k] b) • ((1 : Q) ⊗ₜ[U ⊗[k] V,μ] (m ⊗ₜ[k] n))
  rw [← h]
  exact extension_tmul_smul μ (ExteriorModule.obj k U V M N) 1 (1 ⊗ₜ[k] b) (m ⊗ₜ[k] n)

/-- The inverse after extending its right input. -/
def inverseRight (m : M) :
    (ModuleCat.extendScalars (rightMap k U V Q μ)).obj N →ₗ[Q] source k U V Q μ M N :=
  extensionLift (rightMap k U V Q μ) N (source k U V Q μ M N)
    (inverseRightSeed μ M N m) (inverseRightSeed_smul μ M N m)

/-- The right-extended inverse on pure tensors. -/
@[simp] theorem inverseRight_tmul (m : M) (q : Q) (n : N) :
    inverseRight μ M N m (q ⊗ₜ[V,rightMap k U V Q μ] n) =
      q ⊗ₜ[U ⊗[k] V,μ] (m ⊗ₜ[k] n) := by
  change (q * 1) ⊗ₜ[U ⊗[k] V,μ] (m ⊗ₜ[k] n) = _
  rw [mul_one]

/-- The module of right-extended linear maps, used to extend the left variable. -/
abbrev inverseHom : ModuleCat.{u} Q :=
  ModuleCat.of Q ((ModuleCat.extendScalars (rightMap k U V Q μ)).obj N →ₗ[Q]
    source k U V Q μ M N)

/-- Additivity of the right-extended inverse in its left input. -/
def inverseLeftSeed : M →+ inverseHom μ M N :=
  AddMonoidHom.mk' (inverseRight μ M N) (by
    let : Algebra (U ⊗[k] V) Q := μ.toAlgebra
    intro m m'
    apply LinearMap.ext
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul q n =>
      change Q at q
      change N at n
      change inverseRight μ M N (m + m') (q ⊗ₜ[V,rightMap k U V Q μ] n) =
        inverseRight μ M N m (q ⊗ₜ[V,rightMap k U V Q μ] n) +
        inverseRight μ M N m' (q ⊗ₜ[V,rightMap k U V Q μ] n)
      rw [inverseRight_tmul, inverseRight_tmul, inverseRight_tmul, add_tmul, tmul_add]
    | add x y hx hy =>
      simp only [LinearMap.add_apply, map_add] at *
      rw [hx, hy])

/-- Left scalar balancing after the right extension. -/
theorem inverseLeftSeed_smul (a : U) (m : M) :
    inverseLeftSeed μ M N (a • m) = leftMap k U V Q μ a • inverseLeftSeed μ M N m := by
  let : Algebra (U ⊗[k] V) Q := μ.toAlgebra
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul q n =>
    change Q at q
    change N at n
    change inverseRight μ M N (a • m) (q ⊗ₜ[V,rightMap k U V Q μ] n) =
      leftMap k U V Q μ a • inverseRight μ M N m (q ⊗ₜ[V,rightMap k U V Q μ] n)
    rw [inverseRight_tmul, inverseRight_tmul]
    have h : (a ⊗ₜ[k] (1 : V)) • (m ⊗ₜ[k] n) = (a • m) ⊗ₜ[k] n := by
      rw [ExteriorModule.smul_tmul, one_smul]
    rw [← h]
    exact extension_tmul_smul μ (ExteriorModule.obj k U V M N) q (a ⊗ₜ[k] 1) (m ⊗ₜ[k] n)
  | add x y hx hy =>
    change inverseRight μ M N (a • m) (x + y) =
      leftMap k U V Q μ a • inverseRight μ M N m (x + y)
    rw [map_add, map_add, smul_add]
    exact congrArg₂ (· + ·) hx hy

/-- The fully extended bilinear inverse. -/
def inverseBilinear :
    (ModuleCat.extendScalars (leftMap k U V Q μ)).obj M →ₗ[Q] inverseHom μ M N :=
  extensionLift (leftMap k U V Q μ) M (inverseHom μ M N)
    (inverseLeftSeed μ M N) (inverseLeftSeed_smul μ M N)

/-- The genuine inverse, linear over the destination ring. -/
def inverse : target k U V Q μ M N →ₗ[Q] source k U V Q μ M N :=
  TensorProduct.lift (inverseBilinear μ M N)

/-- The inverse multiplies the two common coefficients. -/
@[simp] theorem inverse_tmul (q q' : Q) (m : M) (n : N) :
    inverse μ M N ((q ⊗ₜ[U,leftMap k U V Q μ] m) ⊗ₜ[Q]
      (q' ⊗ₜ[V,rightMap k U V Q μ] n)) =
      (q * q') ⊗ₜ[U ⊗[k] V,μ] (m ⊗ₜ[k] n) := by
  change q • inverseRight μ M N m (q' ⊗ₜ[V,rightMap k U V Q μ] n) = _
  rw [inverseRight_tmul]
  rfl

/-- Maps out of the extended exterior tensor are determined by triple pure tensors. -/
@[ext] theorem source_ext {T : ModuleCat.{u} Q}
    {f g : source k U V Q μ M N →ₗ[Q] T}
    (h : ∀ (q : Q) (m : M) (n : N),
      f (q ⊗ₜ[U ⊗[k] V,μ] (m ⊗ₜ[k] n)) =
      g (q ⊗ₜ[U ⊗[k] V,μ] (m ⊗ₜ[k] n))) : f = g := by
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul q x =>
    change Q at q
    change M ⊗[k] N at x
    induction x with
    | tmul m n => exact h q m n
    | add x y hx hy => simpa only [tmul_add, map_add] using congrArg₂ (· + ·) hx hy
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Maps out of the tensor of extensions are determined by four pure factors. -/
@[ext] theorem target_ext {T : ModuleCat.{u} Q}
    {f g : target k U V Q μ M N →ₗ[Q] T}
    (h : ∀ (q q' : Q) (m : M) (n : N),
      f ((q ⊗ₜ[U,leftMap k U V Q μ] m) ⊗ₜ[Q]
        (q' ⊗ₜ[V,rightMap k U V Q μ] n)) =
      g ((q ⊗ₜ[U,leftMap k U V Q μ] m) ⊗ₜ[Q]
        (q' ⊗ₜ[V,rightMap k U V Q μ] n))) : f = g := by
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul x y =>
    induction x using TensorProduct.inductionOn with
    | tmul q m =>
      change Q at q
      change M at m
      induction y using TensorProduct.inductionOn with
      | tmul q' n => exact h q q' m n
      | add y y' hy hy' => simpa only [tmul_add, map_add] using congrArg₂ (· + ·) hy hy'
    | add x x' hx hx' => simpa only [add_tmul, map_add] using congrArg₂ (· + ·) hx hx'
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The backward map is a left inverse to the forward map. -/
theorem inverse_comp_forward : (inverse μ M N).comp (forward μ M N) = LinearMap.id := by
  apply source_ext μ M N
  intro q m n
  change inverse μ M N ((q ⊗ₜ[U,leftMap k U V Q μ] m) ⊗ₜ[Q]
    ((1 : Q) ⊗ₜ[V,rightMap k U V Q μ] n)) = _
  simpa only [mul_one, LinearMap.id_apply] using inverse_tmul μ M N q 1 m n

/-- The backward map is a right inverse to the forward map. -/
theorem forward_comp_inverse : (forward μ M N).comp (inverse μ M N) = LinearMap.id := by
  apply target_ext μ M N
  intro q q' m n
  simp only [LinearMap.comp_apply, LinearMap.id_apply]
  rw [inverse_tmul μ M N q q' m n, forward_tmul μ M N (q * q') m n]
  rw [mul_comm q q', ← ModuleCat.ExtendScalars.smul_tmul
    (f := leftMap k U V Q μ) (M := M) q' q m]
  rw [TensorProduct.smul_tmul q'
    (q ⊗ₜ[U,leftMap k U V Q μ] m : (ModuleCat.extendScalars (leftMap k U V Q μ)).obj M)
    ((1 : Q) ⊗ₜ[V,rightMap k U V Q μ] n :
      (ModuleCat.extendScalars (rightMap k U V Q μ)).obj N)]
  rw [ModuleCat.ExtendScalars.smul_tmul (f := rightMap k U V Q μ) (M := N), mul_one]

/-- The actual mixed-base tensor equivalence; it requires no flatness hypothesis. -/
def equiv : source k U V Q μ M N ≃ₗ[Q] target k U V Q μ M N :=
  LinearEquiv.ofLinearMap (forward μ M N) (inverse μ M N)
    (forward_comp_inverse μ M N) (inverse_comp_forward μ M N)

/-- The equivalence evaluates by putting the common coefficient in the left factor. -/
@[simp] theorem equiv_tmul (q : Q) (m : M) (n : N) :
    equiv μ M N (q ⊗ₜ[U ⊗[k] V,μ] (m ⊗ₜ[k] n)) =
      forwardPure μ M N q m n := rfl

/-- The inverse equivalence multiplies the two common coefficients. -/
@[simp] theorem equiv_symm_tmul (q q' : Q) (m : M) (n : N) :
    (equiv μ M N).symm ((q ⊗ₜ[U,leftMap k U V Q μ] m) ⊗ₜ[Q]
      (q' ⊗ₜ[V,rightMap k U V Q μ] n)) =
      (q * q') ⊗ₜ[U ⊗[k] V,μ] (m ⊗ₜ[k] n) := inverse_tmul μ M N q q' m n

/-- The comparison in the actual module category over `Q`. -/
def iso : source k U V Q μ M N ≅ target k U V Q μ M N :=
  (equiv μ M N).toModuleIso

end Motivic.TorComparison.MixedBase
