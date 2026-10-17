/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Exterior modules over the tensor product algebra

The action on `M ⊗[k] N` constructed here is the actual exterior action of
`U ⊗[k] V`, with both factors acting. Tensor products of split free presentations
prove projectivity over this tensor product algebra. This is distinct from the
left-factor projectivity instance in `Module.Projective.tensorProduct`.

The exterior module instance is scoped to avoid changing existing tensor actions.
-/

@[expose] public section

noncomputable section

open TensorProduct

universe u

namespace Motivic.TorComparison.ExteriorModule

variable (k U V M N : Type u) [CommRing k] [CommRing U] [CommRing V]
  [Algebra k U] [Algebra k V]
  [AddCommGroup M] [Module k M] [Module U M] [IsScalarTower k U M]
  [AddCommGroup N] [Module k N] [Module V N] [IsScalarTower k V N]

/-- The exterior representation, including both algebra factors. -/
def action : U ⊗[k] V →ₐ[k] Module.End k (M ⊗[k] N) :=
  (Module.endTensorEndAlgHom (R := k) (S := k) (A := k) (M := M) (N := N)).comp
    (Algebra.TensorProduct.map (Algebra.lsmul k k M : U →ₐ[k] Module.End k M)
      (Algebra.lsmul k k N : V →ₐ[k] Module.End k N))

/-- The literal exterior action of the tensor product algebra. -/
scoped instance module : Module (U ⊗[k] V) (M ⊗[k] N) :=
  Module.compHom _ (action k U V M N).toRingHom

/-- Scalar compatibility with the original base-ring tensor module. -/
scoped instance scalarTower : IsScalarTower k (U ⊗[k] V) (M ⊗[k] N) :=
  IsScalarTower.of_algebraMap_smul fun r x ↦ by
    change action k U V M N (algebraMap k (U ⊗[k] V) r) x = r • x
    rw [(action k U V M N).commutes]
    rfl

variable {k U V M N}

/-- Pure algebra tensors act separately on the two module factors. -/
@[simp] theorem smul_tmul (a : U) (b : V) (m : M) (n : N) :
    (a ⊗ₜ[k] b) • (m ⊗ₜ[k] n) = (a • m) ⊗ₜ[k] (b • n) := rfl

/-- Exterior-linear maps are determined on pure tensors. -/
@[ext] theorem ext {T : Type u} [AddCommGroup T] [Module (U ⊗[k] V) T]
    {f g : (M ⊗[k] N) →ₗ[U ⊗[k] V] T}
    (h : ∀ m n, f (m ⊗ₜ[k] n) = g (m ⊗ₜ[k] n)) : f = g := by
  apply LinearMap.ext
  intro x
  induction x with
  | tmul m n => exact h m n
  | add x y hx hy => simp only [map_add, hx, hy]

variable {M' N' M'' N'' : Type u}
  [AddCommGroup M'] [Module k M'] [Module U M'] [IsScalarTower k U M']
  [AddCommGroup N'] [Module k N'] [Module V N'] [IsScalarTower k V N']
  [AddCommGroup M''] [Module k M''] [Module U M''] [IsScalarTower k U M'']
  [AddCommGroup N''] [Module k N''] [Module V N''] [IsScalarTower k V N'']

/-- Tensoring maps is linear over the full exterior algebra. -/
def map (f : M →ₗ[U] M') (g : N →ₗ[V] N') :
    (M ⊗[k] N) →ₗ[U ⊗[k] V] (M' ⊗[k] N') where
  __ := (TensorProduct.map (f.restrictScalars k) (g.restrictScalars k)).toAddMonoidHom
  map_smul' p x := by
    change TensorProduct.map (f.restrictScalars k) (g.restrictScalars k) (p • x) =
      p • TensorProduct.map (f.restrictScalars k) (g.restrictScalars k) x
    induction p with
    | tmul a b =>
      induction x with
      | tmul m n => simp only [smul_tmul, TensorProduct.map_tmul,
          LinearMap.restrictScalars_apply, map_smul]
      | add x y hx hy => simp only [smul_add, map_add, hx, hy]
    | add p q hp hq => simp only [add_smul, map_add, hp, hq]

/-- The map on pure tensors is the tensor of the two given maps. -/
@[simp] theorem map_tmul (f : M →ₗ[U] M') (g : N →ₗ[V] N') (m : M) (n : N) :
    map (k := k) f g (m ⊗ₜ[k] n) = f m ⊗ₜ[k] g n := rfl

/-- Exterior tensor maps preserve identities. -/
@[simp] theorem map_id :
    map (k := k) (LinearMap.id : M →ₗ[U] M) (LinearMap.id : N →ₗ[V] N) =
      LinearMap.id := by
  ext m n
  rfl

/-- Exterior tensor maps preserve composition in both variables. -/
theorem map_comp (f : M →ₗ[U] M') (f' : M' →ₗ[U] M'')
    (g : N →ₗ[V] N') (g' : N' →ₗ[V] N'') :
    map (k := k) (f'.comp f) (g'.comp g) =
      (map (k := k) f' g').comp (map (k := k) f g) := by
  ext m n
  rfl

variable (k U V)

/-- The tensor of free modules is free over the actual exterior algebra. -/
def freeTensorEquiv (ι κ : Type u) :
    ((ι →₀ U) ⊗[k] (κ →₀ V)) ≃ₗ[U ⊗[k] V] ((ι × κ) →₀ U ⊗[k] V) where
  __ := (finsuppTensorFinsupp k k U V ι κ).toAddEquiv
  map_smul' p x := by
    change finsuppTensorFinsupp k k U V ι κ (p • x) =
      p • finsuppTensorFinsupp k k U V ι κ x
    induction p with
    | tmul a b =>
      induction x with
      | tmul f g =>
        apply Finsupp.ext
        rintro ⟨i, j⟩
        simp only [smul_tmul, finsuppTensorFinsupp_apply, Finsupp.smul_apply,
          smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul]
      | add x y hx hy => simp only [smul_add, map_add, hx, hy]
    | add p q hp hq => simp only [add_smul, map_add, hp, hq]

/-- The free-module equivalence has the expected coefficient formula. -/
@[simp] theorem freeTensorEquiv_tmul_apply {ι κ : Type u}
    (f : ι →₀ U) (g : κ →₀ V) (i : ι) (j : κ) :
    freeTensorEquiv k U V ι κ (f ⊗ₜ[k] g) (i, j) = f i ⊗ₜ[k] g j :=
  finsuppTensorFinsupp_apply k k U V ι κ f g i j

/-- Projectivity of the exterior tensor of two free presentations. -/
theorem projective_free (ι κ : Type u) :
    Module.Projective (U ⊗[k] V) ((ι →₀ U) ⊗[k] (κ →₀ V)) :=
  Module.Projective.of_equiv (freeTensorEquiv k U V ι κ).symm

variable (M N)

/-- The exterior tensor of projective modules is projective over `U ⊗[k] V`.
No flatness or projectivity over the base ring is assumed. -/
theorem projective [hM : Module.Projective U M] [hN : Module.Projective V N] :
    Module.Projective (U ⊗[k] V) (M ⊗[k] N) := by
  obtain ⟨sM, hsM⟩ := hM
  obtain ⟨sN, hsN⟩ := hN
  let := projective_free k U V M N
  apply Module.Projective.of_split (map (k := k) sM sN)
    (map (k := k) (Finsupp.linearCombination U id) (Finsupp.linearCombination V id))
  ext m n
  simp only [LinearMap.comp_apply, map_tmul, LinearMap.id_apply]
  rw [hsM m, hsN n]

/-- The same projectivity statement in the actual category of exterior modules. -/
theorem categorical_projective [Module.Projective U M] [Module.Projective V N] :
    CategoryTheory.Projective (ModuleCat.of (U ⊗[k] V) (M ⊗[k] N)) := by
  let := projective k U V M N
  infer_instance

end Motivic.TorComparison.ExteriorModule
