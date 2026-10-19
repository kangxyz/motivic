/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Restriction of scalars along surjective ring maps
-/

@[expose] public noncomputable section

open CategoryTheory

noncomputable section


universe u

namespace ModuleCat.SurjectiveScalarDescent

variable {R S : Type u} [CommRing R] [CommRing S]
  (f : R →+* S) (hf : Function.Surjective f) (M : ModuleCat.{u} R)
  (h : RingHom.ker f ≤ Module.annihilator R M)

/-- The actual scalar action factors uniquely through a surjective ring map. -/
def actionHom : S →+* AddMonoid.End M :=
  f.liftOfSurjective hf ⟨Module.toAddMonoidEnd R M, h⟩

/-- A scalar in the image acts by precisely its original ambient action. -/
@[simp] theorem actionHom_apply_image (r : R) (x : M) :
    actionHom f hf M h (f r) x = r • x := by
  change (f.liftOfRightInverse (Function.surjInv hf)
    (Function.rightInverse_surjInv hf) ⟨Module.toAddMonoidEnd R M, h⟩) (f r) x = _
  rw [RingHom.liftOfRightInverse_comp_apply]
  rfl

/-- The constructed quotient action on the same underlying additive group. -/
@[instance_reducible] def moduleAction : Module S M where
  smul := fun s x => actionHom f hf M h s x
  one_smul x := by change actionHom f hf M h 1 x = x; rw [map_one]; rfl
  mul_smul a b x := by
    change actionHom f hf M h (a * b) x = actionHom f hf M h a (actionHom f hf M h b x)
    rw [map_mul]
    rfl
  smul_zero a := (actionHom f hf M h a).map_zero
  smul_add a x y := (actionHom f hf M h a).map_add x y
  zero_smul x := by change actionHom f hf M h 0 x = 0; rw [map_zero]; rfl
  add_smul a b x := by
    change actionHom f hf M h (a + b) x = actionHom f hf M h a x + actionHom f hf M h b x
    rw [map_add]
    rfl

/-- The original module with its constructed quotient-ring action. -/
def descendedModule : ModuleCat.{u} S :=
  letI := moduleAction f hf M h
  ModuleCat.of S M

/-- Literal scalar restriction recovers the original module, by the identity on elements. -/
def restrictIso : M ≅ (ModuleCat.restrictScalars f).obj (descendedModule f hf M h) := by
  let N : ModuleCat.{u} R := (ModuleCat.restrictScalars f).obj (descendedModule f hf M h)
  let e : M ≃ₗ[R] N :=
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun r x => (actionHom_apply_image f hf M h r x).symm }
  exact e.toModuleIso

/-- The recovery isomorphism sends each original element to that same element. -/
@[simp] theorem restrictIso_hom_apply (x : M) :
    (restrictIso f hf M h).hom x = x := rfl

end ModuleCat.SurjectiveScalarDescent
