/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.Basis.Defs

/-! # Freeness on the actual tensor model of a localization

Intended upstream module: `Aglib.RingTheory.Localization.FreeTensor`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Flat.PolynomialGeneric`.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Module

/-- Freeness of the canonical localized module transports to the actual tensor
algebra over any model of the same ring localization. -/
theorem free_tensorProduct_of_free_localizedModule
    {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (S : Submonoid R) [IsLocalization S A]
    [Module.Free (Localization S) (LocalizedModule S B)] :
    Module.Free A (A ⊗[R] B) := by
  let e := IsLocalization.algEquiv S (Localization S) A
  let : Algebra (Localization S) (A ⊗[R] B) :=
    ((algebraMap A (A ⊗[R] B)).comp e.toRingHom).toAlgebra
  let : IsScalarTower R (Localization S) (A ⊗[R] B) :=
    IsScalarTower.of_algebraMap_eq (R := R) (S := Localization S) (A := A ⊗[R] B) fun r => by
      change algebraMap R (A ⊗[R] B) r =
        algebraMap A (A ⊗[R] B) (e (algebraMap R (Localization S) r))
      rw [e.commutes, IsScalarTower.algebraMap_apply R A (A ⊗[R] B)]
  let f := IsLocalizedModule.iso S (TensorProduct.mk R A B 1)
  let f' := f.extendScalarsOfIsLocalization S (Localization S)
  let : Module.Free (Localization S) (A ⊗[R] B) := Module.Free.of_equiv f'
  let b := Module.Free.chooseBasis (Localization S) (A ⊗[R] B)
  apply Module.Free.of_basis (b.mapCoeffs e.toRingEquiv _)
  intro c x
  simp only [Algebra.smul_def]
  rfl

end Module
