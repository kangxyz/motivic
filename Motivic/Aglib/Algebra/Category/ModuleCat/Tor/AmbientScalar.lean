/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Category.ModuleCat.Tor.FlatBaseChange

/-!
# Scalar adapters for the ambient Tor comparison

For an arbitrary commutative-ring map, tensoring by the restricted target
ring agrees with extension of scalars followed by restriction. The comparison
is the literal identity on the underlying tensor product, with its scalar
compatibility proved. It gives an actual chain isomorphism. Exact restriction
then commutes with homology, without any flatness hypothesis on the ring map.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory HomologicalComplex
open scoped TensorProduct

universe u

namespace ModuleCat.TorComparison

variable {R S : Type u} [CommRing R] [CommRing S]

/-- Tensoring by the target ring, restricted along its actual scalar map,
is naturally the restriction of scalar extension. -/
def ambientTensorRestrictExtendIso (f : R →+* S) :
    tensorLeft ((ModuleCat.restrictScalars f).obj (ModuleCat.of S S)) ≅
      ModuleCat.extendScalars f ⋙ ModuleCat.restrictScalars f :=
  NatIso.ofComponents (fun M ↦
    (AddEquiv.toLinearEquiv
      (M := ↑((ModuleCat.restrictScalars f).obj (ModuleCat.of S S) ⊗ M))
      (M₂ := ↑((ModuleCat.restrictScalars f).obj ((ModuleCat.extendScalars f).obj M)))
      (by rfl)
      (fun r x ↦ by
        induction x using TensorProduct.inductionOn with
        | tmul s m => rfl
        | add x y _ _ =>
          change (r • (x + y) :
            (ModuleCat.restrictScalars f).obj (ModuleCat.of S S) ⊗ M) =
              (r • (x + y) :
                (ModuleCat.restrictScalars f).obj ((ModuleCat.extendScalars f).obj M))
          simp only [smul_add])).toModuleIso)
    (by
      intro M N g
      apply ModuleCat.hom_ext
      apply TensorProduct.ext'
      intro s m
      rfl)

/-- The actual coefficient-tensor complex is isomorphic to scalar extension
followed by scalar restriction, for every complex and every ring map. -/
def ambientTensorRestrictExtendComplexIso (f : R →+* S)
    (K : ChainComplex (ModuleCat.{u} R) ℕ) :
    ((tensorLeft ((ModuleCat.restrictScalars f).obj (ModuleCat.of S S))).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj K ≅
      ((ModuleCat.restrictScalars f).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (((ModuleCat.extendScalars f).mapHomologicalComplex (ComplexShape.down ℕ)).obj K) :=
  (NatIso.mapHomologicalComplex (ambientTensorRestrictExtendIso f) _).app K

/-- Restriction of scalars is exact for arbitrary ring maps and identifies
homology with the actual restricted scalar action. -/
def ambientRestrictHomologyIso (f : R →+* S)
    (K : ChainComplex (ModuleCat.{u} S) ℕ) (n : ℕ) :
    (((ModuleCat.restrictScalars f).mapHomologicalComplex (ComplexShape.down ℕ)).obj K).homology n ≅
      (ModuleCat.restrictScalars f).obj (K.homology n) :=
  (K.sc n).mapHomologyIso (ModuleCat.restrictScalars f)

end ModuleCat.TorComparison
