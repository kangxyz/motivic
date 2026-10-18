/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Cycles.FinitePushforwardSemilocal

/-!
# A uniform whole-fiber bound from actual source-stalk bounds

A degreewise given QC family may have different vanishing bounds at each
original source point. The actual finite fiber gives one finite maximum.
The scalar-compatible whole-module zero criterion then proves a uniform bound
on the entire localized coefficient family. No finite generation or finite
length is inferred from this boundedness statement.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

universe u

namespace Motivic.FiniteSchemeEuler

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
  {U : Y.Opens} (hU : IsAffineOpen U) (p : Spec Γ(Y, U))

/-- The boundedness comparison retains the original coordinate section action. -/
local instance boundedCoordinateAlgebra : Algebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U) :=
  (f.app U).hom.toAlgebra

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The whole finite algebra proves finiteness of the entire original source fiber. -/
theorem originalSourceFiber_finite : Finite {x : X // f x = hU.fromSpec p} := by
  have := coordinateFinite f hU
  have : Finite (MaximalSpectrum (FiniteFiber.localAlgebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U) p)) :=
    Module.finiteAlgebra_maximalSpectrum_finite (Localization.AtPrime p.asIdeal) _
  exact (wholeAlgebraFiberEquiv f hU p).finite_iff.mp inferInstance

/-- The actual finite maximum of the possibly different bounds on original source stalks. -/
def originalFiberDegreeBound (b : {x : X // f x = hU.fromSpec p} → ℕ) : ℕ := by
  have := originalSourceFiber_finite f hU p
  letI : Fintype {x : X // f x = hU.fromSpec p} := Fintype.ofFinite _
  exact Finset.univ.sup b

/-- Every actual source bound is below the constructed whole-fiber bound. -/
theorem le_originalFiberDegreeBound (b : {x : X // f x = hU.fromSpec p} → ℕ)
    (x : {x : X // f x = hU.fromSpec p}) : b x ≤ originalFiberDegreeBound f hU p b := by
  have := originalSourceFiber_finite f hU p
  let : Fintype {x : X // f x = hU.fromSpec p} := Fintype.ofFinite _
  unfold originalFiberDegreeBound
  exact Finset.le_sup (Finset.mem_univ x)

variable (N : ℕ → X.Modules) [∀ n, (N n).IsQuasicoherent]

/-- A finite maximum of genuine pointwise bounds kills the whole localized family,
using all original source points and their actual structure-stalk modules. -/
theorem originalWholeFamily_zero_ge (b : {x : X // f x = hU.fromSpec p} → ℕ)
    (hN : ∀ x : {x : X // f x = hU.fromSpec p}, ∀ n, b x ≤ n →
      Subsingleton (originalSourceStalkModule (N n) x.1))
    (n : ℕ) (hn : originalFiberDegreeBound f hU p b ≤ n) :
    Subsingleton (originalWholeLocalizedModule f hU p (N n)) :=
  originalWholeModule_subsingleton f hU p (N n)
    (fun x => hN x n ((le_originalFiberDegreeBound f hU p b x).trans hn))

/-- Merely pointwise eventual source-stalk vanishing yields one whole localized bound.
No uniform source bound, equidimensionality or nonempty-fiber premise is assumed. -/
theorem originalWholeFamily_exists_bound
    (hN : ∀ x : {x : X // f x = hU.fromSpec p}, ∃ b : ℕ, ∀ n, b ≤ n →
      Subsingleton (originalSourceStalkModule (N n) x.1)) :
    ∃ b : ℕ, ∀ n, b ≤ n → Subsingleton (originalWholeLocalizedModule f hU p (N n)) := by
  classical
  choose b hb using hN
  exact ⟨originalFiberDegreeBound f hU p b,
    fun n hn => originalWholeFamily_zero_ge f hU p N b hb n hn⟩

/-- The degrees with nonzero whole coefficients form a finite set, derived from
actual source-stalk eventual vanishing without any length or rank assumption. -/
theorem originalWholeFamily_nonzero_finite
    (hN : ∀ x : {x : X // f x = hU.fromSpec p}, ∃ b : ℕ, ∀ n, b ≤ n →
      Subsingleton (originalSourceStalkModule (N n) x.1)) :
    {n : ℕ | ¬ Subsingleton (originalWholeLocalizedModule f hU p (N n))}.Finite := by
  obtain ⟨b, hb⟩ := originalWholeFamily_exists_bound f hU p N hN
  apply (Set.finite_Iio b).subset
  intro n hn
  exact Nat.lt_of_not_ge (fun h => hn (hb n h))

end Motivic.FiniteSchemeEuler
