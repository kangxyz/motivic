/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.LaurentTorus
public import Mathlib.Algebra.Ring.PUnit
public import Mathlib.Data.ZMod.Basic
public import Lean.Util.CollectAxioms

/-! # Actual Laurent projection and identity-section consumers -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent

universe u

namespace MotivicTest.LaurentTorus

variable (R : CommRingCat.{u})

example : Smooth (laurentProjection R) := inferInstance

example : IsSeparated (laurentProjection R) := inferInstance

example : LocallyOfFiniteType (laurentProjection R) ∧ QuasiCompact (laurentProjection R) :=
  laurentProjection_finiteType R

example : laurentOneSection R = Spec.map (CommRingCat.ofHom
    (LaurentPolynomial.eval₂ (RingHom.id R) 1)) := rfl

example : laurentOneSection R ≫ laurentProjection R = 𝟙 (Spec R) := by simp

example (r : R) : laurentEvalOne R (LaurentPolynomial.C r) = r := by simp

example (n : ℤ) : laurentEvalOne R (LaurentPolynomial.T n) = 1 := by simp

example : (laurentOneSection R).appTop
    (laurentGlobalUnit R : Γ(Spec (.of (LaurentPolynomial R)), ⊤)) = 1 := by simp

example : IsClosedImmersion (laurentOneSection R) := inferInstance

/- The zero ring is allowed, so the construction does not assume nonempty spectra. -/
example : Smooth (laurentProjection (.of PUnit)) := inferInstance

example : laurentOneSection (.of PUnit) ≫ laurentProjection (.of PUnit) =
    𝟙 (Spec (.of PUnit)) := laurentOneSection_projection _

/- A genuinely nonreduced coefficient ring is allowed. -/
example : (2 : ZMod 4) ≠ 0 ∧ (2 : ZMod 4) ^ 2 = 0 := by decide

example : Smooth (laurentProjection (.of (ZMod 4))) := inferInstance

example : IsClosedImmersion (laurentOneSection (.of (ZMod 4))) := inferInstance

open Lean in
run_cmd do
  for name in #[``instSmoothLaurentProjection, ``instIsSeparatedLaurentProjection,
      ``instQuasiCompactLaurentProjection, ``laurentOneSection,
      ``laurentOneSection_projection, ``laurentOneSection_appTop_coordinate,
      ``instIsClosedImmersionLaurentOneSection] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"

end MotivicTest.LaurentTorus
