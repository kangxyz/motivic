/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.Smooth.SmoothCartierAtPrime
import all Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.Smooth.SmoothCartierAtPrime
public import Lean.Util.CollectAxioms
public import Batteries.Tactic.Lint

/-! # Actual smooth Cartier choice without a supplied divisor -/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace MotivicTest.SmoothCartierChoice

/-- The affine input is only the original positive-rank prime, not a divisor. -/
theorem original_prime
    (k R : Type u) [Field k] [PerfectField k] [CommRing R]
    [Algebra k R] [Algebra.Smooth k R] (p : Ideal R) [p.IsPrime]
    (hpos : 0 < ringKrullDim (Localization.AtPrime p)) :
    ∃ r ∉ p, ∃ (Z : Scheme.{u}) (i : Z ⟶ Spec (.of (Localization.Away r))),
      IsClosedImmersion i ∧ IsLocallyRankOne _ (Scheme.Hom.idealModule i) ∧
      Smooth (i ≫ Spec.map (CommRingCat.ofHom (algebraMap k (Localization.Away r)))) ∧
      ∃ q : Spec (.of (Localization.Away r)),
        (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))) q =
          (⟨p, inferInstance⟩ : PrimeSpectrum R) ∧ q ∈ Set.range i :=
  Scheme.exists_smooth_cartier_at_prime k R p hpos

/-- An arbitrary original point, not merely a closed or rational point, is retained. -/
theorem original_point
    {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [Smooth p] (x : X)
    (hpos : 0 < ringKrullDim (X.presheaf.stalk x)) :
    ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧
      ∃ (Z : Scheme.{u}) (i : Z ⟶ U.toScheme),
        IsClosedImmersion i ∧ IsLocallyRankOne U.toScheme (Scheme.Hom.idealModule i) ∧
        Smooth (i ≫ U.ι ≫ p) ∧ x ∈ Set.range (i ≫ U.ι) :=
  Scheme.exists_smooth_cartier_neighborhood p x hpos

open Lean in
run_cmd do
  for name in #[``original_prime, ``original_point,
      ``Algebra.exists_prime_parameter_etale_line_chart,
      ``Scheme.Hom.etaleLineZeroFiber_isLocallyRankOne,
      ``Scheme.exists_smooth_cartier_at_prime,
      ``Scheme.exists_smooth_cartier_neighborhood] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo
    "Actual smooth Cartier choice at original positive-rank points: standard foundations only."

open Lean Batteries.Tactic.Lint in
run_cmd do
  let declarations := #[``original_prime, ``original_point,
    ``Scheme.exists_smooth_cartier_at_prime, ``Scheme.exists_smooth_cartier_neighborhood]
  let linters ← Lean.Elab.Command.liftCoreM (getChecks true none none)
  unless !linters.isEmpty do
    throwError "No declaration linters were selected."
  let results ← Lean.Elab.Command.liftCoreM <|
    Lean.withExporting (isExporting := false) (lintCore declarations linters)
  for (linter, findings) in results do
    for (name, message) in findings.toArray do
      throwError "{linter.name}: {name}: {message}"
  logInfo "Smooth Cartier choice: all selected declaration linters passed."

end MotivicTest.SmoothCartierChoice
