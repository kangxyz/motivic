import Motivic.KTheory.MilnorK.PolynomialDedekindResidue
import Lean.Util.CollectAxioms

/-! # Literal polynomial-to-Dedekind residue regression checks -/

open Motivic.KTheory.MilnorK Polynomial IsDedekindDomain
open Motivic.KTheory.MilnorK.PolynomialDedekindResidue

noncomputable section

variable {k : Type*} [Field k]

example (q : HeightOneSpectrum k[X]) : point (polynomial q) = q := point_polynomial q

example (p : PolynomialResidue.MonicIrreducible k) : polynomial (point p) = p :=
  polynomial_point p

example (p : PolynomialResidue.MonicIrreducible k) (n : ℕ)
    (x : K (RatFunc k) (n + 1)) :
    Motivic.KTheory.MilnorK.map n (Polynomial.LocalResidue.residueEquiv p.val).toRingHom
      (DedekindResidue.totalResidue k[X] (RatFunc k) n x (point p)) =
      PolynomialResidue.residueAt p.val n x := totalResidue_point p n x

open Lean in
run_cmd do
  let env ← getEnv
  for name in #[
      `Motivic.KTheory.MilnorK.PolynomialDedekindResidue.pointEquiv,
      `Motivic.KTheory.MilnorK.PolynomialDedekindResidue.fractionAlgebra_eq,
      `Motivic.KTheory.MilnorK.PolynomialDedekindResidue.totalResidue_point] do
    unless (env.checked.get.find? name).isSome do
      throwError "Declaration {name} is missing from the checked environment"
    for dependency in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Polynomial place equivalence and literal Dedekind residue bridge: standard axioms only."
