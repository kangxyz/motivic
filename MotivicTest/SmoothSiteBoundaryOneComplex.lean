module

public import Motivic.AlgebraicGeometry.SmoothSiteBoundaryOneComplex
public import Motivic.Cohomology.Motivic.Hypercohomology
public import Lean.Util.CollectAxioms

/-! # Direct audit of genuine all-degree boundary-one sheaf acyclicity -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic

universe u

example (k : Type u) [Field k] (n : ℕ) :
    IsZero ((SmoothSite.boundaryOneSheafComplex k).homology n) :=
  SmoothSite.isZero_homology_boundaryOneSheafComplex k n

open Lean in
run_cmd do
  for name in #[``AlgebraicSimplex.schemeBoundaryOneSimplicialIso,
      ``AlgebraicSimplex.isZero_homology_affineRelativeBoundaryOne,
      ``AlgebraicSimplex.affineSourceRelativeSimplexIso,
      ``AlgebraicSimplex.parameterRelativeSimplexIso,
      ``SmoothSite.integralAffineInclusion_isCoverDense,
      ``SmoothSite.isZero_sheafify_of_integral_affine,
      ``SmoothSite.isZero_sheafified_homology_of_integral_affine,
      ``SmoothSite.isZero_homology_boundaryOne_affine,
      ``SmoothSite.isZero_homology_largeBoundaryOne_affine,
      ``SmoothSite.isZero_homology_boundaryOneSheafComplex] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "All-degree genuine boundary-one sheaf acyclicity uses only standard Lean foundations."
