module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Units.BoundaryOneComplex
public import Motivic.Cohomology.SuslinVoevodsky.Hypercohomology
public import Lean.Util.CollectAxioms

/-! # Direct audit of genuine all-degree boundary-one sheaf acyclicity -/

@[expose] public noncomputable section

open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic

universe u

example (k : Type u) [Field k] (n : ℕ) :
    IsZero ((SmoothSite.boundaryOneSheafComplex k).homology n) :=
  SmoothSite.isZero_homology_boundaryOneSheafComplex k n

open Lean in
open _root_.AlgebraicGeometry.Scheme.SmoothSite in
run_cmd do
  for name in #[``_root_.AlgebraicSimplex.schemeBoundaryOneSimplicialIso,
      ``_root_.AlgebraicSimplex.isZero_homology_affineRelativeBoundaryOne,
      ``_root_.AlgebraicSimplex.affineSourceRelativeSimplexIso,
      ``_root_.AlgebraicSimplex.parameterRelativeSimplexIso,
      ``_root_.AlgebraicGeometry.Scheme.SmoothSite.integralAffineInclusion_isCoverDense,
      ``_root_.AlgebraicGeometry.Scheme.SmoothSite.isZero_sheafify_of_integral_affine,
      ``isZero_sheafified_homology_of_integral_affine,
      ``_root_.AlgebraicGeometry.Scheme.SmoothSite.isZero_homology_boundaryOne_affine,
      ``_root_.AlgebraicGeometry.Scheme.SmoothSite.isZero_homology_largeBoundaryOne_affine,
      ``_root_.AlgebraicGeometry.Scheme.SmoothSite.isZero_homology_boundaryOneSheafComplex] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "All-degree genuine boundary-one sheaf acyclicity uses only standard Lean foundations."
