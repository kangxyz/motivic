module

public import Motivic.Cohomology.WeightOne.Geometry.BoundaryOneDivisorNorm
public import Motivic.Cohomology.SuslinVoevodsky.Hypercohomology
public import Lean.Util.CollectAxioms

/-! # Direct audit of the original sheaf boundary divisor and its zero norm -/

open Lean in
open _root_.AlgebraicGeometry.Scheme.SmoothSite in
run_cmd do
  for name in #[``Motivic.SmoothSiteBoundaryOneDivisor.sheafDivisorChainMap,
      ``Motivic.SmoothSiteBoundaryOneDivisor.sheafDivisorChainMap_norm,
      ``_root_.AlgebraicGeometry.Scheme.SmoothSite.integralAffineSheafifyIso,
      ``epi_sheafifyMap_of_integral_affine_surjective] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Original sheaf divisor chain map and zero norm use only standard Lean foundations."
