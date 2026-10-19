module

public import Motivic.Cohomology.WeightOne.Geometry.WeightOneExact
public import Motivic.Cohomology.SuslinVoevodsky.Hypercohomology
public import Lean.Util.CollectAxioms

/-! # Direct audit of the original ordinary Nisnevich weight-one divisor sequence -/

open CategoryTheory Motivic

universe u
example (k : Type u) [Field k] : (SmoothSiteWeightOneExact.shortComplex k).ShortExact :=
  SmoothSiteWeightOneExact.shortExact k

open Lean in
run_cmd do
  for name in #[``_root_.AlgebraicGeometry.Scheme.SmoothSite.integralAffineRawKernelIso,
      ``_root_.AlgebraicGeometry.Scheme.SmoothSite.integralAffineSheafifyMapIsKernel,
      ``SmoothSiteWeightOneExact.divisorIsKernel,
      ``SmoothSiteWeightOneExact.norm_epi,
      ``SmoothSiteWeightOneExact.shortExact] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Original ordinary Nisnevich weight-one divisor SES uses only standard Lean foundations."
