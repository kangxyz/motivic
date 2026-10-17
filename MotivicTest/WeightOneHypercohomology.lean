module

public import Motivic.Cohomology.Motivic.WeightOneHypercohomology
public import Motivic.AlgebraicGeometry.SmoothSiteTorusGraphNorm
public import Lean.Util.CollectAxioms

/-! # Direct all-smooth-source weight-one comparison audit -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Motivic

universe w w' u
variable (k : Type u) [Field k]
  [HasDerivedCategory.{w}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [HasExt.{w'}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

example (n : ℕ) (X : SmoothSite (Spec (.of k))) :
    motivicCohomology.{w, u} k ((n : ℤ) + 1) 1 X ≃+
      SheafCohomology.H.{w', u + 1, u, u + 1} (SmoothSite.nisnevichTopology (Spec (.of k)))
        (SmoothSite.largeUnitsSheaf (Spec (.of k))) n X :=
  weightOneSheafCohomologyEquiv k n X

open Lean in
run_cmd do
  for name in #[``Hypercohomology.shiftPresheafIso,
      ``weightOneHypercohomologyPresheafIso,
      ``weightOneSheafCohomologyEquiv] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "All-smooth-source weight-one cohomology comparison uses only standard Lean foundations."
