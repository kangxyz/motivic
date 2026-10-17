module

public import Motivic.AlgebraicGeometry.Sites.FiniteEtaleCohomologyComparison
public import Lean.Util.CollectAxioms

/-! Direct original-H consumer and axiom audit. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
universe w w' u
variable {B : Scheme.{u}} [IsAffine B] (X : SmoothSite B)
  [HasExt.{w} (Sheaf (SmoothSite.nisnevichTopology B) AddCommGrpCat.{u + 1})]
  [HasExt.{w'} (Sheaf (FiniteEtaleSite.nisnevichTopology X.left) AddCommGrpCat.{u + 1})]

example (F : Sheaf (SmoothSite.nisnevichTopology B) AddCommGrpCat.{u + 1}) (n : ℕ) :
    SheafCohomology.H.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology B) F n X ≃+
    SheafCohomology.H.{w', u + 1, u, u + 1} (FiniteEtaleSite.nisnevichTopology X.left)
      ((FiniteEtaleSite.restrict X AddCommGrpCat).obj F) n (FiniteEtaleSite.identityObject X) :=
  FiniteEtaleSite.cohomologyAtBaseEquiv X F n

example : PreservesFiniteLimits (FiniteEtaleSite.extend X) := inferInstance
example : PreservesFiniteColimits (FiniteEtaleSite.extend X) := inferInstance
example : PreservesFiniteLimits (FiniteEtaleSite.restrict X AddCommGrpCat.{u + 1}) := inferInstance
example : PreservesFiniteColimits (FiniteEtaleSite.restrict X AddCommGrpCat.{u + 1}) :=
  inferInstance

open Lean in
run_cmd do
  for name in #[``FiniteEtaleSite.cohomologyRestrictionEquiv,
      ``FiniteEtaleSite.cohomologyAtBaseEquiv,
      ``FiniteEtaleSite.extendFactorizationIso,
      ``SliceSheaf.nativeExtensionIso,
      ``SlicePresheaf.adjunction] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Big-to-small cohomology comparison: standard Lean foundations only."
