module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.CohomologyComparison
public import Lean.Util.CollectAxioms

/-! Direct original-H consumer and axiom audit. -/
@[expose] public noncomputable section
open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe w w' u
variable {B : Scheme.{u}} [IsAffine B] (X : SmoothSite B)
  [HasExt.{w} (Sheaf (SmoothSite.nisnevichTopology B) AddCommGrpCat.{u + 1})]
  [HasExt.{w'} (Sheaf
      (_root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.nisnevichTopology X.left)
      AddCommGrpCat.{u + 1})]

example (F : Sheaf (SmoothSite.nisnevichTopology B) AddCommGrpCat.{u + 1}) (n : ℕ) :
    _root_.CategoryTheory.Sheaf.LargeCohomology.H.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology
        B) F n X ≃+
    _root_.CategoryTheory.Sheaf.LargeCohomology.H.{w', u + 1, u, u + 1}
        (_root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.nisnevichTopology X.left)
      ((_root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.restrict X AddCommGrpCat).obj F) n
          (_root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.identityObject X) :=
  _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.cohomologyAtBaseEquiv X F n

example : PreservesFiniteLimits (_root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.extend
    X) := inferInstance
example : PreservesFiniteColimits
    (_root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.extend X) := inferInstance
example : PreservesFiniteLimits
    (_root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.restrict X AddCommGrpCat.{u + 1}) :=
    inferInstance
example : PreservesFiniteColimits
    (_root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.restrict X AddCommGrpCat.{u + 1}) :=
  inferInstance

open Lean in
run_cmd do
  for name in
      #[``_root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.cohomologyRestrictionEquiv,
      ``_root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.cohomologyAtBaseEquiv,
      ``_root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.extendFactorizationIso,
      ``_root_.CategoryTheory.SliceSheaf.nativeExtensionIso,
      ``_root_.CategoryTheory.SlicePresheaf.adjunction] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Big-to-small cohomology comparison: standard Lean foundations only."
