/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Motivic.WeightTwoCorestrictionDegree
public import Lean.Util.CollectAxioms

/-!
# Whole-support scalar degree consumers

These consumers retain the original signed correspondence groups, arbitrary
finite field extensions, and nonreduced scalar-extended support schemes.
No separability or supplied homology-descent assumption is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open WeightTwoCorestriction PresheafWithTransfers WeightOnePointNorm
open scoped Simplicial

universe w u

namespace MotivicTest.WeightTwoCorestrictionDegree

variable {k E : Type u} [Field k] [Field E] [Algebra k E] [Module.Finite k E]

/-- The original signed point cycle is multiplied by the full extension degree. -/
theorem actual_point_degree (α : point k ⟶ WeightTwoSymbols.target k) :
    pointPushforward (k := k) (E := E)
      (baseTorusCycleFieldChange (algebraMap k E) 2 α) =
      (Module.finrank k E : ℤ) • α :=
  pointPushforward_baseTorusCycleFieldChange α

/-- All original signs survive, including arbitrary negative coefficients. -/
theorem signed_point_degree (α β : point k ⟶ WeightTwoSymbols.target k) (n m : ℤ) :
    pointPushforward (k := k) (E := E)
      (baseTorusCycleFieldChange (algebraMap k E) 2 (n • α - m • β)) =
      (Module.finrank k E : ℤ) • (n • α - m • β) :=
  pointPushforward_baseTorusCycleFieldChange _

/-- The same actual degree formula holds in every original singular degree. -/
theorem all_simplex_degrees (r q : ℕ)
    (α : Cor.mk (source k r) ⟶ Cor.mk (WeightTwoCorestriction.target k q)) :
    cyclePushforward (k := k) (E := E) r q
      ((Cor.graphFunctor E).map
        (SmoothSite.baseSimplexFieldChangeIso (algebraMap k E) ⦋r⦌).inv ≫
          (Cor.fieldBaseChange (algebraMap k E)).map α ≫ (Cor.graphFunctor E).map
            (SmoothSite.torusPowerBaseChangeIso (CommRingCat.ofHom (algebraMap k E)) q).hom) =
      (Module.finrank k E : ℤ) • α :=
  cyclePushforward_fieldBaseChange r q α

/-- The formula applies to every original raw H22 class, not only rational symbols. -/
theorem actual_homology_degree (x : (motivicRawBaseComplex k 2).homology 2) :
    corestriction (k := k) (E := E)
      (HomologicalComplex.homologyMap
        (motivicRawBaseComplexMap (algebraMap k E) 2) 2 x) =
      (Module.finrank k E : ℤ) • x :=
  corestriction_fieldChange x

section Derived

variable [HasDerivedCategory.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of E))) AddCommGrpCat.{u + 1})]

/-- The actual motivic group has the same full finite-extension degree formula. -/
theorem actual_motivic_degree
    (x : motivicCohomology k 2 2 (SmoothSite.base (Spec (.of k)))) :
    motivicCorestriction (k := k) (E := E)
      (motivicCohomologyFieldChange (algebraMap k E) 2 2 x) =
      (Module.finrank k E : ℤ) • x :=
  motivicCorestriction_fieldChange x

end Derived

open Lean in
run_cmd do
  for name in #[``finitePushforward_scalar_fundamentalCycle,
      ``finitePushforward_fieldBaseChangeCycle, ``finitePushforward_fieldBaseChange,
      ``graphTransportIso_ambientMap, ``cyclePushforward_fieldBaseChange,
      ``pointPushforward_baseTorusCycleFieldChange,
      ``actual_point_degree, ``signed_point_degree, ``all_simplex_degrees,
      ``corestriction_fieldChange, ``motivicCorestriction_fieldChange,
      ``actual_homology_degree, ``actual_motivic_degree] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Whole scalar degree and original signed cycle transfer use only standard foundations."

end MotivicTest.WeightTwoCorestrictionDegree
