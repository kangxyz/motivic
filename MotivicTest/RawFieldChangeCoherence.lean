/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Motivic.RawFieldChangeCoherence

/-!
# Consumers of the original all-degree field-change coherence

These consumers use the original raw cochain maps and the original derived
integral and finite maps. The fields and homomorphisms are arbitrary, and no
coefficient-level invertibility or finite-generation hypothesis is supplied.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic

universe w u

namespace MotivicTest.RawFieldChangeCoherence

variable {k L M : Type u} [Field k] [Field L] [Field M]

/-- The identity is an equality of the original whole raw complexes. -/
theorem originalRawIdentity (q : ℕ) :
    motivicRawBaseComplexMap (RingHom.id k) q = 𝟙 (motivicRawBaseComplex k q) :=
  motivicRawBaseComplexMap_id q

/-- The tower law compares the original public raw cochain maps. -/
theorem originalRawTower (φ : k →+* L) (ψ : L →+* M) (q : ℕ) :
    motivicRawBaseComplexMap (ψ.comp φ) q =
      motivicRawBaseComplexMap φ q ≫ motivicRawBaseComplexMap ψ q :=
  motivicRawBaseComplexMap_comp φ ψ q

/-- Every integer degree, including the zero-extended degrees, satisfies the
same original map equality. -/
theorem everyRawDegreeTower (φ : k →+* L) (ψ : L →+* M) (q : ℕ) (i : ℤ) :
    (motivicRawBaseComplexMap (ψ.comp φ) q).f i =
      (motivicRawBaseComplexMap φ q).f i ≫ (motivicRawBaseComplexMap ψ q).f i :=
  congrArg (fun f => f.f i) (motivicRawBaseComplexMap_comp φ ψ q)

variable [HasDerivedCategory.{w}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of L))) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of M))) AddCommGrpCat.{u + 1})]

/-- The original actual derived integral map has the identity law. -/
theorem originalIntegralIdentity (p : ℤ) (q : ℕ) :
    motivicCohomologyFieldChange (RingHom.id k) p q = AddMonoidHom.id _ :=
  motivicCohomologyFieldChange_id p q

/-- The original actual derived integral maps compose in every bidegree. -/
theorem originalIntegralTower (φ : k →+* L) (ψ : L →+* M) (p : ℤ) (q : ℕ) :
    motivicCohomologyFieldChange (ψ.comp φ) p q =
      (motivicCohomologyFieldChange ψ p q).comp (motivicCohomologyFieldChange φ p q) :=
  motivicCohomologyFieldChange_comp φ ψ p q

/-- The actual finite map has the identity law at every level. -/
theorem originalFiniteIdentity (p : ℤ) (q n : ℕ) :
    motivicFiniteCohomologyFieldChange (RingHom.id k) p q n = AddMonoidHom.id _ :=
  motivicFiniteCohomologyFieldChange_id p q n

/-- The original finite maps compose at arbitrary coefficient level. -/
theorem originalFiniteTower (φ : k →+* L) (ψ : L →+* M) (p : ℤ) (q n : ℕ) :
    motivicFiniteCohomologyFieldChange (ψ.comp φ) p q n =
      (motivicFiniteCohomologyFieldChange ψ p q n).comp
        (motivicFiniteCohomologyFieldChange φ p q n) :=
  motivicFiniteCohomologyFieldChange_comp φ ψ p q n

/-- In particular, the original characteristic level needs no invertibility premise. -/
theorem characteristicLevelTower (φ : k →+* L) (ψ : L →+* M) (p : ℤ) (q : ℕ) :
    motivicFiniteCohomologyFieldChange (ψ.comp φ) p q (ringChar k) =
      (motivicFiniteCohomologyFieldChange ψ p q (ringChar k)).comp
        (motivicFiniteCohomologyFieldChange φ p q (ringChar k)) :=
  motivicFiniteCohomologyFieldChange_comp φ ψ p q (ringChar k)

open Lean in
run_cmd do
  for name in [
      ``Motivic.SmoothSite.fieldBaseChangeObjectIdIso_naturality,
      ``Motivic.SmoothSite.torusBaseChangeIso_id,
      ``Motivic.SmoothSite.fieldBaseChangeComparison_inv_original,
      ``Motivic.SmoothSite.torusBaseChangeIso_comp_inv,
      ``Motivic.SmoothSite.torusBaseChangeIso_comp,
      ``Motivic.SmoothSite.torusPowerBaseChangeIso_id,
      ``Motivic.SmoothSite.torusPowerBaseChangeIso_comp,
      ``Motivic.SmoothSite.simplexBaseChangeIso_id,
      ``Motivic.SmoothSite.simplexBaseChangeIso_comp_inv,
      ``Motivic.SmoothSite.simplexBaseChangeIso_comp,
      ``Motivic.SmoothSite.baseSimplexFieldChangeIso_hom_snd,
      ``Motivic.SmoothSite.baseSimplexFieldChangeIso_id,
      ``Motivic.SmoothSite.baseSimplexFieldChangeIso_comp,
      ``Motivic.Cor.fieldBaseChange_id_graph,
      ``Motivic.Cor.fieldBaseChange_comp_graph,
      ``Motivic.SmoothSite.baseSimplex_isIntegral,
      ``Motivic.SmoothSite.fieldBaseChange_baseSimplex_isIntegral,
      ``Motivic.SmoothSite.baseSimplexFieldChangeIso_comp_inv,
      ``Motivic.SmoothSite.baseSimplexFieldChangeIso_id_inv,
      ``Motivic.PresheafWithTransfers.reducedTorusSingularFieldChange_id,
      ``Motivic.PresheafWithTransfers.reducedTorusSingularCycleFieldChange_comp,
      ``Motivic.PresheafWithTransfers.reducedTorusSingularFieldChange_comp,
      ``Motivic.RawFieldChange.component_id,
      ``Motivic.RawFieldChange.component_comp,
      ``Motivic.RawFieldChange.unshiftedMap_id,
      ``Motivic.RawFieldChange.unshiftedMap_comp,
      ``Motivic.motivicRawBaseComplexMap_id,
      ``Motivic.motivicRawBaseComplexMap_comp,
      ``Motivic.motivicBaseComplexMap_id,
      ``Motivic.motivicBaseComplexMap_comp,
      ``Motivic.motivicBaseFiniteConeMap_id,
      ``Motivic.motivicBaseFiniteConeMap_comp,
      ``Motivic.motivicCohomologyFieldChange_id,
      ``Motivic.motivicFiniteCohomologyFieldChange_id,
      ``Motivic.motivicCohomologyFieldChange_comp,
      ``Motivic.motivicFiniteCohomologyFieldChange_comp,
      ``originalRawIdentity,
      ``originalRawTower,
      ``everyRawDegreeTower,
      ``originalIntegralIdentity,
      ``originalIntegralTower,
      ``originalFiniteIdentity,
      ``originalFiniteTower,
      ``characteristicLevelTower] do
    let dependencies ← collectAxioms name
    for dependency in dependencies do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Original all-degree raw and derived field-change coherence uses standard foundations."

end MotivicTest.RawFieldChangeCoherence
