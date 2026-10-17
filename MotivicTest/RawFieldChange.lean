/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Motivic.RawFieldChange

/-!
# Actual arbitrary-field raw motivic complex consumers

The original quotient-cycle formulas, all singular degrees, and the signed
cochain differential are checked without restricting the field extension.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Motivic Opposite
open Motivic.PresheafWithTransfers

universe u v

namespace MotivicTest.RawFieldChange

variable {k L : Type u} [Field k] [Field L] (φ : k →+* L)

/-- Restriction retains an independently chosen coefficient universe. -/
example (P : PresheafWithTransfers.{v} L) :
    (fieldChangeRestriction φ P).obj.Additive := inferInstance

/-- The genuine all-degree map uses the fixed coefficient universe of the raw complexes. -/
example (q : ℕ) : motivicRawBaseComplex k q ⟶ motivicRawBaseComplex L q :=
  motivicRawBaseComplexMap φ q

/-- Both the original and new identity axes are actual torus-coordinate graphs. -/
theorem quotientAxes (q : ℕ) (i : Fin q) :
    torusIdentityAxis k q i ≫ torusFieldChangeToReduced φ q = 0 :=
  torusFieldChangeToReduced_axis φ q i

/-- Actual signed cycles from the base transform through the two literal comparisons. -/
theorem signedBaseCycle (q : ℕ)
    (α : Cor.mk (SmoothSite.base (Spec (.of k))) ⟶
      Cor.mk (SmoothSite.torusPower (.of k) q)) (m : ℤ) :
    baseTorusCycleFieldChange φ q (m • α) =
      m • ((Cor.graphFunctor L).map
        (SmoothSite.baseChangeBaseIso (Spec.map (CommRingCat.ofHom φ))).inv ≫
          (Cor.fieldBaseChange φ).map α ≫ (Cor.graphFunctor L).map
            (SmoothSite.torusPowerBaseChangeIso (CommRingCat.ofHom φ) q).hom) :=
  map_zsmul (baseTorusCycleFieldChange φ q) m α

/-- Every simplex map, including faces and degeneracies, respects actual coefficient change. -/
theorem everySimplexMap {m n : SimplexCategory} (f : m ⟶ n) :
    (SmoothSite.fieldBaseChange φ).map
      (SmoothSite.productMap (𝟙 (SmoothSite.base (Spec (.of k))))
        ((AlgebraicSimplex.cosimplicialSmoothSite k).map f)) ≫
          (SmoothSite.baseSimplexFieldChangeIso φ n).hom =
      (SmoothSite.baseSimplexFieldChangeIso φ m).hom ≫
        SmoothSite.productMap (𝟙 (SmoothSite.base (Spec (.of L))))
          ((AlgebraicSimplex.cosimplicialSmoothSite L).map f) :=
  SmoothSite.baseSimplexFieldChangeIso_naturality φ f

/-- The canonical occupied-degree dictionary retains the actual singular map. -/
theorem allOccupiedDegrees (q r : ℕ) :
    (motivicRawBaseComplexMap φ q).f (Indexing.singularDegree q r) =
      (motivicRawBaseComplexXIso k q r).hom ≫
        (reducedTorusSingularFieldChange φ q).f r ≫
          (motivicRawBaseComplexXIso L q r).inv :=
  motivicRawBaseComplexMap_f φ q r

/-- All integer-degree differentials retain the original signed shift. -/
theorem allDifferentials (q : ℕ) (i j : ℤ) :
    (motivicRawBaseComplexMap φ q).f i ≫ (motivicRawBaseComplex L q).d i j =
      (motivicRawBaseComplex k q).d i j ≫ (motivicRawBaseComplexMap φ q).f j :=
  motivicRawBaseComplexMap_comm φ q i j

/-- The weight-one minus sign is retained by the very same cochain equation. -/
theorem weightOneDifferential :
    (motivicRawBaseComplexMap φ 1).f 0 ≫ (motivicRawBaseComplex L 1).d 0 1 =
      (motivicRawBaseComplex k 1).d 0 1 ≫ (motivicRawBaseComplexMap φ 1).f 1 :=
  allDifferentials φ 1 0 1

open Lean in
run_cmd do
  for name in #[``quotientAxes, ``signedBaseCycle, ``everySimplexMap, ``allOccupiedDegrees,
      ``allDifferentials, ``weightOneDifferential,
      ``SmoothSite.baseChangeProductIso_naturality,
      ``SmoothSite.baseSimplexFieldChangeIso_naturality,
      ``Cor.baseSimplexFieldChangeIso,
      ``torusFieldChange, ``reducedTorusFieldChange,
      ``reducedTorusFieldChange_quotient, ``baseTorusCycleFieldChange,
      ``baseReducedTorusFieldChange_quotient,
      ``reducedTorusSimplicialFieldChange, ``reducedTorusSingularFieldChange_quotient,
      ``motivicRawBaseComplexMap] do
    let dependencies ← collectAxioms name
    for dependency in dependencies do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual arbitrary-field raw motivic maps use only standard foundations."

end MotivicTest.RawFieldChange
