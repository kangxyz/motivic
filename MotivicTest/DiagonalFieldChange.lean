/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Motivic.DiagonalFieldChange
public import Lean.Util.CollectAxioms

/-!
# Consumers of actual diagonal-symbol field naturality

The field homomorphism is arbitrary within the declared common universe.
The raw graph-class test works over every field, and the actual Milnor symbol
naturality test uses the proved characteristic-zero construction.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Motivic
open Motivic.DiagonalCycleSymbols Motivic.DiagonalMilnorSymbol Motivic.DiagonalFieldChange

universe w u

namespace MotivicTest.DiagonalFieldChange

variable {k L : Type u} [Field k] [Field L] (φ : k →+* L)

/-- Actual rational graph classes retain every ordinary image unit. -/
theorem actual_graph_naturality (n : ℕ) (a : Fin n → kˣ) :
    HomologicalComplex.homologyMap (motivicRawBaseComplexMap φ n) n (graphSymbol k n a) =
      graphSymbol L n (fun i => Units.map φ.toMonoidHom (a i)) :=
  graphSymbol_fieldChange φ n a

variable [CharZero k] [CharZero L]

/-- All-weight standard Milnor field change agrees with the original signed raw map. -/
theorem actual_raw_naturality (n : ℕ) (x : MilnorK.K k n) :
    HomologicalComplex.homologyMap (motivicRawBaseComplexMap φ n) n (rawSymbol k n x) =
      rawSymbol L n (MilnorK.map n φ x) := rawSymbol_fieldChange φ n x

variable [HasDerivedCategory.{w}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of L))) AddCommGrpCat.{u + 1})]

/-- The commutative square uses the original derived motivic field map. -/
theorem actual_derived_naturality (n : ℕ) (x : MilnorK.K k n) :
    motivicCohomologyFieldChange φ n n (motivicSymbol k n x) =
      motivicSymbol L n (MilnorK.map n φ x) := motivicSymbol_fieldChange φ n x

open Lean in
run_cmd do
  for name in #[``rationalTuple_fieldChange, ``rationalGraph_fieldChange, ``rawClass_fieldChange,
      ``topTermIso_fieldChange, ``singularClass_fieldChange, ``cycleClass_fieldChange,
      ``graphSymbol_fieldChange, ``rawSymbol_fieldChange, ``motivicSymbol_fieldChange,
      ``motivicSymbol_fieldChange_square, ``actual_graph_naturality, ``actual_raw_naturality,
      ``actual_derived_naturality] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual all-weight symbol field naturality uses only standard foundations."

end MotivicTest.DiagonalFieldChange
