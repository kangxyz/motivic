/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Diagonal.CorestrictionPresentationTransport
public import Lean.Util.CollectAxioms

/-!
# Consumers of actual transfer presentation transport

The two original finite extension fields and their original algebra structures
are retained. No norm law or field replacement is an assumption. The consumers
check every weight, both graph representatives and all Milnor classes, and the
original derived comparison.
-/

@[expose] public noncomputable section

open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory AlgebraicGeometry Motivic
open Motivic.DiagonalCycleSymbols Motivic.DiagonalMilnorSymbol Motivic.DiagonalCorestriction

universe w u

namespace MotivicTest.DiagonalCorestrictionPresentationTransport

variable {k E F : Type u} [Field k] [Field E] [Field F]
  [Algebra k E] [Algebra k F] [Module.Finite k E] [Module.Finite k F]

/-- Graph-level presentation transport preserves the full actual finite pushforward. -/
theorem actual_graph_transport (ε : E ≃ₐ[k] F) (n : ℕ) (a : Fin n → Eˣ) :
    corestriction (k := k) (E := E) n (graphSymbol E n a) =
    corestriction (k := k) (E := F) n
      (graphSymbol F n (fun i => Units.map ε.toRingHom.toMonoidHom (a i))) :=
  corestriction_graphSymbol_algEquiv ε n a

variable [CharZero E] [CharZero F]

/-- Every Milnor class retains the original raw transfer after changing its presentation. -/
theorem actual_raw_transport (ε : E ≃ₐ[k] F) (n : ℕ) (x : MilnorK.K E n) :
    corestriction (k := k) (E := E) n (rawSymbol E n x) =
    corestriction (k := k) (E := F) n (rawSymbol F n (MilnorK.map n ε.toRingHom x)) :=
  corestriction_rawSymbol_algEquiv ε n x

/-- A comparison already proved on a presentation transfers without a norm-compatibility axiom. -/
theorem comparison_from_presentation (ε : E ≃ₐ[k] F) (n : ℕ)
    (g : MilnorK.K F n →+ (motivicRawBaseComplex k n).homology n)
    (h : ∀ y, corestriction (k := k) (E := F) n (rawSymbol F n y) = g y)
    (x : MilnorK.K E n) :
    corestriction (k := k) (E := E) n (rawSymbol E n x) = g (MilnorK.map n ε.toRingHom x) :=
  (corestriction_rawSymbol_algEquiv ε n x).trans (h _)

variable [HasDerivedCategory.{w}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of E))) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of F))) AddCommGrpCat.{u + 1})]

/-- Presentation transport also retains the actual original derived groups. -/
theorem actual_derived_transport (ε : E ≃ₐ[k] F) (n : ℕ) (x : MilnorK.K E n) :
    motivicCorestriction (k := k) (E := E) n (motivicSymbol E n x) =
    motivicCorestriction (k := k) (E := F) n
      (motivicSymbol F n (MilnorK.map n ε.toRingHom x)) :=
  motivicCorestriction_motivicSymbol_algEquiv ε n x

open Lean in
run_cmd do
  for name in #[``rationalTuple_algHom, ``finitePointMap_algHom,
      ``pointPushforward_graph_algEquiv, ``corestriction_graphSymbol_algEquiv,
      ``corestriction_rawSymbol_algEquiv, ``motivicCorestriction_motivicSymbol_algEquiv,
      ``actual_graph_transport, ``actual_raw_transport, ``comparison_from_presentation,
      ``actual_derived_transport] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual all-weight transfer presentation transport uses only standard foundations."

end MotivicTest.DiagonalCorestrictionPresentationTransport
