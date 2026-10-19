/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Cycles.ScalarExtension.FinitePointBaseChange
public import Mathlib.RingTheory.DualNumber
public import Lean.Util.CollectAxioms

/-! # Consumers of whole finite-point pushforward under field change -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.Cycles.FinitePointBaseChange

universe u

namespace MotivicTest.FinitePointBaseChange
open _root_.AlgebraicGeometry.Scheme.Cycles.FinitePointBaseChange

variable {k L E : Type u} [Field k] [Field L] [Field E]
  [Algebra k E] [Module.Finite k E] (φ : k →+* L)

/-- The actual finite extension morphism, with its original scalar map. -/
def extensionMap : Spec (.of E) ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k E))

instance extensionMap_finite : IsFinite (extensionMap (k := k) (E := E)) :=
  (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)

/-- Every component of the literal scalar extension is retained in the pushforward. -/
theorem whole_extension :
    _root_.AlgebraicGeometry.Scheme.IntegralCycle.finitePushforward
      (map φ (extensionMap (k := k) (E := E)) (𝟙 _))
      (_root_.AlgebraicGeometry.Scheme.fundamentalCycle (source φ (extensionMap (k := k) (E := E))
          (𝟙 _))) =
      ((extensionMap (k := k) (E := E)).residueDegree
        (genericPoint (Spec (.of E))) : ℤ) • _root_.AlgebraicGeometry.Scheme.fundamentalCycle
            (target φ (𝟙 _)) :=
  finitePushforward_fundamentalCycle φ _ _

/-- Signed coefficients are transported by the actual cycle pushforward. -/
theorem signed_whole_extension (n : ℤ) :
    _root_.AlgebraicGeometry.Scheme.IntegralCycle.finitePushforward
      (map φ (extensionMap (k := k) (E := E)) (𝟙 _))
      (n • _root_.AlgebraicGeometry.Scheme.fundamentalCycle (source φ (extensionMap (k := k) (E :=
          E)) (𝟙 _))) =
      n • (((extensionMap (k := k) (E := E)).residueDegree
        (genericPoint (Spec (.of E))) : ℤ) • _root_.AlgebraicGeometry.Scheme.fundamentalCycle
            (target φ (𝟙 _))) := by
  rw [map_zsmul, whole_extension]

omit [Module.Finite k E] in
/-- The scalar projection is the actual Cartesian projection, without reducing the source. -/
theorem literal_projection :
    map φ (extensionMap (k := k) (E := E)) (𝟙 _) ≫
        pullback.snd (𝟙 _) (Spec.map (CommRingCat.ofHom φ)) =
      pullback.snd (extensionMap (k := k) (E := E) ≫ 𝟙 _)
        (Spec.map (CommRingCat.ofHom φ)) :=
  map_snd φ _ _

/-- Finite-point genericity applies even to the nonreduced dual-number scheme. -/
theorem dual_number_generic (x : Spec (.of (DualNumber k))) :
    x ∈ genericPoints (Spec (.of (DualNumber k))) := by
  let : Module.Finite k (DualNumber k) := inferInstanceAs (Module.Finite k (k × k))
  let p := Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k)))
  let : IsFinite p :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  exact mem_genericPoints_of_finite p x

open Lean in
run_cmd do
  for name in #[``finitePushforward_fundamentalCycle,
      ``mem_genericPoints_of_finite,
      ``whole_extension, ``signed_whole_extension, ``literal_projection,
      ``dual_number_generic] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Whole finite-point field change uses only standard logical foundations."

end MotivicTest.FinitePointBaseChange
