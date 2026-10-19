/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Graph.Flat.LeftComposition
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Simplex.Basic
public import Lean.Util.CollectAxioms

/-!
# Consumers of actual flat left-graph composition

The first consumers use arbitrary flat support projections, without any
assumed equality between Tor and length. The endpoint consumers use the
literal graph functor and the actual zero- and one-simplex over every field.
The full original fiber stalk appears in the multiplicity formula; no
reducedness or separability hypothesis is introduced.
-/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme (fundamentalCycle)
open _root_.AlgebraicGeometry.Scheme (IntegralCycle)
open _root_.AlgebraicGeometry.Scheme.Products (correspondenceTripleInclusion)
open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open RingTheory.Sequence
open scoped Simplicial

universe u

namespace MotivicTest.FlatLeftGraphComposition

variable (k : Type u) [Field k] {X Y Z : SmoothSite (Spec (.of k))}

local instance (T : SmoothSite (Spec (.of k))) : IsNoetherian ((𝟭 Scheme).obj T.left) :=
  inferInstanceAs (IsNoetherian T.left)

/-- Actual flatness supplies regularity of the actual original coefficient list. -/
theorem flat_regular_list
    (A : FiniteCorrespondenceGenerator X.hom Y.hom)
    (B : FiniteCorrespondenceGenerator Y.hom Z.hom) [Flat B.projection]
    (w : A.incidence B) :
    ∃ s : List (A.incidenceAmbientStalk B w),
      RingHom.ker ((correspondenceTripleInclusion X.hom Y.hom Z.hom).stalkMap
        (A.incidenceInclusion B w)).hom = Ideal.ofList s ∧
      IsRegular (A.incidenceAmbientStalk B w) s ∧
      IsWeaklyRegular (A.incidenceSupportStalkModule B w) s :=
  A.exists_incidence_regular_list_of_flat_projection B w

/-- The genuine higher Tor objects vanish, without a supplied Tor premise. -/
theorem flat_positive_tor
    (A : FiniteCorrespondenceGenerator X.hom Y.hom)
    (B : FiniteCorrespondenceGenerator Y.hom Z.hom) [Flat B.projection]
    (w : A.incidence B) (n : ℕ) : IsZero (A.incidenceTor B w (n + 1)) :=
  A.isZero_incidenceTor_succ_of_flat_projection B w n

/-- Both signed coefficients survive the actual fundamental-cycle comparison. -/
theorem signed_flat_basis
    (A : FiniteCorrespondenceGenerator X.hom Y.hom)
    (B : FiniteCorrespondenceGenerator Y.hom Z.hom) [Flat B.projection] (m n : ℤ) :
    FiniteCorrespondence.incidenceTorPairing k (X := X) (Y := Y) (Z := Z)
      (Finsupp.single A m) (Finsupp.single B n) =
      (m * n) • A.incidenceFundamentalCorrespondence k B := by
  rw [FiniteCorrespondence.incidenceTorPairing_single,
    A.incidenceTorCorrespondence_eq_fundamental_of_flat_projection k B]

/-- Every map from an integral smooth source computes the literal whole fiber. -/
theorem actual_graph_fiber [IsIntegral X.left]
    (B : FiniteCorrespondenceGenerator Y.hom Z.hom) [Flat B.projection] (φ : X ⟶ Y) :
    FiniteCorrespondence.toIntegralCycle (f := X.hom) (g := Z.hom)
      ((Cor.graphFunctor k).map φ ≫ (show Cor.mk Y ⟶ Cor.mk Z from B.cycle)) =
      IntegralCycle.finitePushforward (B.graphPullbackMap φ.left (MorphismProperty.Over.w φ))
        (fundamentalCycle (pullback φ.left B.projection)) :=
  B.toIntegralCycle_graphFunctor_comp k φ

/-- The unchanged scheme-theoretic fiber stalk supplies the actual integer length. -/
theorem original_fiber_stalk_length [IsIntegral X.left]
    (B : FiniteCorrespondenceGenerator Y.hom Z.hom) [Flat B.projection]
    (φ : X ⟶ Y)
    (x : genericPoints ((graphGeneratorOver φ.left (MorphismProperty.Over.w φ)).incidence B)) :
    (graphGeneratorOver φ.left (MorphismProperty.Over.w φ)).incidenceTorCoefficient
      (S := Spec (.of k)) B x =
      ((Module.length
        ((B.graphPullback φ.left).presheaf.stalk
          ((B.leftGraphIncidenceIso φ.left (MorphismProperty.Over.w φ)).hom x.val))
        ((B.graphPullback φ.left).presheaf.stalk
          ((B.leftGraphIncidenceIso φ.left (MorphismProperty.Over.w φ)).hom x.val))).toNat : ℤ) :=
  B.incidenceTorCoefficient_graph_left_eq_fiberMultiplicity k φ.left
    (MorphismProperty.Over.w φ) x

/-- A base-field point, including an endpoint, has precisely its whole fiber cycle. -/
theorem base_field_endpoint
    (B : FiniteCorrespondenceGenerator Y.hom Z.hom) [Flat B.projection]
    (e : SmoothSite.base (Spec (.of k)) ⟶ Y) :
    FiniteCorrespondence.toIntegralCycle
      (f := (SmoothSite.base (Spec (.of k))).hom) (g := Z.hom)
      ((Cor.graphFunctor k).map e ≫ (show Cor.mk Y ⟶ Cor.mk Z from B.cycle)) =
      IntegralCycle.finitePushforward (B.graphPullbackMap e.left (MorphismProperty.Over.w e))
        (fundamentalCycle (pullback e.left B.projection)) := by
  have : IsIntegral (SmoothSite.base (Spec (.of k))).left :=
    inferInstanceAs (IsIntegral (Spec (.of k)))
  exact B.toIntegralCycle_graphFunctor_comp k e

local instance simplex_integral (n : ℕ) :
    IsIntegral (_root_.AlgebraicSimplex.smoothSiteObj k n).left :=
  inferInstanceAs (IsIntegral (Spec (.of (_root_.AlgebraicSimplex.CoordinateRing k n))))

/-- Both actual faces of the one-simplex compute whole fibers, including their lengths. -/
theorem one_simplex_face
    (B : FiniteCorrespondenceGenerator (_root_.AlgebraicSimplex.smoothSiteObj k 1).hom Z.hom)
    [Flat B.projection] (i : Fin 2) :
    let e : _root_.AlgebraicSimplex.smoothSiteObj k 0 ⟶ _root_.AlgebraicSimplex.smoothSiteObj k 1 :=
      (_root_.AlgebraicSimplex.cosimplicialSmoothSite k).δ i
    FiniteCorrespondence.toIntegralCycle
      (f := (_root_.AlgebraicSimplex.smoothSiteObj k 0).hom) (g := Z.hom)
      ((Cor.graphFunctor k).map e ≫
        (show Cor.mk (_root_.AlgebraicSimplex.smoothSiteObj k 1) ⟶ Cor.mk Z from B.cycle)) =
      IntegralCycle.finitePushforward (B.graphPullbackMap e.left (MorphismProperty.Over.w e))
        (fundamentalCycle (pullback e.left B.projection)) := by
  dsimp only
  exact B.toIntegralCycle_graphFunctor_comp k _

open Lean Motivic.FiniteCorrespondenceGenerator in
run_cmd do
  for name in #[
      ``exists_incidence_regular_list_of_flat_projection,
      ``isZero_incidenceTor_succ_of_flat_projection,
      ``incidenceTorCorrespondence_eq_fundamental_of_flat_projection,
      ``toIntegralCycle_graphFunctor_comp,
      ``incidenceTorCoefficient_graph_left_eq_fiberMultiplicity,
      ``base_field_endpoint, ``one_simplex_face, ``original_fiber_stalk_length] do
    let dependencies ← collectAxioms name
    for dependency in dependencies do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Flat left-graph Tor and fiber cycles use only standard Lean logical foundations."

end MotivicTest.FlatLeftGraphComposition
