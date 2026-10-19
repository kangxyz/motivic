/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Generators.Basic
public import Motivic.Aglib.AlgebraicGeometry.Scheme.ReducedComponents

/-!
# Graph cycles with reducible sources

For a reduced Noetherian source and a separated target, each irreducible
component of the graph is an actual finite-correspondence generator. Their
finite sum defines the graph cycle without imposing an integral-source
hypothesis. This includes disconnected smooth sources once their usual
Noetherian and reduced properties have been established.

Composition and the graph functor into `Cor` are separate obligations.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic
open _root_.AlgebraicGeometry.Scheme

variable {S X Y : Scheme.{u}} (φ : X ⟶ Y) (g : Y ⟶ S)
  [IsNoetherian X] [IsSeparated g]

section Reduced

variable [IsReduced X]

/-- The actual graph restricted to a specified irreducible source component. -/
noncomputable def componentGraph (Z : Set X) (hZ : Z ∈ irreducibleComponents X) :
    X.irreducibleComponent Z hZ ⟶ pullback (φ ≫ g) g :=
  X.irreducibleComponentι Z hZ ≫ _root_.AlgebraicGeometry.Scheme.Graph.correspondenceGraph φ g

instance (Z : Set X) (hZ : Z ∈ irreducibleComponents X) :
    IsClosedImmersion (componentGraph φ g Z hZ) := by
  unfold componentGraph
  infer_instance

/-- The ideal cutting out one graph component in the original fiber product. -/
noncomputable def componentGraphIdeal (Z : Set X) (hZ : Z ∈ irreducibleComponents X) :
    (pullback (φ ≫ g) g).IdealSheafData := (componentGraph φ g Z hZ).ker

omit [IsReduced X] [IsSeparated g] in
@[reassoc, simp]
theorem componentGraph_toImage_projection (Z : Set X) (hZ : Z ∈ irreducibleComponents X) :
    (componentGraph φ g Z hZ).toImage ≫
      correspondenceProjection (φ ≫ g) g (componentGraphIdeal φ g Z hZ) =
        X.irreducibleComponentι Z hZ := by
  simp [componentGraphIdeal, correspondenceProjection, componentGraph]

instance (Z : Set X) (hZ : Z ∈ irreducibleComponents X) :
    IsFinite (correspondenceProjection (φ ≫ g) g (componentGraphIdeal φ g Z hZ)) := by
  let h := componentGraph φ g Z hZ
  have : IsIso h.toImage := IsClosedImmersion.instIsIsoSchemeToImage _
  have heq : correspondenceProjection (φ ≫ g) g (componentGraphIdeal φ g Z hZ) =
      inv h.toImage ≫ X.irreducibleComponentι Z hZ := by
    apply (cancel_epi h.toImage).mp
    simp [h]
  rw [heq]
  have : IsIso (inv h.toImage) := (asIso h.toImage).symm.isIso_hom
  exact MorphismProperty.IsStableUnderComposition.comp_mem
    (P := @IsFinite) (inv h.toImage) (X.irreducibleComponentι Z hZ)
    (inferInstanceAs (IsFinite (inv h.toImage)))
    (inferInstanceAs (IsFinite (X.irreducibleComponentι Z hZ)))

omit [IsReduced X] in
/-- The graph component projects precisely onto its original source component. -/
theorem componentGraph_range_projection (Z : Set X) (hZ : Z ∈ irreducibleComponents X) :
    Set.range (correspondenceProjection (φ ≫ g) g (componentGraphIdeal φ g Z hZ)) = Z := by
  have : IsIso (componentGraph φ g Z hZ).toImage :=
    IsClosedImmersion.instIsIsoSchemeToImage _
  have hsurj : Function.Surjective (componentGraph φ g Z hZ).toImage :=
    (Scheme.homeoOfIso (asIso (componentGraph φ g Z hZ).toImage)).surjective
  calc
    Set.range (correspondenceProjection (φ ≫ g) g (componentGraphIdeal φ g Z hZ)) =
        Set.range (correspondenceProjection (φ ≫ g) g (componentGraphIdeal φ g Z hZ) ∘
          (componentGraph φ g Z hZ).toImage) := (hsurj.range_comp _).symm
    _ = Set.range ((componentGraph φ g Z hZ).toImage ≫
        correspondenceProjection (φ ≫ g) g (componentGraphIdeal φ g Z hZ)) := rfl
    _ = Z := by rw [componentGraph_toImage_projection, range_irreducibleComponentι]

/-- A componentwise graph is a genuine geometric correspondence generator. -/
noncomputable def componentGraphGenerator (Z : Set X) (hZ : Z ∈ irreducibleComponents X) :
    FiniteCorrespondenceGenerator (φ ≫ g) g := by
  refine ⟨componentGraphIdeal φ g Z hZ, ?_, inferInstance, ?_⟩
  · change IsIntegral (componentGraph φ g Z hZ).image
    have : IsIso (componentGraph φ g Z hZ).toImage :=
      IsClosedImmersion.instIsIsoSchemeToImage _
    exact IsIntegral.of_isIso (componentGraph φ g Z hZ).toImage
  · rw [componentGraph_range_projection]
    exact hZ

/-- The original component is recovered from the graph generator's source projection. -/
@[simp]
theorem componentGraphGenerator_range (Z : Set X) (hZ : Z ∈ irreducibleComponents X) :
    Set.range (componentGraphGenerator φ g Z hZ).projection = Z :=
  componentGraph_range_projection φ g Z hZ

/-- Different irreducible source components give different graph generators. -/
@[simp]
theorem componentGraphGenerator_eq_iff (Z W : Set X)
    (hZ : Z ∈ irreducibleComponents X) (hW : W ∈ irreducibleComponents X) :
    componentGraphGenerator φ g Z hZ = componentGraphGenerator φ g W hW ↔ Z = W := by
  constructor
  · intro h
    have heq := congrArg (fun C : FiniteCorrespondenceGenerator (φ ≫ g) g =>
      Set.range C.projection) h
    simpa only [componentGraphGenerator_range] using heq
  · rintro rfl
    rfl

/-- The graph correspondence is the finite sum of its integral components. -/
noncomputable def componentGraphCycle : FiniteCorrespondence (φ ≫ g) g := by
  classical
  exact ∑ Z ∈ TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.toFinset,
    if hZ : Z ∈ irreducibleComponents X then (componentGraphGenerator φ g Z hZ).cycle else 0

/-- Every graph component occurs with multiplicity exactly one. -/
@[simp]
theorem componentGraphCycle_coefficient (Z : Set X) (hZ : Z ∈ irreducibleComponents X) :
    componentGraphCycle φ g (componentGraphGenerator φ g Z hZ) = 1 := by
  classical
  simp only [componentGraphCycle, Finsupp.coe_finsetSum, Finset.sum_apply]
  rw [Finset.sum_eq_single Z]
  · simp [hZ]
  · intro W hW hne
    have hW' : W ∈ irreducibleComponents X := by simpa using hW
    simp [hW', FiniteCorrespondenceGenerator.cycle, hne]
  · intro hnot
    exact (hnot (by simpa using hZ)).elim

end Reduced

/-- On an integral source each component graph agrees with the original graph generator. -/
@[simp]
theorem componentGraphGenerator_eq_graphGenerator [IsIntegral X]
    (Z : Set X) (hZ : Z ∈ irreducibleComponents X) :
    componentGraphGenerator φ g Z hZ = graphGenerator φ g := by
  apply Subtype.ext
  exact Scheme.Hom.ker_comp_of_isIso (X.irreducibleComponentι Z hZ)
    (_root_.AlgebraicGeometry.Scheme.Graph.correspondenceGraph φ g)

/-- The componentwise graph recovers the integral-source graph cycle. -/
@[simp]
theorem componentGraphCycle_eq_graphCycle [IsIntegral X] :
    componentGraphCycle φ g = graphCycle φ g := by
  classical
  simp [componentGraphCycle, irreducibleComponents_eq_singleton, graphCycle]

end Motivic
