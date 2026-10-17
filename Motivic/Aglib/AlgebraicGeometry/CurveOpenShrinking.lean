/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Topology.KrullDimension.ClosedSubspace
public import Mathlib.AlgebraicGeometry.Artinian
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Shrinking a curve without losing a specified closed complement

On a Noetherian curve, an open containing every component generic point misses
only finitely many closed points. Inside an open of a Jacobson scheme, these
points remain closed in the ambient scheme. Removing precisely those points
shrinks the overlap while retaining the complete original closed complement.
No perfectness or separability hypothesis on closed residue fields is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- The entire complement of an open containing every component generic point
in a Noetherian scheme of dimension at most one is finite and consists of
closed points. The scheme may be empty or disconnected. -/
theorem finite_closed_complement_of_genericPoints_subset
    {X : Scheme.{u}} [IsNoetherian X] (O : X.Opens)
    (hgeneric : genericPoints X ⊆ (O : Set X))
    (hdim : topologicalKrullDim X ≤ 1) :
    ((O : Set X)ᶜ).Finite ∧ ∀ x : X, x ∉ O → IsClosed ({x} : Set X) := by
  let Z : Closeds X := ⟨(O : Set X)ᶜ, O.isOpen.isClosed_compl⟩
  let I := IdealSheafData.vanishingIdeal Z
  have hzero : topologicalKrullDim Z ≤ 0 := by
    exact topologicalKrullDim_closed_le_of_avoids_genericPoints
      (Z : Set X) Z.isClosed
      (Set.disjoint_left.mpr (fun _ hx hg => hx (hgeneric hg))) 0
      (by simpa using hdim)
  have hdimI : topologicalKrullDim I.subscheme ≤ 0 := by
    change topologicalKrullDim ↥(I.support : Set X) ≤ 0
    dsimp only [I]
    rw [IdealSheafData.coe_support_vanishingIdeal]
    exact hzero
  let : IsLocallyNoetherian I.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian I.subschemeι
  let : NoetherianSpace I.subscheme :=
    I.subschemeι.isClosedEmbedding.isEmbedding.isInducing.noetherianSpace
  let : IsLocallyArtinian I.subscheme := .of_topologicalKrullDim_le_zero hdimI
  let : Finite I.subscheme := NoetherianSpace.finite
  have hrange : Set.range I.subschemeι = (O : Set X)ᶜ := by
    rw [IdealSheafData.range_subschemeι]
    simp [I, Z]
  refine ⟨hrange ▸ Set.finite_range I.subschemeι, ?_⟩
  intro x hx
  have hxrange : x ∈ Set.range I.subschemeι := by
    rw [hrange]
    exact hx
  obtain ⟨z, rfl⟩ := hxrange
  simpa only [Set.image_singleton] using
    I.subschemeι.isClosedEmbedding.isClosedMap ({z} : Set I.subscheme) isClosed_singleton

/-- A dense-on-every-component open inside an open curve can be realized as
its intersection with an ambient open retaining the entire old complement.
The finiteness and closedness of the removed set are conclusions. -/
theorem exists_open_shrinking_retaining_complement
    {V : Scheme.{u}} [IsNoetherian V] [JacobsonSpace V]
    (W : V.Opens) (O : W.toScheme.Opens)
    (hgeneric : genericPoints W.toScheme ⊆ (O : Set W.toScheme))
    (hdim : topologicalKrullDim W.toScheme ≤ 1) :
    ∃ T : V.Opens, (W : Set V)ᶜ ⊆ (T : Set V) ∧
      W.ι ⁻¹ᵁ T = O ∧ ((T : Set V)ᶜ).Finite := by
  let : IsLocallyNoetherian W.toScheme := LocallyOfFiniteType.isLocallyNoetherian W.ι
  let : NoetherianSpace W.toScheme :=
    W.ι.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
  let : IsNoetherian W.toScheme := ⟨⟩
  obtain ⟨hfinite, hclosed⟩ :=
    finite_closed_complement_of_genericPoints_subset O hgeneric hdim
  let E : Set V := W.ι '' (O : Set W.toScheme)ᶜ
  have hEfinite : E.Finite := hfinite.image W.ι
  have hEclosed : IsClosed E := by
    rw [show E = ⋃ x ∈ E, ({x} : Set V) by simp]
    apply hEfinite.isClosed_biUnion
    rintro x ⟨y, hy, rfl⟩
    exact W.ι.closePoints_subset_preimage_closedPoints (hclosed y hy)
  let T : V.Opens := ⟨Eᶜ, hEclosed.isOpen_compl⟩
  refine ⟨T, ?_, ?_, ?_⟩
  · rintro x hx ⟨y, _, rfl⟩
    exact hx y.property
  · ext x
    change W.ι x ∉ E ↔ x ∈ O
    simp only [E, Set.mem_image, Set.mem_compl_iff]
    constructor
    · intro hx
      by_contra hn
      exact hx ⟨x, hn, rfl⟩
    · rintro hx ⟨y, hy, he⟩
      exact hy (W.ι.isOpenEmbedding.injective he ▸ hx)
  · simpa only [T, Opens.coe_mk, compl_compl] using hEfinite

end AlgebraicGeometry.Scheme
