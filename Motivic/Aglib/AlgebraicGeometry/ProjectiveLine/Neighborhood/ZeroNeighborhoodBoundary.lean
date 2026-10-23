/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.ZeroComplement
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.DisjointClosedImmersion
/-! # The entire relative projective boundary of a zero-section neighborhood

No monic defining polynomial, finite boundary, or flat boundary is assumed.
The finiteness proof also applies unchanged to arbitrary nonreduced closed
boundaries disjoint from the original zero section.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
universe u
namespace AlgebraicGeometry.RelativeProjectiveLine
variable (R : Type u) [CommRing R]

@[reassoc (attr := simp)]
lemma zeroSection_toSpec :
    zeroSection R ≫ ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)) = 𝟙 _ := by
  rw [zeroSection, Category.assoc, chart_toSpec, ← Spec.map_comp]
  have h : CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R) ≫
      CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)) = 𝟙 _ := by
    ext x
    simp
  rw [h, Spec.map_id]

instance zeroSection_isClosedImmersion : IsClosedImmersion (zeroSection R) := by
  have : IsClosedImmersion
      (zeroSection R ≫ ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) := by
    rw [zeroSection_toSpec]
    infer_instance
  exact IsClosedImmersion.of_comp _ (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))


/-- Every actual closed scheme disjoint from zero is finite over the base. -/
theorem isFinite_boundary_disjoint_zero {B : Scheme.{u}}
    (i : B ⟶ ProjectiveSpace R (ULift.{u} (Fin 2))) [IsClosedImmersion i]
    (h : Disjoint (Set.range i) (Set.range (zeroSection R))) :
    IsFinite (i ≫ ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) := by
  apply ProjectiveSpace.isFinite_boundary_in_coordinateOpen R _ i ⟨1⟩
  intro x hx
  by_contra hn
  exact Set.disjoint_left.mp h hx (by rw [range_zeroSection]; exact hn)

variable (V : (Spec (.of (Polynomial R))).Opens)

/-- The unchanged neighborhood, viewed as an open of the actual relative projective line. -/
def projectiveNeighborhood : (ProjectiveSpace R (ULift.{u} (Fin 2))).Opens :=
  chart R ⟨0⟩ ''ᵁ V

/-- The vanishing ideal of the whole missing neighborhood, including infinity. -/
def neighborhoodBoundaryIdeal :
    (ProjectiveSpace R (ULift.{u} (Fin 2))).IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal
    ⟨(projectiveNeighborhood R V : Set _)ᶜ,
      (projectiveNeighborhood R V).isOpen.isClosed_compl⟩

/-- The closed subscheme defined by the vanishing ideal of the missing projective neighborhood. -/
def neighborhoodBoundary : Scheme.{u} := (neighborhoodBoundaryIdeal R V).subscheme

/-- The closed subscheme inclusion of the missing neighborhood boundary into the projective line. -/
def neighborhoodBoundaryInclusion :
    neighborhoodBoundary R V ⟶ ProjectiveSpace R (ULift.{u} (Fin 2)) :=
  (neighborhoodBoundaryIdeal R V).subschemeι

instance : IsClosedImmersion (neighborhoodBoundaryInclusion R V) := by
  change IsClosedImmersion (neighborhoodBoundaryIdeal R V).subschemeι
  infer_instance

lemma range_neighborhoodBoundaryInclusion :
    Set.range (neighborhoodBoundaryInclusion R V) =
      (projectiveNeighborhood R V : Set _)ᶜ := by
  change Set.range (neighborhoodBoundaryIdeal R V).subschemeι = _
  rw [Scheme.IdealSheafData.range_subschemeι]
  simp [neighborhoodBoundaryIdeal]

/-- Finiteness of the entire boundary follows from containing the whole zero section. -/
theorem neighborhoodBoundary_finite
    (hV : Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) ⊆ V) :
    IsFinite (neighborhoodBoundaryInclusion R V ≫
      ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) := by
  apply isFinite_boundary_disjoint_zero
  apply Set.disjoint_left.mpr
  intro x hx hz
  rw [range_neighborhoodBoundaryInclusion] at hx
  obtain ⟨y, rfl⟩ := hz
  apply hx
  exact ⟨_, hV ⟨y, rfl⟩, rfl⟩
/-- The full prescribed boundary consists of the actual complement and original zero scheme. -/
def fullNeighborhoodBoundaryMap :
    neighborhoodBoundary R V ⨿ Spec (.of R) ⟶ ProjectiveSpace R (ULift.{u} (Fin 2)) :=
  coprod.desc (neighborhoodBoundaryInclusion R V) (zeroSection R)

lemma neighborhoodBoundary_disjoint_zero
    (hV : Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) ⊆ V) :
    Disjoint (Set.range (neighborhoodBoundaryInclusion R V)) (Set.range (zeroSection R)) := by
  apply Set.disjoint_left.mpr
  intro x hx hz
  rw [range_neighborhoodBoundaryInclusion] at hx
  obtain ⟨y, rfl⟩ := hz
  exact hx ⟨_, hV ⟨y, rfl⟩, rfl⟩

theorem fullNeighborhoodBoundary_closed
    (hV : Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) ⊆ V) :
    IsClosedImmersion (fullNeighborhoodBoundaryMap R V) :=
  isClosedImmersion_coprod_desc _ _ (neighborhoodBoundary_disjoint_zero R V hV)

theorem fullNeighborhoodBoundary_finite
    (hV : Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) ⊆ V) :
    IsFinite (fullNeighborhoodBoundaryMap R V ≫
      ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))) := by
  have := neighborhoodBoundary_finite R V hV
  rw [fullNeighborhoodBoundaryMap, coprod.desc_comp, zeroSection_toSpec]
  infer_instance

@[reassoc (attr := simp)]
lemma fullNeighborhoodBoundary_inl : coprod.inl ≫ fullNeighborhoodBoundaryMap R V =
    neighborhoodBoundaryInclusion R V := coprod.inl_desc _ _

@[reassoc (attr := simp)]
lemma fullNeighborhoodBoundary_inr : coprod.inr ≫ fullNeighborhoodBoundaryMap R V =
    zeroSection R := coprod.inr_desc _ _

end AlgebraicGeometry.RelativeProjectiveLine
