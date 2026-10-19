/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.Boundary.InfinityBoundary
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.DisjointClosedImmersion
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Frames.DisjointBoundary.Restriction

/-! # The actual disjoint infinity and finite-scheme boundary -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.EtaleCompactification
variable (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
  [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)]
  {Y : Scheme.{u}} (f : Y ⟶ X) [Etale f] [QuasiCompact f] [IsSeparated f]
  {Z : Scheme.{u}} (s : Z ⟶ Y)

/-- The original Z scheme and the full infinity complement are disjoint. -/
theorem infinity_disjoint_original :
    Disjoint (Set.range (infinityInclusion X f)) (Set.range (s ≫ inclusion X f)) := by
  rw [range_infinityInclusion]
  apply Set.disjoint_left.mpr
  rintro x hx ⟨z, rfl⟩
  exact hx ⟨s z, rfl⟩

/-- No reduction or replacement of the prescribed finite boundary Z is made. -/
def boundaryInclusion : infinity X f ⨿ Z ⟶ (genericMap X f).normalization :=
  coprod.desc (infinityInclusion X f) (s ≫ inclusion X f)

@[reassoc (attr := simp)]
theorem inl_boundaryInclusion : coprod.inl ≫ boundaryInclusion X f s =
    infinityInclusion X f := coprod.inl_desc _ _

@[reassoc (attr := simp)]
theorem inr_boundaryInclusion : coprod.inr ≫ boundaryInclusion X f s =
    s ≫ inclusion X f := coprod.inr_desc _ _

/-- Properness of the original Z over the base supplies closedness in the compactification. -/
theorem originalBoundary_isClosedImmersion [IsClosedImmersion s]
    {S : Scheme.{u}} (p : X ⟶ S) [IsSeparated p] [IsProper (s ≫ f ≫ p)] :
    IsClosedImmersion (s ≫ inclusion X f) := by
  let q := (genericMap X f).fromNormalization ≫ p
  have : IsProper ((s ≫ inclusion X f) ≫ q) := by
    simpa [q, Category.assoc] using (inferInstance : IsProper (s ≫ f ≫ p))
  have : IsProper (s ≫ inclusion X f) := IsProper.of_comp _ q
  exact IsClosedImmersion.of_isPreimmersion _
    (s ≫ inclusion X f).isClosedMap.isClosed_range

/-- The actual full boundary is a closed immersion, with its original Z scheme structure. -/
theorem boundaryInclusion_isClosedImmersion [IsClosedImmersion s]
    {S : Scheme.{u}} (p : X ⟶ S) [IsSeparated p] [IsProper (s ≫ f ≫ p)] :
    IsClosedImmersion (boundaryInclusion X f s) := by
  let := originalBoundary_isClosedImmersion X f s p
  exact isClosedImmersion_coprod_desc _ _ (infinity_disjoint_original X f s)

end AlgebraicGeometry.Scheme.EtaleCompactification
