/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.Boundary.InfinityBoundary
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Charts.Normal
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Structure

/-! # Relative finite normalization of an actual étale affine-line cover

The original source and any whole lifted zero section are retained literally.
The missing boundary is proper over the coefficient ring, but is not asserted
finite: unlike the field case it can contain vertical positive-dimensional parts.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification
variable (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [IsNoetherianRing R] {Y : Scheme.{u}}
  (p : Y ⟶ Spec (.of (Polynomial R))) [Etale p] [QuasiCompact p] [IsSeparated p]

/-- The original cover followed by the literal affine chart in the projective line. -/
abbrev projectiveMap := p ≫ RelativeProjectiveLine.chart R ⟨0⟩

/-- The actual finite normalization; no compactification is an input. -/
abbrev compactification :=
  (EtaleCompactification.genericMap (ProjectiveSpace R (ULift.{u} (Fin 2)))
    (projectiveMap R p)).normalization

/-- The original source embeds in the constructed compactification. -/
abbrev inclusion : Y ⟶ compactification R p :=
  EtaleCompactification.inclusion _ (projectiveMap R p)

/-- The constructed finite map to the actual projective line. -/
abbrev toProjectiveLine : compactification R p ⟶ ProjectiveSpace R (ULift.{u} (Fin 2)) :=
  (EtaleCompactification.genericMap _ (projectiveMap R p)).fromNormalization

instance : IsOpenImmersion (inclusion R p) := inferInstanceAs
  (IsOpenImmersion (EtaleCompactification.inclusion _ (projectiveMap R p)))

instance : IsFinite (toProjectiveLine R p) := inferInstanceAs
  (IsFinite (EtaleCompactification.genericMap _ (projectiveMap R p)).fromNormalization)

/-- Literal map to the coefficient ring. -/
abbrev projection : compactification R p ⟶ Spec (.of R) :=
  toProjectiveLine R p ≫ ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))

instance : IsProper (projection R p) := by dsimp [projection]; infer_instance

omit [IsSeparated p] in
/-- Compactification does not change the original affine-line map. -/
@[reassoc]
theorem inclusion_toProjectiveLine : inclusion R p ≫ toProjectiveLine R p =
    p ≫ RelativeProjectiveLine.chart R ⟨0⟩ := EtaleCompactification.inclusion_over ..

omit [IsSeparated p] in
/-- Exact coefficient-ring structural equation for the retained original source. -/
@[reassoc]
theorem inclusion_projection : inclusion R p ≫ projection R p =
    p ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) := by
  rw [projection, ← Category.assoc, inclusion_toProjectiveLine,
    Category.assoc, RelativeProjectiveLine.chart_toSpec]

/-- The full actual complement of the original open, not a chosen finite boundary. -/
abbrev infinity := EtaleCompactification.infinity _ (projectiveMap R p)

/-- Its original closed immersion into the compactification. -/
abbrev infinityInclusion : infinity R p ⟶ compactification R p :=
  EtaleCompactification.infinityInclusion _ (projectiveMap R p)

instance : IsClosedImmersion (infinityInclusion R p) := inferInstanceAs
  (IsClosedImmersion (EtaleCompactification.infinityInclusion _ (projectiveMap R p)))

/-- The actual full missing boundary is proper over the original base. -/
instance proper_infinity : IsProper (infinityInclusion R p ≫ projection R p) := by
  infer_instance

variable (z : Spec (.of R) ⟶ Y)
  (hz : z ≫ p = Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R))))

/-- The whole original lifted zero, with no open shrinking of its source. -/
abbrev liftedZero : Spec (.of R) ⟶ compactification R p := z ≫ inclusion R p

include hz in
omit [IsSeparated p] in
/-- Its map to the literal projective line remains the original zero section. -/
@[reassoc]
theorem liftedZero_toProjectiveLine :
    liftedZero R p z ≫ toProjectiveLine R p =
      Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R))) ≫
        RelativeProjectiveLine.chart R ⟨0⟩ := by
  rw [liftedZero, Category.assoc, inclusion_toProjectiveLine, ← Category.assoc, hz]

omit [IsSeparated p] in
/-- Every point of the original whole lifted zero remains in the original open. -/
theorem liftedZero_mem_inclusion (s : Spec (.of R)) :
    liftedZero R p z s ∈ Set.range (inclusion R p) := ⟨z s, rfl⟩

/-- The retained zero is disjoint from the full missing boundary. -/
theorem liftedZero_not_mem_infinity (s : Spec (.of R)) :
    liftedZero R p z s ∉ Set.range (infinityInclusion R p) := by
  rw [EtaleCompactification.range_infinityInclusion]
  exact not_not_intro (liftedZero_mem_inclusion R p z s)

end AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification
