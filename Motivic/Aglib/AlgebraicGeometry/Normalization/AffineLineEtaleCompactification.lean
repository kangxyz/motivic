/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.Normalization.EtaleInfinityBoundary
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Coheight

/-! # Constructed finite compactification of an actual étale affine-line cover -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.AffineLineEtaleCompactification
variable (k : Type u) [Field k] {Y : Scheme.{u}}
  (p : Y ⟶ Spec (.of (Polynomial k))) [Etale p] [QuasiCompact p] [IsSeparated p]

/-- The original cover followed by the literal affine chart in the projective line. -/
abbrev projectiveMap := p ≫ ProjectiveLine.chart k ⟨0⟩

/-- The actual finite normalization; no compactification is an input. -/
abbrev compactification :=
  (EtaleCompactification.genericMap (ProjectiveSpace k (ULift.{u} (Fin 2)))
    (projectiveMap k p)).normalization

/-- The original source embeds in the constructed compactification. -/
abbrev inclusion : Y ⟶ compactification k p :=
  EtaleCompactification.inclusion _ (projectiveMap k p)

/-- The constructed finite map to the actual projective line. -/
abbrev toProjectiveLine : compactification k p ⟶ ProjectiveSpace k (ULift.{u} (Fin 2)) :=
  (EtaleCompactification.genericMap _ (projectiveMap k p)).fromNormalization

instance : IsOpenImmersion (inclusion k p) := inferInstanceAs
  (IsOpenImmersion (EtaleCompactification.inclusion _ (projectiveMap k p)))

instance : IsFinite (toProjectiveLine k p) := inferInstanceAs
  (IsFinite (EtaleCompactification.genericMap _ (projectiveMap k p)).fromNormalization)

/-- Literal map to the coefficient field. -/
abbrev projection : compactification k p ⟶ Spec (.of k) :=
  toProjectiveLine k p ≫ ProjectiveSpace.toSpec k (ULift.{u} (Fin 2))

instance : IsProper (projection k p) := by dsimp [projection]; infer_instance

omit [IsSeparated p] in
/-- Compactification does not change the original affine-line map. -/
@[reassoc (attr := simp)]
theorem inclusion_toProjectiveLine : inclusion k p ≫ toProjectiveLine k p =
    p ≫ ProjectiveLine.chart k ⟨0⟩ := EtaleCompactification.inclusion_over ..

omit [IsSeparated p] in
/-- Exact coefficient-field structural equation for the retained original source. -/
@[reassoc (attr := simp)]
theorem inclusion_projection : inclusion k p ≫ projection k p =
    p ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k)) := by
  rw [projection, ← Category.assoc, inclusion_toProjectiveLine,
    Category.assoc, ProjectiveLine.chart_toSpec]

/-- The full actual complement of the original open, not a chosen finite boundary. -/
abbrev infinity := EtaleCompactification.infinity _ (projectiveMap k p)

/-- Its original closed immersion into the compactification. -/
abbrev infinityInclusion : infinity k p ⟶ compactification k p :=
  EtaleCompactification.infinityInclusion _ (projectiveMap k p)

instance : IsClosedImmersion (infinityInclusion k p) := inferInstanceAs
  (IsClosedImmersion (EtaleCompactification.infinityInclusion _ (projectiveMap k p)))

/-- The whole infinity boundary is finite over the field, with all curve hypotheses proved. -/
instance finite_infinity : IsFinite (infinityInclusion k p ≫ projection k p) := by
  let : CompactSpace (ProjectiveSpace k (ULift.{u} (Fin 2))) :=
    QuasiCompact.compactSpace_of_compactSpace (ProjectiveSpace.toSpec k (ULift.{u} (Fin 2)))
  exact EtaleCompactification.finite_infinity_projection _ (projectiveMap k p)
    (ProjectiveLine.coheight_eq_one_of_ne_genericPoint k)
    (ProjectiveSpace.toSpec k (ULift.{u} (Fin 2)))

end AlgebraicGeometry.Scheme.AffineLineEtaleCompactification
