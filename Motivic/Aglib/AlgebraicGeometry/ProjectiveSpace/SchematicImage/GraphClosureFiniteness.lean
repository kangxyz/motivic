/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.Morphisms.Proper.GraphClosure
/-! # Empty actual graph boundary implies finiteness of the original coordinate map

This uses the scheme-theoretic graph closure and the original coordinate map. It does
not choose a projection, replace the source by its reduction, or assume finiteness.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
universe u
namespace AlgebraicGeometry.Scheme.GraphClosure
variable {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (U : X.Opens)
  (h : U.toScheme ⟶ Y) (w : U.ι ≫ f = h ≫ g)

/-- Separatedness of the coordinate target already recovers the entire original graph
on its affine-domain chart; properness of the coordinate target is not required. -/
theorem fromOpenToPreimage_isIso_of_separated [IsSeparated g] [QuasiCompact U.ι] :
    IsIso (fromOpenToPreimage f g U h w) := by
  let a := fromOpenToPreimage f g U h w
  let b := (toSource f g U h w) ∣_ U
  have : IsSeparated b := by
    dsimp [b, toSource]
    infer_instance
  have : IsProper (a ≫ b) := by
    rw [fromOpenToPreimage_restrict]
    infer_instance
  have : IsProper a := IsProper.of_comp a b
  have : Surjective a := surjective_of_isDominant_of_isClosed_range a
    a.isClosedMap.isClosed_range
  exact (isIso_iff_isOpenImmersion_and_surjective a).mpr ⟨inferInstance, inferInstance⟩

/-- If the actual scheme-theoretic graph closure has no points at infinity, the original
map into that closure is itself an isomorphism, including all nilpotents. -/
theorem fromOpen_isIso_of_no_infinity [IsSeparated g] [QuasiCompact U.ι]
    (hno : ∀ c : closure f g U h w, toSource f g U h w c ∈ U) :
    IsIso (fromOpen f g U h w) := by
  have := fromOpenToPreimage_isIso_of_separated f g U h w
  have htop : (toSource f g U h w) ⁻¹ᵁ U = ⊤ := by
    ext c
    exact iff_true_intro (hno c)
  have : IsIso (((toSource f g U h w) ⁻¹ᵁ U).ι) := by
    rw [htop]
    exact (closure f g U h w).topIso.isIso_hom
  rw [← fromOpenToPreimage_ι f g U h w]
  infer_instance

/-- Proper compact ambient plus absence of the actual graph infinity makes the
original coordinate map proper. No second projection is introduced. -/
theorem isProper_of_no_graph_infinity [IsProper f] [IsSeparated g] [QuasiCompact U.ι]
    (hno : ∀ c : closure f g U h w, toSource f g U h w c ∈ U) : IsProper h := by
  have := fromOpen_isIso_of_no_infinity f g U h w hno
  rw [← fromOpen_toTarget f g U h w]
  infer_instance

/-- The affine coordinate map is finite, not merely quasi-finite on a selected fibre. -/
theorem isFinite_of_no_graph_infinity [IsProper f] [IsSeparated g] [QuasiCompact U.ι]
    [IsAffineHom h]
    (hno : ∀ c : closure f g U h w, toSource f g U h w c ∈ U) : IsFinite h := by
  have := isProper_of_no_graph_infinity f g U h w hno
  exact (IsFinite.iff_isProper_and_isAffineHom (f := h)).mpr ⟨inferInstance, inferInstance⟩

/-- A scheme-theoretically empty full graph boundary supplies the no-infinity condition.
The chosen boundary may be nonreduced or disconnected. -/
theorem isFinite_of_empty_graph_boundary [IsProper f] [IsSeparated g] [QuasiCompact U.ι]
    [IsAffineHom h] {D : Scheme.{u}} (d : D ⟶ X)
    (hcover : ∀ x : X, x ∈ U ∨ x ∈ Set.range d)
    [IsEmpty (pullback (toSource f g U h w) d : Scheme.{u})] : IsFinite h := by
  apply isFinite_of_no_graph_infinity f g U h w
  intro c
  rcases hcover (toSource f g U h w c) with hc | ⟨b, hb⟩
  · exact hc
  · obtain ⟨z, _, _⟩ := Scheme.exists_preimage_of_isPullback
      (IsPullback.of_hasPullback (toSource f g U h w) d) c b hb.symm
    exact isEmptyElim z
end AlgebraicGeometry.Scheme.GraphClosure
