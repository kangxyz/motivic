/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Cycles.Restriction.Open
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-!
# Whole point closures retained by an original open immersion

When the entire original closure lies in the retained open, its actual pullback
projection is an isomorphism. The canonical comparison preserves the literal
closed inclusions, so finiteness and dominance over the unchanged base transfer
without treating an arbitrary open part of a finite support as finite.


Intended upstream module: `Aglib.AlgebraicGeometry.Cycles.Restriction.RetainedPointClosure`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.Cycles.PrincipalDivisor.Faces.PrincipalFamilyWholeEndpoints`.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.IntegralClosedSubscheme

variable {C V S : Scheme.{u}} (j : V ⟶ C) [IsOpenImmersion j] (x : V)

/-- The native point closure on the open is the actual pulled-back ideal sheaf. -/
theorem retainedPointClosure_comap :
    (_root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme.pointClosure x).val =
        (_root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme.pointClosure (j x)).val.comap j :=
        by
  let i := ((_root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme.pointClosure (j
      x)).val.comapIso j).hom ≫
    pullback.snd j (_root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme.pointClosure (j
        x)).val.subschemeι
  have : IsOpenImmersion i := by dsimp only [i]; infer_instance
  have : IsReduced ((_root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme.pointClosure (j
      x)).val.comap j).subscheme :=
    isReduced_of_isOpenImmersion i
  apply _root_.AlgebraicGeometry.Scheme.IdealSheafData.idealSheaf_eq_of_support_eq
  apply SetLike.coe_injective
  simpa only [_root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme.support_pointClosure,
      Scheme.IdealSheafData.support_comap,
    TopologicalSpace.Closeds.coe_preimage, Set.image_singleton] using
    j.isOpenEmbedding.closure_eq_preimage_closure_image ({x} : Set V)

variable (h : Set.range (_root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme.pointClosure (j
    x)).val.subschemeι ⊆ Set.range j)

include h in
/-- Whole-support containment makes the actual open base-change projection an iso. -/
theorem retainedPointClosure_pullback_isIso :
    IsIso (pullback.snd j (_root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme.pointClosure (j
        x)).val.subschemeι) := by
  apply (isIso_iff_isOpenImmersion_and_surjective _).mpr
  refine ⟨inferInstance, ?_⟩
  apply (surjective_iff _).mpr
  intro z
  obtain ⟨y, hy⟩ := h ⟨z, rfl⟩
  obtain ⟨w, -, hw⟩ := Scheme.exists_preimage_of_isPullback
    (IsPullback.of_hasPullback j
        (_root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme.pointClosure (j x)).val.subschemeι)
        y z hy
  exact ⟨w, hw⟩

/-- The same whole support before and after restriction, with its canonical maps. -/
def retainedPointClosureIso :
    (_root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme.pointClosure x).val.subscheme ≅
        (_root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme.pointClosure (j x)).val.subscheme
        := by
  let : IsIso (pullback.snd j (_root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme.pointClosure
      (j x)).val.subschemeι) :=
    retainedPointClosure_pullback_isIso j x h
  let E : (_root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme.pointClosure x).val.subscheme ≅
      ((_root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme.pointClosure (j x)).val.comap
          j).subscheme :=
    { hom := Scheme.IdealSheafData.inclusion (retainedPointClosure_comap j x).ge
      inv := Scheme.IdealSheafData.inclusion (retainedPointClosure_comap j x).le
      hom_inv_id := by simp
      inv_hom_id := by simp }
  exact E ≪≫ (_root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme.pointClosure (j
      x)).val.comapIso j ≪≫
    asIso (pullback.snd j (_root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme.pointClosure (j
        x)).val.subschemeι)

/-- The support comparison respects the original closed immersion into C. -/
@[reassoc]
theorem retainedPointClosureIso_hom_inclusion :
    (retainedPointClosureIso j x h).hom ≫
        (_root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme.pointClosure (j x)).val.subschemeι
        =
      (_root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme.pointClosure x).val.subschemeι ≫ j :=
          by
  simp only [retainedPointClosureIso, Iso.trans_hom, asIso_hom, Category.assoc,
    ← pullback.condition, Scheme.IdealSheafData.comapIso_hom_fst_assoc,
    Scheme.IdealSheafData.inclusion_subschemeι_assoc]

include h in
/-- Both actual support properties transfer along the whole-support iso, over
exactly the same base map. No normality or flatness of a support is required. -/
theorem retainedPointClosure_finite_dominant (q : C ⟶ S)
    [IsFinite ((_root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme.pointClosure (j
        x)).val.subschemeι ≫ q)]
    [IsDominant ((_root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme.pointClosure (j
        x)).val.subschemeι ≫ q)] :
    IsFinite ((_root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme.pointClosure
        x).val.subschemeι ≫ j ≫ q) ∧
      IsDominant ((_root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme.pointClosure
          x).val.subschemeι ≫ j ≫ q) := by
  have he : (retainedPointClosureIso j x h).hom ≫
      ((_root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme.pointClosure (j x)).val.subschemeι ≫
          q) =
      (_root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme.pointClosure x).val.subschemeι ≫ j ≫
          q := by
    rw [← Category.assoc, retainedPointClosureIso_hom_inclusion, Category.assoc]
  rw [← he]
  exact ⟨inferInstance, inferInstance⟩

end AlgebraicGeometry.Scheme.IntegralClosedSubscheme
