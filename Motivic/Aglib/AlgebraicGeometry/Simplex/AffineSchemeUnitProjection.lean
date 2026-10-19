/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Simplex.AffineSimplexUnitComplex
public import Mathlib.AlgebraicGeometry.Properties

/-! # Genuine affine-scheme unit invariance for relative simplices -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicSimplex

variable {k : Type u} [CommRing k] {X : Scheme.{u}} [IsAffine X] [IsReduced X]

omit [IsReduced X] in
/-- The actual map to an affine base in the canonical affine chart. -/
theorem isoSpec_inv_map (f : X ⟶ Spec (.of k)) :
    X.isoSpec.inv ≫ f = Spec.map ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) := by
  rw [← Scheme.isoSpec_inv_naturality, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]

/-- No chosen affine presentation is required: every reduced affine scheme has
invariant global units under the actual relative simplex projection. -/
theorem isIso_units_affineSchemeProjection (f : X ⟶ Spec (.of k)) (n : ℕ) :
    IsIso (_root_.AlgebraicGeometry.Scheme.ringUnits.map (pullback.snd (structureMap k n)
        f).appTop) := by
  let c : k →+* Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom
  let e := pullback.map (structureMap k n) (Spec.map (CommRingCat.ofHom c))
    (structureMap k n) f (𝟙 _) X.isoSpec.inv (𝟙 _)
      (by simp) (by simpa [c] using (isoSpec_inv_map f).symm)
  have he : IsIso e := by dsimp [e]; infer_instance
  have h : e ≫ pullback.snd (structureMap k n) f =
      pullback.snd (structureMap k n) (Spec.map (CommRingCat.ofHom c)) ≫ X.isoSpec.inv :=
    CategoryTheory.Limits.pullback.lift_snd _ _ _
  have hmap := congrArg (fun g => _root_.AlgebraicGeometry.Scheme.ringUnits.map g.appTop) h
  simp only [Scheme.Hom.comp_appTop, _root_.AlgebraicGeometry.Scheme.ringUnits.map_comp] at hmap
  have : IsIso (_root_.AlgebraicGeometry.Scheme.ringUnits.map (pullback.snd (structureMap k n)
      f).appTop ≫
      _root_.AlgebraicGeometry.Scheme.ringUnits.map e.appTop) := by
    rw [hmap]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (_root_.AlgebraicGeometry.Scheme.ringUnits.map e.appTop)

end AlgebraicSimplex
