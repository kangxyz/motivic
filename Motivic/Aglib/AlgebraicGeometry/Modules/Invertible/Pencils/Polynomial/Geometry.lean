/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Pencils.PolynomialBoundaryPencil
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Constant.CurveSourceChange
/-! # Actual Cartesian geometry of the literal polynomial pencil -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.Modules.Invertible.PolynomialBoundaryPencil
variable {R : Type u} [CommRing R] {X D : Scheme.{u}} (b : X ⟶ Spec (.of R)) (f : D ⟶ X)

/-- The literal polynomial parameter change is the actual base change of f. -/
theorem parameterMap_isPullback :
    IsPullback (parameterMap b f) (projection (f ≫ b)) (projection b) f := by
  have he : parameterMap b f = Scheme.constantSourceMap f b
      (Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))) := by
    apply pullback.hom_ext <;> simp [parameterMap, projection]
  rw [he]
  exact Scheme.constantSourceMap_isPullback f b _

/-- The range on the actual polynomial line is the whole inverse image of the original range. -/
theorem range_parameterMap :
    Set.range (parameterMap b f) = (projection b) ⁻¹' Set.range f := by
  have H := parameterMap_isPullback b f
  rw [← Scheme.Pullback.range_fst (projection b) f]
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨H.isoPullback.hom y, ?_⟩
    change (H.isoPullback.hom ≫ pullback.fst (projection b) f) y = _
    rw [H.isoPullback_hom_fst]
  · rintro ⟨y, rfl⟩
    refine ⟨H.isoPullback.inv y, ?_⟩
    change (H.isoPullback.inv ≫ parameterMap b f) y = _
    rw [H.isoPullback_inv_fst]

instance [IsProper f] : IsProper (parameterMap b f) :=
  MorphismProperty.of_isPullback (parameterMap_isPullback b f).flip inferInstance
instance [IsOpenImmersion f] : IsOpenImmersion (parameterMap b f) :=
  MorphismProperty.of_isPullback (parameterMap_isPullback b f).flip inferInstance
instance [SmoothOfRelativeDimension 1 f] : SmoothOfRelativeDimension 1 (parameterMap b f) :=
  MorphismProperty.of_isPullback (parameterMap_isPullback b f).flip inferInstance

/-- The polynomial parameter space is affine over the original source. -/
instance : IsAffineHom (projection b) := by
  change IsAffineHom (pullback.fst b
    (Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))))
  exact MorphismProperty.pullback_fst _ _ inferInstance
instance [IsAffine X] : IsAffine (parameterSpace b) :=
  isAffine_of_isAffineHom (projection b)

/-- Quasi-affineness is retained on the smooth open, without smooth compactification. -/
theorem parameterSpace_quasiAffine [X.IsQuasiAffine] : (parameterSpace b).IsQuasiAffine :=
  Scheme.IsQuasiAffine.of_isAffineHom (projection b)

/-- The original boundary cover pulls back to the entire literal polynomial family. -/
theorem parameter_cover {B U : Scheme.{u}} (i : B ⟶ X) (j : U ⟶ X)
    (h : ∀ x : X, x ∈ Set.range j ∨ x ∈ Set.range i) :
    ∀ x : parameterSpace b,
      x ∈ Set.range (parameterMap b j) ∨ x ∈ Set.range (parameterMap b i) := by
  intro x
  simpa only [range_parameterMap, Set.mem_preimage] using h (projection b x)
end AlgebraicGeometry.Scheme.Modules.Invertible.PolynomialBoundaryPencil
