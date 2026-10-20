/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.BaseChange.Cartesian
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# The projective coordinate map on an actual native fiber

For a commutative ring `R : Type u`, schemes `C S : Scheme.{u}`, the actual
maps `q : C ⟶ S` and `F : C ⟶ ProjectiveSpace R (ULift (Fin 2))`, a specified
isomorphism `e : S ≅ Spec R`, and `F ≫ toSpec = q ≫ e.hom`, the coordinate
map is constructed on the literal native fiber `q.fiber s`. Its coefficient
field is `S.residueField s`, using the actual ring hom recovered from
`S.fromSpecResidueField s ≫ e.hom` by `Spec.preimage`.

The two original structural maps give a Cartesian square. Separate instances
transport finiteness and flatness of `F` to the native fiber map. No nonempty,
connected, reduced, smooth, or positive-rank premise is imposed. No component
or dimension assertion is part of this independent map construction.

Intended upstream module: `Aglib.AlgebraicGeometry.ProjectiveLine.Fiber`.
Current consumer: the first/final coefficient-fiber component-dimension
adapter, via `ProjectiveLine.Dimension.FiberComponents`
and `Normalization.Compactification.RelativeAffineLine.CoefficientFiberDimension`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.RelativeProjectiveLine

universe u

variable (R : Type u) [CommRing R] {C S : Scheme.{u}}
  (q : C ⟶ S) (F : C ⟶ ProjectiveSpace R (ULift.{u} (Fin 2)))
  (e : S ≅ Spec (.of R))
  (hF : F ≫ ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)) = q ≫ e.hom)
  (s : S)

/-- The projective coefficient square for the actual native residue-field arrow. -/
theorem residueProjectiveSquare :
    IsPullback
      (ProjectiveSpace.map
        (Spec.preimage (S.fromSpecResidueField s ≫ e.hom)).hom (ULift.{u} (Fin 2)))
      (ProjectiveSpace.toSpec (S.residueField s) (ULift.{u} (Fin 2)))
      (ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))
      (S.fromSpecResidueField s ≫ e.hom) := by
  simpa only [CommRingCat.ofHom_hom, Spec.map_preimage] using
    ProjectiveSpace.isPullback_map
      (Spec.preimage (S.fromSpecResidueField s ≫ e.hom)).hom (ULift.{u} (Fin 2))

include hF in
/-- The native fiber square transported through the specified affine-base isomorphism. -/
theorem fiberProjectionSquare :
    IsPullback (q.fiberι s) (q.fiberToSpecResidueField s)
      (F ≫ ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))
      (S.fromSpecResidueField s ≫ e.hom) := by
  refine (IsPullback.of_hasPullback q (S.fromSpecResidueField s)).of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _) e
    (by
      change pullback.fst q (S.fromSpecResidueField s) ≫ 𝟙 C =
        𝟙 (pullback q (S.fromSpecResidueField s)) ≫
          pullback.fst q (S.fromSpecResidueField s)
      simp only [Category.comp_id, Category.id_comp])
    (by
      change pullback.snd q (S.fromSpecResidueField s) ≫ 𝟙 (Spec (S.residueField s)) =
        𝟙 (pullback q (S.fromSpecResidueField s)) ≫
          pullback.snd q (S.fromSpecResidueField s)
      simp only [Category.comp_id, Category.id_comp]) ?_ (by simp)
  simpa only [Iso.refl_hom, Category.id_comp] using hF.symm

/-- The canonical projective coordinate map on the literal native fiber. -/
def nativeFiberToProjectiveLine :
    q.fiber s ⟶ ProjectiveSpace (S.residueField s) (ULift.{u} (Fin 2)) :=
  (residueProjectiveSquare R e s).lift (q.fiberι s ≫ F)
    (q.fiberToSpecResidueField s)
    (by rw [Category.assoc, (fiberProjectionSquare R q F e hF s).w])

@[reassoc (attr := simp)]
theorem nativeFiberToProjectiveLine_map :
    nativeFiberToProjectiveLine R q F e hF s ≫
      ProjectiveSpace.map
        (Spec.preimage (S.fromSpecResidueField s ≫ e.hom)).hom (ULift.{u} (Fin 2)) =
      q.fiberι s ≫ F :=
  (residueProjectiveSquare R e s).lift_fst _ _ _

@[reassoc (attr := simp)]
theorem nativeFiberToProjectiveLine_toSpec :
    nativeFiberToProjectiveLine R q F e hF s ≫
      ProjectiveSpace.toSpec (S.residueField s) (ULift.{u} (Fin 2)) =
      q.fiberToSpecResidueField s :=
  (residueProjectiveSquare R e s).lift_snd _ _ _

/-- The coordinate map on the native fiber is the actual base change of `F`. -/
theorem nativeFiberToProjectiveLine_isPullback :
    IsPullback (q.fiberι s) (nativeFiberToProjectiveLine R q F e hF s) F
      (ProjectiveSpace.map
        (Spec.preimage (S.fromSpecResidueField s ≫ e.hom)).hom (ULift.{u} (Fin 2))) :=
  (fiberProjectionSquare R q F e hF s).of_bot' (residueProjectiveSquare R e s)

instance nativeFiberToProjectiveLine_finite [IsFinite F] :
    IsFinite (nativeFiberToProjectiveLine R q F e hF s) :=
  MorphismProperty.of_isPullback (P := (@IsFinite : MorphismProperty Scheme.{u}))
    (nativeFiberToProjectiveLine_isPullback R q F e hF s) inferInstance

instance nativeFiberToProjectiveLine_flat [Flat F] :
    Flat (nativeFiberToProjectiveLine R q F e hF s) :=
  MorphismProperty.of_isPullback (P := (@Flat : MorphismProperty Scheme.{u}))
    (nativeFiberToProjectiveLine_isPullback R q F e hF s) inferInstance

end AlgebraicGeometry.RelativeProjectiveLine
