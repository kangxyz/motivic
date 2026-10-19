/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Cycles.FiniteSupport
public import Motivic.Aglib.AlgebraicGeometry.Cycles.IntegralImage

/-! # Consumers of finite point-cycle pushforward and actual integral images -/

@[expose] public section

open CategoryTheory AlgebraicGeometry  _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle

universe u

variable {X Y Z : Scheme.{u}}

example (f : X ⟶ Y) (g : Y ⟶ Z) [IsFinite f] [IsFinite g]
    (c : _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle X) :
    residuePushforward (f ≫ g) c = residuePushforward g (residuePushforward f c) := by
  rw [residuePushforward_comp]
  rfl

example (e : X ≅ Y) (c : _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle X) :
    (isoPushforward e).symm (isoPushforward e c) = c :=
  (isoPushforward e).symm_apply_apply c

example (f : X ⟶ Y) [IsFinite f] [IsIntegral X] : IsIntegral f.ker.subscheme :=
  _root_.AlgebraicGeometry.Scheme.Hom.isIntegral_finiteImage f

example (f : X ⟶ Y) [IsFinite f] [IsIntegral X] :
    letI := _root_.AlgebraicGeometry.Scheme.Hom.isIntegral_finiteImage f
    residuePushforward f (Finsupp.single (genericPoint X) 1) =
      Finsupp.single (f.imageι (genericPoint f.image)) (f.residueDegree (genericPoint X) : ℤ) := by
  let := _root_.AlgebraicGeometry.Scheme.Hom.isIntegral_finiteImage f
  rw [residuePushforward_single, one_mul, _root_.AlgebraicGeometry.Scheme.Hom.imageι_genericPoint]

example (f : X ⟶ Y) [IsFinite f] [IsIntegral X] :
    IsGenericPoint (f (genericPoint X)) (Set.range f) := by
  rw [← _root_.AlgebraicGeometry.Scheme.Hom.support_finiteImage f]
  exact _root_.AlgebraicGeometry.Scheme.Hom.isGenericPoint_finiteImage f

example (f : X ⟶ Y) [IsClosedImmersion f] (x : X) :
    f.residueDegree x = 1 := _root_.AlgebraicGeometry.Scheme.Hom.residueDegree_of_surjectiveOnStalks
        f x

example (f : X ⟶ Y) [IsFinite f] (x : X) :
    f.residueDegree x = f.toImage.residueDegree x := by
  have h := _root_.AlgebraicGeometry.Scheme.Hom.residueDegree_comp f.toImage f.imageι x
  simpa only [f.toImage_imageι,
      _root_.AlgebraicGeometry.Scheme.Hom.residueDegree_of_surjectiveOnStalks, one_mul] using h
