/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Refinement
public import Mathlib.CategoryTheory.Sites.CoverLifting

/-!
# Ordinary Nisnevich sheafification and restriction to smooth schemes

Over an affine base, ordinary sheafification commutes with restriction from
the big over-site to the smooth site. This is Mathlib's canonical comparison
for a continuous and cocontinuous functor, with its actual unit formula.
Sheafification and pointwise right Kan extension hypotheses remain explicit,
including the universe-dependent size requirements they encode.

These are ordinary sheaves; this comparison does not equip sheafification
with transfers.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u v w

namespace AlgebraicGeometry.Scheme.SmoothSite

variable (S : Scheme.{u}) [IsAffine S] (A : Type w) [Category.{v} A]
variable [HasWeakSheafify (nisnevichTopology S) A]
variable [HasWeakSheafify (Nisnevich.topology.over S) A]
variable [∀ F : (SmoothSite S)ᵒᵖ ⥤ A, (forget S).op.HasPointwiseRightKanExtension F]

/-- The canonical ordinary sheafification comparison under smooth-site restriction. -/
def restrictNisnevichSheafificationIso :
    (Functor.whiskeringLeft _ _ A).obj (forget S).op ⋙
      presheafToSheaf (nisnevichTopology S) A ≅
    presheafToSheaf (Nisnevich.topology.over S) A ⋙ restrictNisnevichSheaf S A :=
  (forget S).pushforwardContinuousSheafificationCompatibility A _ _

/-- The comparison carries the small sheafification unit to the restricted big unit. -/
@[reassoc]
theorem toSheafify_restrictNisnevichSheafificationIso (P : (Over S)ᵒᵖ ⥤ A) :
    toSheafify (nisnevichTopology S) ((forget S).op ⋙ P) ≫
      ((restrictNisnevichSheafificationIso S A).hom.app P).hom =
        Functor.whiskerLeft (forget S).op (toSheafify (Nisnevich.topology.over S) P) :=
  (forget S).toSheafify_pullbackSheafificationCompatibility A _ _ P

end AlgebraicGeometry.Scheme.SmoothSite
