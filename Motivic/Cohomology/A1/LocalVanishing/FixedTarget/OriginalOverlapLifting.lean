/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.LocalVanishing.FixedTarget.NormalizedLifting
public import Motivic.Cohomology.A1.LocalVanishing.Original.OverlapSectionLifting

/-! # Fixed-target lifting on the unchanged original overlap

The retained target and its auxiliary base restriction are used only to restrict
an original section. The resulting right-hand side is the original overlap
restriction, with the original signed difference and coefficient presheaf.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic ProjectiveSpace
open Scheme.Hom Scheme.EtaleCompactification

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

local instance {X Y : Scheme.{u}} (f : X ⟶ Y) [SmoothOfRelativeDimension 1 f] :
    Smooth f := SmoothOfRelativeDimension.smooth 1 f

variable (k : Type u) [Field k] (R : Type u) [CommRing R] [IsNoetherianRing R]
  (ι : Type u) [Finite ι] (X C : Scheme.{u}) [IsAffine X]
  [IsIntegral C] [IsLocallyNoetherian C]
  [∀ x : C, IsIntegrallyClosed (C.presheaf.stalk x)]
  {Y A : Scheme.{u}} [IsAffine Y] [IsAffine A]
  (t : Spec (.of R) ⟶ Spec (.of k)) [Smooth t]
  (q : X ⟶ Spec (.of R)) [IsSeparated q] [SmoothOfRelativeDimension 1 q]
  (p : Y ⟶ X) [Etale p] [QuasiCompact p] [IsSeparated p]
  (a : A ⟶ X) [IsOpenImmersion a]
  (j : X ⟶ C) [IsOpenImmersion j] [QuasiCompact j]
  (f : C ⟶ ProjectiveSpace R ι) [IsFinite f]
  (hq : j ≫ (f ≫ toSpec R ι) = q)
  (U : X.Opens) (V : (Spec (.of R)).Opens)
  [IsAffine V.toScheme] [IsAffine (boundaryBaseSourceOpen q U V).toScheme]

/-- The exact restriction to the original overlap of the fixed target square. -/
abbrev fixedTargetOverlapRestriction :=
  boundaryBaseOverlapRestriction k R ι t q p a
    (fixedTargetSourceProjectiveMap R ι X C p j f) (inclusion C (p ≫ j))
    (fixedTargetSource_over R ι X C p j f q hq) U V

omit [IsNoetherianRing R] [Finite ι] [IsLocallyNoetherian C]
  [IsSeparated q] [IsSeparated p] [IsFinite f] in
/-- The fixed-target pencil produces a signed lift of every original overlap section.
No sheafification, replacement coefficient object, or new-section surjectivity is used. -/
theorem fixedTarget_originalOverlap_hasRestrictionDifferenceLifting
    (P : PresheafWithTransfers.{u + 1} k)
    (hL : P.HasRestrictionDifferenceLifting
      (fixedTargetPencilGraph k R ι X C t q p a j f hq U V)
      (fixedTargetPencilBeta k R ι X C t q p a j f hq U V)
      (fixedTargetPencilAlpha k R ι X C t q p a j f hq U V)) :
    P.HasRestrictionDifferenceLifting
      (fixedTargetOverlapRestriction k R ι X C t q p a j f hq U V)
      (fixedTargetPencilBeta k R ι X C t q p a j f hq U V)
      (fixedTargetPencilAlpha k R ι X C t q p a j f hq U V) := by
  let : SmoothOfRelativeDimension 1 ((pullback.fst p a ≫ inclusion C (p ≫ j)) ≫
      (fixedTargetSourceProjectiveMap R ι X C p j f ≫ toSpec R ι)) :=
    fixedTargetRetained_smooth R ι X C p j f q hq a
  exact originalOverlap_hasRestrictionDifferenceLifting k R ι t q p a
    (fixedTargetSourceProjectiveMap R ι X C p j f) (inclusion C (p ≫ j))
    (fixedTargetSource_over R ι X C p j f q hq) U V P hL

end AlgebraicGeometry.Scheme.RelativeCurvePencil
