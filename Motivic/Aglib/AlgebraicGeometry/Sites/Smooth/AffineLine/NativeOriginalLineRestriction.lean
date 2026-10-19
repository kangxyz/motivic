/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.AffineLine.NativeOriginalBase
/-! # Actual native line restriction and its original field compatibility

Intended upstream module:
`Aglib.AlgebraicGeometry.Sites.Smooth.AffineLine.NativeOriginalLineRestriction`.

The exact hypotheses are the section variables and declaration signatures below.
Current direct import consumers (unique module suffixes):
`AffineLine.NativeOriginalCylinder`.
-/

open _root_.AlgebraicGeometry.Scheme (SmoothSite)

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.PolynomialLaurent
universe u
namespace AlgebraicGeometry.Scheme.SmoothSite

private theorem fieldMap_of_isPullback
    {C : Type*} [Category C] {S U U' T T' : C}
    {m : T' ⟶ T} {q : T' ⟶ U'} {p : T ⟶ U} {l : U' ⟶ U}
    {tU : U ⟶ S} {tT : T ⟶ S} {tU' : U' ⟶ S}
    (H : IsPullback m q p l) (hp : p ≫ tU = tT) (hl : l ≫ tU = tU') :
    m ≫ tT = q ≫ tU' := by
  calc
    m ≫ tT = m ≫ (p ≫ tU) := congrArg (fun f => m ≫ f) hp.symm
    _ = (m ≫ p) ≫ tU := (Category.assoc _ _ _).symm
    _ = (q ≫ l) ≫ tU := congrArg (fun f => f ≫ tU) H.w
    _ = q ≫ tU' := (Category.assoc _ _ _).trans (congrArg (fun f => q ≫ f) hl)

variable {k : Type u} [Field k]
  (U T : SmoothSite (Spec (.of k))) [IsAffine U.left]
  (e : T ≅ a1Cylinder (.of k) U)
  (B : (Spec Γ(U.left, ⊤)).Opens) [IsAffine B.toScheme]
  (O : (Spec Γ(B.toScheme, ⊤)).Opens) [IsAffine O.toScheme]
  (V : (Spec Γ(O.toScheme, ⊤)).Opens) [IsAffine V.toScheme]

local notation "m" => nativeOriginalLineMap U T e B O V
local notation "q" => polynomialProjection
  (CommRingCat.of (V.toScheme.presheaf.obj (Opposite.op ⊤)))
local notation "l" => nativeOriginalCoefficientMap U B O V
local notation "t" => nativeOriginalFinalFieldMap U B O V

/-- The original cylinder map has precisely the retained native field structure. -/
theorem nativeOriginalLineMap_field : m ≫ T.hom = q ≫ t :=
  fieldMap_of_isPullback (nativeOriginalCoefficient_isPullback U T e B O V)
    (MorphismProperty.Over.w (e.hom ≫ a1Projection (.of k) U))
    (nativeOriginalCoefficientMap_field U B O V)

/-- The full native line maps to the actual original cylinder over k. -/
def nativeOriginalLineRestriction : nativeOriginalLineSite U B O V ⟶ T :=
  homMk m (nativeOriginalLineMap_field U T e B O V)

/-- The checked scheme square, with exactly its actual smooth-site arrows. -/
theorem nativeOriginalRestriction_isPullback :
    IsPullback (nativeOriginalLineRestriction U T e B O V).left
      (nativeOriginalLineProjection U B O V).left
      (e.hom ≫ a1Projection (.of k) U).left
      (nativeOriginalBaseInclusion U B O V).left := by
  change IsPullback m q (e.hom ≫ a1Projection (.of k) U).left l
  exact nativeOriginalCoefficient_isPullback U T e B O V

end AlgebraicGeometry.Scheme.SmoothSite
