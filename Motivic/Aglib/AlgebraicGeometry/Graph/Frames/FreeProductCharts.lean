/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Flat.FreeCartesian
public import Motivic.Aglib.AlgebraicGeometry.Graph.Frames.OriginalTriangle

/-!
# Free affine neighborhoods for the original graph-product map

The Cartesian square is derived from the literal graph-product definition.
The original free target charts then supply canonical affine neighborhoods on
the unchanged parameter product, without an assumed comparison square.


Intended upstream module: `Aglib.AlgebraicGeometry.Graph.Frames.FreeProductCharts`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.GraphFreeCover`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.FiniteSchemeNormBaseChange

universe u
namespace AlgebraicGeometry.Scheme.Hom

variable {S C X T : Scheme.{u}} (q : X ⟶ S) (f : C ⟶ X) (j : T ⟶ C)

/-- The original graph-product map is the actual base change of the finite map. -/
theorem graphProductMap_isPullback :
    IsPullback (pullback.snd (j ≫ f ≫ q) (f ≫ q)) (graphProductMap q f j)
      f (pullback.snd (j ≫ f ≫ q) q) := by
  apply IsPullback.flip
  apply IsPullback.of_iso_pullback ⟨(graphProductMap_snd q f j)⟩
    (pullbackLeftPullbackSndIso (j ≫ f ≫ q) q f).symm
  · rfl
  · simp

/-- Original free affine charts of the compactification produce the canonical
local coordinate-freeness input for its original graph-product map. -/
theorem graphProductMap_exists_free_affine_neighborhood [IsFinite f]
    {ι : Type u} (A : ι → CommRingCat.{u}) (w : ∀ i, Spec (A i) ⟶ X)
    [∀ i, IsOpenImmersion (w i)]
    (hcover : ∀ x : X, ∃ i, x ∈ Set.range (w i))
    (hfree : ∀ i,
      let : Algebra (A i) Γ(Limits.pullback f (w i), ⊤) :=
        (scalarMap (pullback.snd f (w i))).toAlgebra
      Module.Free (A i) Γ(Limits.pullback f (w i), ⊤))
    (x : (Limits.pullback (j ≫ f ≫ q) q : Scheme.{u})) :
    ∃ (U : (Limits.pullback (j ≫ f ≫ q) q).Opens) (hU : IsAffineOpen U), x ∈ U ∧
      (let : Algebra Γ(Limits.pullback (j ≫ f ≫ q) q, U)
          Γ(Limits.pullback (graphProductMap q f j) hU.fromSpec, ⊤) :=
        (scalarMap (pullback.snd (graphProductMap q f j) hU.fromSpec)).toAlgebra
       Module.Free Γ(Limits.pullback (j ≫ f ≫ q) q, U)
         Γ(Limits.pullback (graphProductMap q f j) hU.fromSpec, ⊤)) :=
  exists_free_affine_neighborhood_of_isPullback f (graphProductMap q f j)
    (pullback.snd (j ≫ f ≫ q) (f ≫ q)) (pullback.snd (j ≫ f ≫ q) q)
    (graphProductMap_isPullback q f j) A w hcover hfree x

end AlgebraicGeometry.Scheme.Hom
