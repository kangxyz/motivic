/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Flat.FreeCartesian
/-! # Original free Cartesian charts inside a prescribed open

Refine the inherited free chart within the prescribed open, then transport
freeness through the actual affine Cartesian square. No new freeness premise
is imposed on the refined chart.

Intended upstream module:
`Aglib.AlgebraicGeometry.Morphisms.Finite.Flat.FreeCartesianOpen`.

The exact hypotheses are the section variables and declaration signatures below.
Current direct import consumers (unique module suffixes):
`FunctionalProduct.Unit`, `Norm.OriginalRetainedNormMaps`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.FiniteSchemeNormBaseChange

/-- The original free affine charts yield free neighborhoods inside any given open. -/
theorem exists_free_affine_neighborhood_subset_of_isPullback
    {C T C' T' : Scheme.{u}} (f : C ⟶ T) [IsFinite f]
    (p : C' ⟶ T') (v : C' ⟶ C) (b : T' ⟶ T) (H : IsPullback v p f b)
    {ι : Type u} (A : ι → CommRingCat.{u}) (w : ∀ i, Spec (A i) ⟶ T)
    [∀ i, IsOpenImmersion (w i)]
    (hcover : ∀ t : T, ∃ i, t ∈ Set.range (w i))
    (hfree : ∀ i,
      let : Algebra (A i) Γ(pullback f (w i), ⊤) :=
        (scalarMap (pullback.snd f (w i))).toAlgebra
      Module.Free (A i) Γ(pullback f (w i), ⊤))
    (V : T'.Opens) (x : T') (hx : x ∈ V) :
    ∃ (U : T'.Opens) (hU : IsAffineOpen U), x ∈ U ∧ U ≤ V ∧
      (let : Algebra Γ(T', U) Γ(pullback p hU.fromSpec, ⊤) :=
        (scalarMap (pullback.snd p hU.fromSpec)).toAlgebra
       Module.Free Γ(T', U) Γ(pullback p hU.fromSpec, ⊤)) := by
  obtain ⟨W, hW, hxW, hfW⟩ :=
    exists_free_affine_neighborhood_of_isPullback f p v b H A w hcover hfree x
  obtain ⟨U, hU, hxU, hUW⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ W ⊓ V from ⟨hxW, hx⟩)
  have hfac : Set.range hU.fromSpec ⊆ Set.range hW.fromSpec := by
    rw [hU.range_fromSpec, hW.range_fromSpec]
    exact fun y hy => (hUW hy).1
  let a := IsOpenImmersion.lift hW.fromSpec hU.fromSpec hfac
  have ha : a ≫ hW.fromSpec = hU.fromSpec :=
    IsOpenImmersion.lift_fac hW.fromSpec hU.fromSpec hfac
  have Hlarge : IsPullback (pullback.fst p hU.fromSpec)
      (pullback.snd p hU.fromSpec) p (a ≫ hW.fromSpec) := by
    simpa only [ha] using IsPullback.of_hasPullback p hU.fromSpec
  have Hsmall := Hlarge.of_right' (IsPullback.of_hasPullback p hW.fromSpec)
  let : IsFinite p := MorphismProperty.of_isPullback H inferInstance
  let : IsAffine (pullback p hW.fromSpec) :=
    isAffine_of_isAffineHom (pullback.snd p hW.fromSpec)
  let : Algebra Γ(T', W) Γ(pullback p hW.fromSpec, ⊤) :=
    (scalarMap (pullback.snd p hW.fromSpec)).toAlgebra
  let : Module.Free Γ(T', W) Γ(pullback p hW.fromSpec, ⊤) := hfW
  refine ⟨U, hU, hxU, fun y hy => (hUW hy).2, ?_⟩
  exact sections_free_of_isPullback (pullback.snd p hW.fromSpec)
    (pullback.snd p hU.fromSpec) _ a Hsmall

end AlgebraicGeometry.FiniteSchemeNormBaseChange
