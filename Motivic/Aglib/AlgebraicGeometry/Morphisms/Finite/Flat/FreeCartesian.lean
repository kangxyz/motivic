/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.FiniteSchemeNormBaseChange

/-!
# Coordinate freeness along an actual affine Cartesian square

The bottom arrow is the original scheme map, not a separately chosen ring map.
Full faithfulness of Spec and the actual pullback comparison transport the
existing coordinate freeness theorem with its structural scalar actions.


Intended upstream module: `Aglib.AlgebraicGeometry.Morphisms.Finite.Flat.FreeCartesian`.
Incoming project consumers: `Motivic.Aglib.AlgebraicGeometry.Graph.Frames.FreeProductCharts`,
`Motivic.Aglib.AlgebraicGeometry.RelativeCurve.ProjectiveMap.AffineSourceFreeCharts`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u
namespace AlgebraicGeometry.FiniteSchemeNormBaseChange

/-- Freeness of coordinates is preserved by an actual Cartesian square over
affine schemes. No integrality, finite morphism or replacement scalar action is
needed; the original affine source and its structural free module suffice. -/
theorem sections_free_of_isPullback
    {A B : CommRingCat.{u}} {C D : Scheme.{u}} [IsAffine C]
    (p : C ⟶ Spec A) (q : D ⟶ Spec B) (v : D ⟶ C)
    (b : Spec B ⟶ Spec A) (H : IsPullback v q p b) :
    let : Algebra A Γ(C, ⊤) := (scalarMap p).toAlgebra
    let : Algebra B Γ(D, ⊤) := (scalarMap q).toAlgebra
    ∀ [Module.Free A Γ(C, ⊤)], Module.Free B Γ(D, ⊤) := by
  let : Algebra A Γ(C, ⊤) := (scalarMap p).toAlgebra
  let : Algebra B Γ(D, ⊤) := (scalarMap q).toAlgebra
  dsimp only
  intro hfree
  obtain ⟨rho, rfl⟩ : ∃ rho : A ⟶ B, Spec.map rho = b :=
    ⟨Spec.preimage b, Spec.map_preimage b⟩
  let : Algebra B Γ(pullback p (Spec.map rho), ⊤) :=
    (scalarMap (pullback.snd p (Spec.map rho))).toAlgebra
  let : Module.Free B Γ(pullback p (Spec.map rho), ⊤) :=
    sections_free_pullback p rho.hom
  exact sections_free_of_iso (pullback.snd p (Spec.map rho)) q
    H.isoPullback.symm H.isoPullback_inv_snd

/-- A genuine free affine chart cover of the original target produces canonical
free affine neighborhoods after any actual Cartesian base change. The affine
neighborhoods and comparison maps are constructed from the original cover. -/
theorem exists_free_affine_neighborhood_of_isPullback
    {C T C' T' : Scheme.{u}} (f : C ⟶ T) [IsFinite f]
    (p : C' ⟶ T') (v : C' ⟶ C) (b : T' ⟶ T) (H : IsPullback v p f b)
    {ι : Type u} (A : ι → CommRingCat.{u}) (w : ∀ i, Spec (A i) ⟶ T)
    [∀ i, IsOpenImmersion (w i)]
    (hcover : ∀ t : T, ∃ i, t ∈ Set.range (w i))
    (hfree : ∀ i,
      let : Algebra (A i) Γ(pullback f (w i), ⊤) :=
        (scalarMap (pullback.snd f (w i))).toAlgebra
      Module.Free (A i) Γ(pullback f (w i), ⊤))
    (x : T') :
    ∃ (U : T'.Opens) (hU : IsAffineOpen U), x ∈ U ∧
      (let : Algebra Γ(T', U) Γ(pullback p hU.fromSpec, ⊤) :=
        (scalarMap (pullback.snd p hU.fromSpec)).toAlgebra
       Module.Free Γ(T', U) Γ(pullback p hU.fromSpec, ⊤)) := by
  obtain ⟨i, hi⟩ := hcover (b x)
  have hx : x ∈ b ⁻¹ᵁ (w i).opensRange := hi
  obtain ⟨U, hU, hxU, hUsub⟩ := exists_isAffineOpen_mem_and_subset hx
  have hfac : Set.range (hU.fromSpec ≫ b) ⊆ Set.range (w i) := by
    rintro _ ⟨z, rfl⟩
    apply hUsub
    change hU.fromSpec z ∈ (U : Set T')
    rw [← hU.range_fromSpec]
    exact Set.mem_range_self _
  let a := IsOpenImmersion.lift (w i) (hU.fromSpec ≫ b) hfac
  have ha : a ≫ w i = hU.fromSpec ≫ b :=
    IsOpenImmersion.lift_fac (w i) (hU.fromSpec ≫ b) hfac
  have Hlarge := (IsPullback.of_hasPullback p hU.fromSpec).paste_horiz H
  rw [← ha] at Hlarge
  have Hsmall := Hlarge.of_right' (IsPullback.of_hasPullback f (w i))
  let : IsAffine (pullback f (w i)) :=
    isAffine_of_isAffineHom (pullback.snd f (w i))
  let : Algebra (A i) Γ(pullback f (w i), ⊤) :=
    (scalarMap (pullback.snd f (w i))).toAlgebra
  let : Module.Free (A i) Γ(pullback f (w i), ⊤) := hfree i
  refine ⟨U, hU, hxU, ?_⟩
  exact sections_free_of_isPullback (pullback.snd f (w i))
    (pullback.snd p hU.fromSpec) _ a Hsmall

end AlgebraicGeometry.FiniteSchemeNormBaseChange
