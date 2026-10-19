/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Frames.FiniteNeighborhood
public import Motivic.Aglib.AlgebraicGeometry.Sites.Nisnevich.Lifting.FiniteSplitting

/-!
# Trivializing line bundles above an open base neighborhood

For a finite morphism from an affine scheme, the entire finite point fibre
fits in one principal open trivializing the actual line bundle. Removing the
closed image of its complement gives a base open whose entire inverse image
has a unit trivialization. This uses the existing finite closed-image
shrinking lemma and does not assume that a chosen fibre trivialization has
already been extended.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules.Invertible

/-- A line-bundle unit trivialization restricts to every smaller open. -/
def restrictUnitIsoOfLE {X : Scheme.{u}} (M : X.Modules) {U V : X.Opens}
    (h : U ≤ V) (e : M.restrict V.ι ≅ SheafOfModules.unit V.toScheme.ringCatSheaf) :
    M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf :=
  ((Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι h)).app M).symm ≪≫
    (Scheme.Modules.restrictFunctorComp (X.homOfLE h) V.ι).app M ≪≫
      (Scheme.Modules.restrictFunctor (X.homOfLE h)).mapIso e ≪≫
        Scheme.Modules.restrictUnitIso (X.homOfLE h)

/-- For a finite morphism with affine source, any actual line bundle is
trivial on the entire inverse image of some neighborhood of each base point.
The source is the full finite scheme, with its original nonreduced structure. -/
theorem exists_base_open_unitIso_of_isFinite_spec (R : CommRingCat.{u})
    {Y : Scheme.{u}} (f : Spec R ⟶ Y) [IsFinite f] (y : Y)
    (L : LineBundle (Spec R)) :
    ∃ U : Y.Opens, y ∈ U ∧
      Nonempty ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).obj L.val ≅
        SheafOfModules.unit (f ⁻¹ᵁ U).toScheme.ringCatSheaf) := by
  classical
  let s := (f.finite_preimage_singleton y).toFinset
  obtain ⟨r, hr, ⟨e⟩⟩ := exists_principal_unitIso_around_finset R L s
  let V : (Spec R).Opens := PrimeSpectrum.basicOpen r
  obtain ⟨U, hy, hU⟩ := exists_open_preimage_disjoint_of_isFinite f
    (V : Set (Spec R))ᶜ V.isOpen.isClosed_compl y (by
      intro x hx hxy
      exact hx (hr x ((f.finite_preimage_singleton y).mem_toFinset.mpr hxy)))
  have hUV : f ⁻¹ᵁ U ≤ V := by
    intro x hx
    by_contra hn
    exact Set.disjoint_left.mp hU hx hn
  exact ⟨U, hy, ⟨restrictUnitIsoOfLE L.val hUV e⟩⟩

/-- The affine-source version, independent of a chosen spectrum presentation. -/
theorem exists_base_open_unitIso_of_isFinite_affine {X Y : Scheme.{u}} [IsAffine X]
    (f : X ⟶ Y) [IsFinite f] (y : Y) (L : LineBundle X) :
    ∃ U : Y.Opens, y ∈ U ∧
      Nonempty ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).obj L.val ≅
        SheafOfModules.unit (f ⁻¹ᵁ U).toScheme.ringCatSheaf) := by
  obtain ⟨V, hV, ⟨e⟩⟩ := exists_open_unitIso_around_finite X L (f ⁻¹' {y})
    (f.finite_preimage_singleton y)
  obtain ⟨U, hy, hU⟩ := exists_open_preimage_disjoint_of_isFinite f
    (V : Set X)ᶜ V.isOpen.isClosed_compl y (by
      intro x hx hxy
      exact hx (hV hxy))
  have hUV : f ⁻¹ᵁ U ≤ V := by
    intro x hx
    by_contra hn
    exact Set.disjoint_left.mp hU hx hn
  exact ⟨U, hy, ⟨restrictUnitIsoOfLE L.val hUV e⟩⟩

/-- Finite boundary/support in an affine ambient scheme admits a trivializing
ambient open and a base neighborhood whose entire support lands in that open.
The finite morphism is the support projection; the ambient scheme need not be
finite over the base. The map into the ambient scheme may, in particular, be
a closed immersion of a boundary subscheme. -/
theorem exists_base_open_support_unitIso {B X Y : Scheme.{u}} [IsAffine X]
    (f : B ⟶ Y) [IsFinite f] (i : B ⟶ X) (y : Y) (L : LineBundle X) :
    ∃ (Ω : X.Opens) (U : Y.Opens), y ∈ U ∧
      f ⁻¹' (U : Set Y) ⊆ i ⁻¹' (Ω : Set X) ∧
      Nonempty ((Scheme.Modules.restrictFunctor Ω.ι).obj L.val ≅
        SheafOfModules.unit Ω.toScheme.ringCatSheaf) := by
  obtain ⟨Ω, hΩ, he⟩ := exists_open_unitIso_around_finite X L
    (i '' (f ⁻¹' {y})) ((f.finite_preimage_singleton y).image i)
  let V := i ⁻¹ᵁ Ω
  obtain ⟨U, hy, hU⟩ := exists_open_preimage_disjoint_of_isFinite f
    (V : Set B)ᶜ V.isOpen.isClosed_compl y (by
      intro b hb hby
      exact hb (hΩ ⟨b, hby, rfl⟩))
  refine ⟨Ω, U, hy, ?_, he⟩
  intro b hb
  by_contra hn
  exact Set.disjoint_left.mp hU hb hn

/-- A unit isomorphism along an open immersion is a unit isomorphism on its
actual open range. -/
def restrictUnitIsoOnRange {X Z : Scheme.{u}} (M : X.Modules) (j : Z ⟶ X)
    [IsOpenImmersion j]
    (e : M.restrict j ≅ SheafOfModules.unit Z.ringCatSheaf) :
    M.restrict j.opensRange.ι ≅ SheafOfModules.unit j.opensRange.toScheme.ringCatSheaf :=
  ((Scheme.Modules.restrictFunctorCongr j.isoOpensRange_inv_comp).app M).symm ≪≫
    (Scheme.Modules.restrictFunctorComp j.isoOpensRange.inv j).app M ≪≫
      (Scheme.Modules.restrictFunctor j.isoOpensRange.inv).mapIso e ≪≫
        Scheme.Modules.restrictUnitIso j.isoOpensRange.inv

set_option backward.isDefEq.respectTransparency false in
/-- Every line bundle on the source of a finite morphism is trivial over the
entire inverse image of a sufficiently small open neighborhood of any base
point. Affineness is needed only for a chosen base chart and follows for its
finite inverse image; it is not a global hypothesis. -/
theorem exists_base_open_unitIso_of_isFinite {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsFinite f] (y : Y) (L : LineBundle X) :
    ∃ U : Y.Opens, y ∈ U ∧
      Nonempty ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).obj L.val ≅
        SheafOfModules.unit (f ⁻¹ᵁ U).toScheme.ringCatSheaf) := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hyW, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ y) isOpen_univ
  let V := f ⁻¹ᵁ W
  have : IsAffine V.toScheme := hW.preimage f
  let L' := pullbackLineBundle V.ι L
  obtain ⟨T, hyT, ⟨e⟩⟩ := exists_base_open_unitIso_of_isFinite_affine
    (f ∣_ W) ⟨y, hyW⟩ L'
  let U := (Scheme.Opens.ι (X := Y) W) ''ᵁ T
  let Z := (f ∣_ W) ⁻¹ᵁ T
  let j := Z.ι ≫ V.ι
  let e' : (Scheme.Modules.restrictFunctor j).obj L.val ≅
      SheafOfModules.unit Z.toScheme.ringCatSheaf :=
    (Scheme.Modules.restrictFunctorComp Z.ι V.ι).app L.val ≪≫
      (Scheme.Modules.restrictFunctor Z.ι).mapIso
        ((Scheme.Modules.restrictFunctorIsoPullback V.ι).app L.val) ≪≫ e
  have hj : j.opensRange = f ⁻¹ᵁ U := by
    rw [Scheme.Hom.opensRange_comp, Scheme.Opens.opensRange_ι]
    exact image_morphismRestrict_preimage f W T
  have he : Nonempty ((Scheme.Modules.restrictFunctor j.opensRange.ι).obj L.val ≅
      SheafOfModules.unit j.opensRange.toScheme.ringCatSheaf) :=
    ⟨restrictUnitIsoOnRange L.val j e'⟩
  rw [hj] at he
  exact ⟨U, ⟨⟨y, hyW⟩, hyT, rfl⟩, he⟩

end AlgebraicGeometry.Scheme.Modules.Invertible
