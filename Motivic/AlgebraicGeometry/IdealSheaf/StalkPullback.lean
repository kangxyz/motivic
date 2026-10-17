/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.IdealSheaf.Stalk
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# Pullback of ideal sheaves on actual stalk rings

The scheme-theoretic pullback of an ideal sheaf extends its affine ideals
along section homomorphisms and its stalk ideals along the actual stalk maps.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X Y : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- On affine schemes, the scheme-theoretic pullback extends the section ideal. -/
theorem ideal_comap_top [IsAffine X] [IsAffine Y] (I : Y.IdealSheafData) (f : X ⟶ Y) :
    (I.comap f).ideal ⟨⊤, isAffineOpen_top X⟩ =
      (I.ideal ⟨⊤, isAffineOpen_top Y⟩).map f.appTop.hom := by
  let L := (I.ideal ⟨⊤, isAffineOpen_top Y⟩).map f.appTop.hom
  have hL : (ofIdealTop L).ideal ⟨⊤, isAffineOpen_top X⟩ = L := by
    simp [ofIdealTop_ideal]
  apply le_antisymm
  · have h : I ≤ (ofIdealTop L).map f := by
      apply le_of_isAffine
      rw [ideal_map_of_isAffineHom]
      simpa [hL, L, Scheme.Hom.appTop] using!
        (Ideal.le_comap_map (I := I.ideal ⟨⊤, isAffineOpen_top Y⟩) (f := f.appTop.hom))
    have := (le_map_iff_comap_le.mp h) ⟨⊤, isAffineOpen_top X⟩
    simpa [hL] using! this
  · apply Ideal.map_le_iff_le_comap.mpr
    have := (le_map_comap I f) ⟨⊤, isAffineOpen_top Y⟩
    simpa [ideal_map_of_isAffineHom, Scheme.Hom.appTop] using! this

/-- On affine schemes the ideal pullback extends the actual stalk ideal. -/
theorem stalk_comap_of_isAffine [IsAffine X] [IsAffine Y]
    (I : Y.IdealSheafData) (f : X ⟶ Y) (x : X) :
    (I.comap f).stalk x = (I.stalk (f x)).map (f.stalkMap x).hom := by
  rw [(I.comap f).stalk_eq_map ⟨⊤, isAffineOpen_top X⟩ trivial,
    ideal_comap_top, I.stalk_eq_map ⟨⊤, isAffineOpen_top Y⟩ trivial,
    Ideal.map_map, Ideal.map_map]
  congr 1
  exact congrArg CommRingCat.Hom.hom (f.germ_stalkMap ⊤ x trivial).symm

/-- Pullback along an open immersion extends the actual stalk ideal. -/
theorem stalk_comap_of_isOpenImmersion
    (I : Y.IdealSheafData) (f : X ⟶ Y) [IsOpenImmersion f] (x : X) :
    (I.comap f).stalk x = (I.stalk (f x)).map (f.stalkMap x).hom := by
  obtain ⟨U, hU, hxU, -⟩ :=
    Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens (show x ∈ (⊤ : X.Opens) from trivial)
  change X.Opens at U
  change IsAffineOpen U at hU
  have hyU : f x ∈ f ''ᵁ U := ⟨x, hxU, rfl⟩
  rw [(I.comap f).stalk_eq_map ⟨U, hU⟩ hxU,
    I.stalk_eq_map ⟨f ''ᵁ U, hU.image_of_isOpenImmersion f⟩ hyU,
    ideal_comap_of_isOpenImmersion]
  have he : (I.ideal ⟨f ''ᵁ U, hU.image_of_isOpenImmersion f⟩).comap
      (f.appIso U).inv.hom =
      (I.ideal ⟨f ''ᵁ U, hU.image_of_isOpenImmersion f⟩).map (f.appIso U).hom.hom :=
    (Ideal.map_comap_of_equiv (f.appIso U).commRingCatIsoToRingEquiv).symm
  rw [he, Ideal.map_map, Ideal.map_map]
  congr 1
  rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp]
  congr 1
  rw [Scheme.Hom.appIso_hom', Scheme.Hom.appLE, Category.assoc,
    X.presheaf.germ_res', f.germ_stalkMap]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Scheme-theoretic ideal pullback is extension along the actual stalk map. -/
theorem stalk_comap (I : Y.IdealSheafData) (f : X ⟶ Y) (x : X) :
    (I.comap f).stalk x = (I.stalk (f x)).map (f.stalkMap x).hom := by
  obtain ⟨U, hU, hxU, -⟩ :=
    Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens (show f x ∈ (⊤ : Y.Opens) from trivial)
  obtain ⟨V, hV, hxV, hVU⟩ :=
    Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens (show x ∈ f ⁻¹ᵁ U from hxU)
  change Y.Opens at U
  change X.Opens at V
  change IsAffineOpen U at hU
  change IsAffineOpen V at hV
  let f' := f.resLE U V hVU
  let x' : V.toScheme := ⟨x, hxV⟩
  have : IsAffine U.toScheme := hU
  have : IsAffine V.toScheme := hV
  have heq : (I.comap f).comap V.ι = (I.comap U.ι).comap f' := by
    rw [← comap_comp, ← comap_comp]
    exact congrArg (I.comap ·) (f.resLE_comp_ι hVU).symm
  have h : ((I.comap f).stalk (V.ι x')).map (V.ι.stalkMap x').hom =
      ((I.stalk (f (V.ι x'))).map (f.stalkMap (V.ι x')).hom).map
        (V.ι.stalkMap x').hom := by
    rw [← stalk_comap_of_isOpenImmersion (I.comap f) V.ι x', heq,
      stalk_comap_of_isAffine, stalk_comap_of_isOpenImmersion]
    have hs := Scheme.Hom.stalkMap_congr_hom (f' ≫ U.ι) (V.ι ≫ f)
      (f.resLE_comp_ι hVU) x'
    have hp : U.ι (f' x') = f (V.ι x') :=
      congrArg (fun k : V.toScheme ⟶ Y => k x') (f.resLE_comp_ι hVU)
    have hs' : U.ι.stalkMap (f' x') ≫ f'.stalkMap x' =
        (Y.presheaf.stalkCongr (.of_eq hp)).hom ≫
          f.stalkMap (V.ι x') ≫ V.ι.stalkMap x' := by
      simpa only [Scheme.Hom.stalkMap_comp] using! hs
    have hi := congrArg (fun k : Y.presheaf.stalk (U.ι (f' x')) ⟶
        V.toScheme.presheaf.stalk x' => (I.stalk (U.ι (f' x'))).map k.hom) hs'
    simp only [CommRingCat.hom_comp, ← Ideal.map_map] at hi
    rw [I.stalk_congr hp] at hi
    exact hi
  apply_fun Ideal.comap (V.ι.stalkMap x').hom at h
  simpa only [Ideal.comap_map_of_bijective _
    (ConcreteCategory.bijective_of_isIso (V.ι.stalkMap x'))] using! h

end AlgebraicGeometry.Scheme.IdealSheafData
