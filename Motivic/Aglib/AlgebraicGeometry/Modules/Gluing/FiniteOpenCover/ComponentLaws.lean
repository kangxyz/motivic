/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Modules.Gluing.FiniteOpenCover.Sections

/-!
# Component laws from the ordinary overlap cocycle

The original transition naturality and triple cocycle supply the local
component compatibility required by the finite equalizer construction.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules.Gluing.FiniteOpenCover

open Scheme.Modules _root_.AlgebraicGeometry.Scheme.Modules.Gluing.TwoOpenCover

variable {X : Scheme.{u}} {ι : Type u}
  (U : ι → X.Opens) (M : ∀ i, (U i).toScheme.Modules)

/-- A local component on ambient-open sections, with its canonical image transport. -/
def componentSections (d : Datum U M) (i j : ι) (A : X.Opens) (hA : A ≤ U i) :
    ambientSections U M i A ⟶ ambientSections U M j A :=
  (localComponent U M d i j).app ((U i).ι ⁻¹ᵁ A) ≫
    (M j).presheaf.map (eqToHom (show (U j).ι ⁻¹ᵁ A =
      (U j).ι ⁻¹ᵁ ((U i).ι ''ᵁ ((U i).ι ⁻¹ᵁ A)) by
        rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
          inf_eq_right.mpr hA])).op

set_option backward.isDefEq.respectTransparency false in
/-- On every smaller common open, a local component is precisely the given section transition. -/
theorem componentSections_restrict (d : Datum U M) (i j : ι) {A W : X.Opens}
    (hA : A ≤ U i) (h : W ≤ A) (hj : W ≤ U j) :
    componentSections U M d i j A hA ≫ ambientSectionMap U M j h =
      ambientSectionMap U M i h ≫
        (sectionTransition U M d i j (h.trans hA) hj).hom := by
  rw [sectionTransition_hom_formula U M d i j (h.trans hA) hj
    ((U i ⊓ U j).ι ⁻¹ᵁ W) (by simp [Scheme.Hom.image_top_eq_opensRange])]
  have ho : (U i ⊓ U j).ι ⁻¹ᵁ W ≤
      X.homOfLE (inf_le_left : U i ⊓ U j ≤ U i) ⁻¹ᵁ ((U i).ι ⁻¹ᵁ A) := by
    rw [homOfLE_preimage_ι]
    exact (U i ⊓ U j).ι.preimage_mono h
  have hn := overlapApp_naturality (d.transition i j).hom ho
  have hs : X.homOfLE (inf_le_right : U i ⊓ U j ≤ U j) ''ᵁ
      ((U i ⊓ U j).ι ⁻¹ᵁ W) = (U j).ι ⁻¹ᵁ W := by
    rw [homOfLE_image_preimage_ι, inf_eq_right.mpr (le_inf (h.trans hA) hj)]
  have hc := congrArg (fun φ =>
    (M i).presheaf.map (homOfLE ((X.homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).image_preimage_le
      ((U i).ι ⁻¹ᵁ A))).op ≫ φ ≫ (M j).presheaf.map (eqToHom hs.symm).op) hn
  simp only [componentSections, localComponent_app, ambientSectionMap]
  change ((M i).presheaf.map _ ≫ overlapApp (d.transition i j).hom _ ≫
      (M j).presheaf.map _) ≫ (M j).presheaf.map _ ≫ (M j).presheaf.map _ =
    (M i).presheaf.map _ ≫ (M i).presheaf.map _ ≫
      overlapApp (d.transition i j).hom _ ≫ (M j).presheaf.map _
  simp only [Category.assoc, ← Functor.map_comp_assoc, ← Functor.map_comp] at hc ⊢
  convert hc.symm using 2

set_option backward.isDefEq.respectTransparency false in
/-- The standard triple cocycle gives the component relation on every common ambient open. -/
theorem componentSections_cocycle (d : Datum U M) (i j k : ι) {A W : X.Opens}
    (hA : A ≤ U i) (h : W ≤ A) (hj : W ≤ U j) (hk : W ≤ U k) :
    componentSections U M d i j A hA ≫ ambientSectionMap U M j h ≫
        (sectionTransition U M d j k hj hk).hom =
      componentSections U M d i k A hA ≫ ambientSectionMap U M k h := by
  rw [← Category.assoc, componentSections_restrict U M d i j hA h hj,
    componentSections_restrict U M d i k hA h hk]
  have hc := congrArg Iso.hom (sectionTransition_cocycle U M d i j k (h.trans hA) hj hk)
  simpa only [Iso.trans_hom, Category.assoc] using
    congrArg (fun φ => ambientSectionMap U M i h ≫ φ) hc

set_option backward.isDefEq.respectTransparency false in
/-- The ordinary normalized overlap cocycle supplies the equalizer component compatibility. -/
theorem componentsCompatible (d : Datum U M) (i : ι) : ComponentsCompatible U M d i := by
  intro j k
  apply Scheme.Modules.hom_ext
  intro S
  obtain ⟨A, hA, rfl⟩ : ∃ A : X.Opens, A ≤ U i ∧ (U i).ι ⁻¹ᵁ A = S :=
    ⟨(U i).ι ''ᵁ S, (U i).ι_image_le S, (U i).ι.preimage_image_eq S⟩
  let W : X.Opens := A ⊓ (U j ⊓ U k)
  have h : W ≤ A := inf_le_left
  have hj : W ≤ U j := inf_le_right.trans inf_le_left
  have hk : W ≤ U k := inf_le_right.trans inf_le_right
  let T : (U j ⊓ U k).toScheme.Opens :=
    X.homOfLE (inf_le_left : U j ⊓ U k ≤ U j) ⁻¹ᵁ
      ((U j).ι ⁻¹ᵁ ((U i).ι ''ᵁ ((U i).ι ⁻¹ᵁ A)))
  have hT : T = X.homOfLE (le_inf hj hk) ''ᵁ ⊤ := by
    simp [T, W, homOfLE_preimage_ι, Scheme.Hom.image_top_eq_opensRange,
      Scheme.Hom.preimage_inf, Scheme.Hom.image_preimage_eq_opensRange_inf,
      inf_eq_right.mpr hA]
  have hs : X.homOfLE (inf_le_right : U j ⊓ U k ≤ U k) ''ᵁ T = (U k).ι ⁻¹ᵁ W := by
    rw [hT]
    simp [Scheme.Hom.image_top_eq_opensRange, homOfLE_image_preimage_ι,
      inf_eq_right.mpr (le_inf hj hk)]
  have hc := componentSections_cocycle U M d i j k hA h hj hk
  rw [sectionTransition_hom_formula U M d j k hj hk T hT] at hc
  simp only [Hom.comp_app, restrictFunctor_map_app, leftOverlapMap, pushforward_map_app,
    restrictAdjunction_unit_app_app, rightOverlapMap_app]
  apply (cancel_mono ((d.transition j k).hom.app T ≫
    (M k).presheaf.map (eqToHom hs.symm).op)).mp
  simp only [Category.assoc]
  rw [← Category.assoc ((d.transition j k).inv.app T), ← Hom.comp_app,
    Iso.inv_hom_id, Hom.id_app, Category.id_comp]
  simp only [componentSections, ambientSectionMap, Category.assoc,
    ← Functor.map_comp_assoc, ← Functor.map_comp] at hc
  change (localComponent U M d i j).app ((U i).ι ⁻¹ᵁ A) ≫
      (M j).presheaf.map _ ≫ overlapApp (d.transition j k).hom T ≫
        (M k).presheaf.map _ =
    (localComponent U M d i k).app ((U i).ι ⁻¹ᵁ A) ≫
      (M k).presheaf.map _ ≫ (M k).presheaf.map _
  simp only [← Functor.map_comp]
  convert hc using 2
  congr 2

end AlgebraicGeometry.Scheme.Modules.Gluing.FiniteOpenCover
