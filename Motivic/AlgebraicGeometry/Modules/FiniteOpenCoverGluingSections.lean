/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Modules.FiniteOpenCoverGluingCoherence

/-!
# Canonical common-open section transitions

The supplied sheaf transition cocycle induces the ordinary compositional
cocycle on actual sections over each common ambient open.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.FiniteOpenModuleGluing

open Scheme.Modules Motivic.OpenModuleGluing

variable {X : Scheme.{u}} {ι : Type u}
  (U : ι → X.Opens) (M : ∀ i, (U i).toScheme.Modules)

/-- The actual abelian group of sections of the original module over an ambient open. -/
abbrev ambientSections (i : ι) (W : X.Opens) : AddCommGrpCat.{u} :=
  Γ(M i, (U i).ι ⁻¹ᵁ W)

/-- Top sections of the restriction agree with the original ambient-open sections. -/
def restrictionSectionsIso {W : X.Opens} (i : ι) (hi : W ≤ U i) :
    Γ((restrictFunctor (X.homOfLE hi)).obj (M i), ⊤) ≅ ambientSections U M i W :=
  (M i).presheaf.mapIso (eqToIso (show (U i).ι ⁻¹ᵁ W = X.homOfLE hi ''ᵁ ⊤ by
    simp [Scheme.Hom.image_top_eq_opensRange])).op

/-- Evaluating a sheaf isomorphism gives its actual abelian-group section isomorphism. -/
def sectionIso {Y : Scheme.{u}} {P N : Y.Modules} (e : P ≅ N) (W : Y.Opens) :
    Γ(P, W) ≅ Γ(N, W) where
  hom := e.hom.app W
  inv := e.inv.app W
  hom_inv_id := by rw [← Hom.comp_app, Iso.hom_inv_id, Hom.id_app]
  inv_hom_id := by rw [← Hom.comp_app, Iso.inv_hom_id, Hom.id_app]

/-- The original overlap transition on sections over any actual common ambient open. -/
def sectionTransition (d : Datum U M) {W : X.Opens} (i j : ι)
    (hi : W ≤ U i) (hj : W ≤ U j) : ambientSections U M i W ≅ ambientSections U M j W :=
  (restrictionSectionsIso U M i hi).symm ≪≫
    sectionIso (transitionOn U M d.transition i j hi hj) ⊤ ≪≫
      restrictionSectionsIso U M j hj

/-- The section transitions satisfy the original triple cocycle without extra hypotheses. -/
theorem sectionTransition_cocycle (d : Datum U M) {W : X.Opens} (i j k : ι)
    (hi : W ≤ U i) (hj : W ≤ U j) (hk : W ≤ U k) :
    sectionTransition U M d i j hi hj ≪≫ sectionTransition U M d j k hj hk =
      sectionTransition U M d i k hi hk := by
  apply Iso.ext
  have hc := congrArg (fun e => e.hom.app ⊤) (d.cocycle W i j k hi hj hk)
  simp only [Iso.trans_hom, Hom.comp_app] at hc
  simp only [sectionTransition, Iso.trans_hom, Iso.symm_hom, sectionIso, Category.assoc,
    Iso.hom_inv_id_assoc]
  exact congrArg (fun φ => (restrictionSectionsIso U M i hi).inv ≫
    φ ≫ (restrictionSectionsIso U M k hk).hom) hc |>.trans (by rfl)

set_option backward.isDefEq.respectTransparency false in
/-- An arbitrary presentation of the common open gives the same supplied transition on sections. -/
theorem sectionTransition_hom_formula (d : Datum U M) {W : X.Opens} (i j : ι)
    (hi : W ≤ U i) (hj : W ≤ U j) (S : (U i ⊓ U j).toScheme.Opens)
    (hS : S = X.homOfLE (le_inf hi hj) ''ᵁ ⊤) :
    (sectionTransition U M d i j hi hj).hom =
      (M i).presheaf.map (eqToHom (show
        X.homOfLE (inf_le_left : U i ⊓ U j ≤ U i) ''ᵁ S = (U i).ι ⁻¹ᵁ W by
          simp [hS, Scheme.Hom.image_top_eq_opensRange, homOfLE_image_preimage_ι,
            inf_eq_right.mpr (le_inf hi hj)])).op ≫
      overlapApp (d.transition i j).hom S ≫
      (M j).presheaf.map (eqToHom (show (U j).ι ⁻¹ᵁ W =
        X.homOfLE (inf_le_right : U i ⊓ U j ≤ U j) ''ᵁ S by
          simp [hS, Scheme.Hom.image_top_eq_opensRange, homOfLE_image_preimage_ι,
            inf_eq_right.mpr (le_inf hi hj)])).op := by
  subst S
  simp only [sectionTransition, Iso.trans_hom, Iso.symm_hom, sectionIso,
    transitionOn_hom_app, restrictionSectionsIso, Functor.mapIso_hom,
    Functor.mapIso_inv]
  change (M i).presheaf.map _ ≫ ((M i).presheaf.map _ ≫
      overlapApp (d.transition i j).hom _ ≫ (M j).presheaf.map _) ≫
    (M j).presheaf.map _ = _
  simp only [Category.assoc, ← Functor.map_comp_assoc, ← Functor.map_comp]
  congr 2

/-- Restriction of original-module sections along a literal ambient open inclusion. -/
def ambientSectionMap (i : ι) {V W : X.Opens} (h : V ≤ W) :
    ambientSections U M i W ⟶ ambientSections U M i V :=
  (M i).presheaf.map (homOfLE ((U i).ι.preimage_mono h)).op

set_option backward.isDefEq.respectTransparency false in
/-- The supplied overlap morphism is natural on its actual overlap sections. -/
theorem overlapApp_naturality {T Y Z : Scheme.{u}} {a : T ⟶ Y} {b : T ⟶ Z}
    [IsOpenImmersion a] [IsOpenImmersion b] {P : Y.Modules} {N : Z.Modules}
    (φ : (restrictFunctor a).obj P ⟶ (restrictFunctor b).obj N)
    {V W : T.Opens} (h : V ≤ W) :
    P.presheaf.map (homOfLE (a.image_mono h)).op ≫ overlapApp φ V =
      overlapApp φ W ≫ N.presheaf.map (homOfLE (b.image_mono h)).op :=
  φ.mapPresheaf.naturality (homOfLE h).op

set_option backward.isDefEq.respectTransparency false in
/-- The common-open transitions commute with every actual ambient section restriction. -/
theorem sectionTransition_naturality (d : Datum U M) {V W : X.Opens} (h : V ≤ W)
    (i j : ι) (hi : W ≤ U i) (hj : W ≤ U j) :
    ambientSectionMap U M i h ≫ (sectionTransition U M d i j (h.trans hi) (h.trans hj)).hom =
      (sectionTransition U M d i j hi hj).hom ≫ ambientSectionMap U M j h := by
  rw [sectionTransition_hom_formula U M d i j (h.trans hi) (h.trans hj)
    ((U i ⊓ U j).ι ⁻¹ᵁ V) (by simp [Scheme.Hom.image_top_eq_opensRange]),
    sectionTransition_hom_formula U M d i j hi hj
      ((U i ⊓ U j).ι ⁻¹ᵁ W) (by simp [Scheme.Hom.image_top_eq_opensRange])]
  have hn := overlapApp_naturality (d.transition i j).hom
    ((U i ⊓ U j).ι.preimage_mono h)
  have hc := congrArg (fun φ =>
    (M i).presheaf.map (eqToHom (show
      X.homOfLE (inf_le_left : U i ⊓ U j ≤ U i) ''ᵁ ((U i ⊓ U j).ι ⁻¹ᵁ W) =
        (U i).ι ⁻¹ᵁ W by
          rw [homOfLE_image_preimage_ι, inf_eq_right.mpr (le_inf hi hj)])).op ≫
      φ ≫ (M j).presheaf.map (eqToHom (show (U j).ι ⁻¹ᵁ V =
        X.homOfLE (inf_le_right : U i ⊓ U j ≤ U j) ''ᵁ ((U i ⊓ U j).ι ⁻¹ᵁ V) by
          rw [homOfLE_image_preimage_ι,
            inf_eq_right.mpr (le_inf (h.trans hi) (h.trans hj))])).op) hn
  simp only [ambientSectionMap, Category.assoc, ← Functor.map_comp_assoc,
    ← Functor.map_comp] at hc ⊢
  convert hc using 2

end Motivic.FiniteOpenModuleGluing
