/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Modules.Gluing.FiniteOpenCover.Basic

/-!
# Coherence of finite open module descent

The actual open base-change and transition maps are normalized on sections.
The diagonal component identity is derived from normalization. The remaining
triple component identity and effective-descent theorem are separate obligations.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules.Gluing.FiniteOpenCover

open Scheme.Modules _root_.AlgebraicGeometry.Scheme.Modules.Gluing.TwoOpenCover

/-- A restriction morphism evaluated with its literal image-open section types. -/
def overlapApp {T Y Z : Scheme.{u}} {a : T ⟶ Y} {b : T ⟶ Z}
    [IsOpenImmersion a] [IsOpenImmersion b] {P : Y.Modules} {N : Z.Modules}
    (φ : (restrictFunctor a).obj P ⟶ (restrictFunctor b).obj N) (V : T.Opens) :
    Γ(P, a ''ᵁ V) ⟶ Γ(N, b ''ᵁ V) := φ.app V

set_option backward.isDefEq.respectTransparency false in
/-- Restriction evaluates module morphisms on the literal image open. -/
@[simp] theorem restrictFunctor_map_app {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    [IsOpenImmersion f] {P Q : Z.Modules} (φ : P ⟶ Q) (W : Y.Opens) :
    ((restrictFunctor f).map φ).app W = φ.app (f ''ᵁ W) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The open base-change map is the canonical equality transport on sections. -/
theorem pushforwardRestrictIso_hom_app {T Y Z A : Scheme.{u}}
    {a : T ⟶ Y} {b : T ⟶ Z} {f : Y ⟶ A} {g : Z ⟶ A}
    [IsOpenImmersion a] [IsOpenImmersion b] [IsOpenImmersion f] [IsOpenImmersion g]
    (sq : IsPullback a b f g) (N : Z.Modules) (W : Y.Opens) :
    (pushforwardRestrictIso sq N).hom.app W =
      N.presheaf.map (eqToHom
        (IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback sq W)).op := by
  simp only [pushforwardRestrictIso, Iso.trans_hom, asIso_hom, Functor.mapIso_hom,
    Hom.comp_app, restrictAdjunction_unit_app_app, pushforward_map_app,
    Iso.app_hom, Iso.symm_hom, restrictFunctorComp_inv_app_app,
    restrictFunctorCongr_hom_app_app, restrictFunctorComp_hom_app_app,
    restrictFunctor_map_app, restrict_map, pushforward_obj_presheaf_map]
  change N.presheaf.map _ ≫ N.presheaf.map _ ≫ N.presheaf.map _ ≫
    N.presheaf.map _ ≫ N.presheaf.map _ = N.presheaf.map _
  simp only [← Functor.map_comp]
  congr 1

set_option backward.isDefEq.respectTransparency false in
/-- The inverse open base-change map is the reverse equality transport. -/
theorem pushforwardRestrictIso_inv_app {T Y Z A : Scheme.{u}}
    {a : T ⟶ Y} {b : T ⟶ Z} {f : Y ⟶ A} {g : Z ⟶ A}
    [IsOpenImmersion a] [IsOpenImmersion b] [IsOpenImmersion f] [IsOpenImmersion g]
    (sq : IsPullback a b f g) (N : Z.Modules) (W : Y.Opens) :
    (pushforwardRestrictIso sq N).inv.app W =
      N.presheaf.map (eqToHom
        (IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback sq W).symm).op := by
  apply (cancel_mono ((pushforwardRestrictIso sq N).hom.app W)).mp
  rw [← Hom.comp_app, Iso.inv_hom_id, Hom.id_app, pushforwardRestrictIso_hom_app]
  change 𝟙 _ = N.presheaf.map _ ≫ N.presheaf.map _
  simp only [← Functor.map_comp]
  exact (N.presheaf.map_id _).symm

set_option backward.isDefEq.respectTransparency false in
/-- The second pushed overlap map first restricts a section and applies the inverse transition. -/
theorem rightOverlapMap_app {T Y Z A : Scheme.{u}}
    {a : T ⟶ Y} {b : T ⟶ Z} {f : Y ⟶ A} {g : Z ⟶ A}
    [IsOpenImmersion a] [IsOpenImmersion b] [IsOpenImmersion f] [IsOpenImmersion g]
    (sq : IsPullback a b f g) (P : Y.Modules) (N : Z.Modules)
    (e : (restrictFunctor a).obj P ≅ (restrictFunctor b).obj N) (W : A.Opens) :
    (rightOverlapMap sq P N e).app W =
      N.presheaf.map (homOfLE (show b ''ᵁ a ⁻¹ᵁ (f ⁻¹ᵁ W) ≤ g ⁻¹ᵁ W by
        rw [IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback sq]
        exact g.preimage_mono (f.image_preimage_le W))).op ≫
        e.inv.app (a ⁻¹ᵁ (f ⁻¹ᵁ W)) := by
  simp only [rightOverlapMap, Adjunction.homEquiv_unit, Hom.comp_app,
    restrictAdjunction_unit_app_app, pushforward_obj_presheaf_map, pushforward_map_app,
    overlapComparison, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    pushforwardRestrictIso_hom_app]
  change N.presheaf.map _ ≫ N.presheaf.map _ ≫ _ = N.presheaf.map _ ≫ _
  rw [← Category.assoc, ← Functor.map_comp]
  congr 2

variable {X : Scheme.{u}} {ι : Type u}
  (U : ι → X.Opens) (M : ∀ i, (U i).toScheme.Modules)

/-- The image of a smaller common open does not depend on factoring through the overlap. -/
theorem overlap_image {W : X.Opens} {i j : ι} (hi : W ≤ U i) (hj : W ≤ U j)
    (V : W.toScheme.Opens) :
    X.homOfLE (inf_le_left : U i ⊓ U j ≤ U i) ''ᵁ
        X.homOfLE (le_inf hi hj) ''ᵁ V = X.homOfLE hi ''ᵁ V := by
  simp [← Scheme.Hom.comp_image]

/-- Preimages through the open inclusion factor strictly through the ambient scheme. -/
@[simp] theorem homOfLE_preimage_ι {V W : X.Opens} (h : V ≤ W) (A : X.Opens) :
    X.homOfLE h ⁻¹ᵁ (W.ι ⁻¹ᵁ A) = V.ι ⁻¹ᵁ A := by
  rw [← Scheme.Hom.comp_preimage, Scheme.homOfLE_ι]

/-- The image under an inclusion is the corresponding ambient intersection. -/
theorem homOfLE_image_preimage_ι {V W : X.Opens} (h : V ≤ W) (A : X.Opens) :
    X.homOfLE h ''ᵁ (V.ι ⁻¹ᵁ A) = W.ι ⁻¹ᵁ (V ⊓ A) := by
  apply W.ι.image_injective
  simp only [← Scheme.Hom.comp_image, Scheme.homOfLE_ι,
    Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  rw [← inf_assoc, inf_eq_right.mpr h]

set_option backward.isDefEq.respectTransparency false in
/-- Restricting a transition gives its section map with the canonical equality transports. -/
theorem transitionOn_hom_app (e : ∀ i j, Transition U M i j) {W : X.Opens} (i j : ι)
    (hi : W ≤ U i) (hj : W ≤ U j) (V : W.toScheme.Opens) :
    (transitionOn U M e i j hi hj).hom.app V =
      (M i).presheaf.map (eqToHom (overlap_image U hi hj V)).op ≫
        (e i j).hom.app (X.homOfLE (le_inf hi hj) ''ᵁ V) ≫
          (M j).presheaf.map (eqToHom (show X.homOfLE hj ''ᵁ V =
            X.homOfLE (inf_le_right : U i ⊓ U j ≤ U j) ''ᵁ
              X.homOfLE (le_inf hi hj) ''ᵁ V by simp [← Scheme.Hom.comp_image])).op := by
  simp only [transitionOn, restrictToOverlapIso, Iso.trans_hom, Iso.symm_hom,
    Iso.trans_inv, Iso.app_hom, Iso.app_inv, Functor.mapIso_hom, Hom.comp_app,
    restrictFunctorComp_hom_app_app, restrictFunctorCongr_hom_app_app,
    restrictFunctorComp_inv_app_app, restrictFunctorCongr_inv_app_app,
    restrictFunctor_map_app]
  change ((M i).presheaf.map _ ≫ (M i).presheaf.map _) ≫ _ ≫
    (M j).presheaf.map _ ≫ (M j).presheaf.map _ = _
  simp only [← Functor.map_comp]
  congr 2

set_option backward.isDefEq.respectTransparency false in
/-- The local component sends a section to its supplied transition on the overlap. -/
theorem localComponent_app (d : Datum U M) (i j : ι) (W : (U i).toScheme.Opens) :
    (localComponent U M d i j).app W =
      (M i).presheaf.map
        (homOfLE ((X.homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).image_preimage_le W)).op ≫
      (d.transition i j).hom.app (X.homOfLE (inf_le_left : U i ⊓ U j ≤ U i) ⁻¹ᵁ W) ≫
      (M j).presheaf.map (eqToHom
        (IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback
          (isPullback_opens_inf (U i) (U j)) W).symm).op := by
  simp only [localComponent, overlapComparison, Iso.trans_inv, Functor.mapIso_inv,
    Iso.symm_inv, Hom.comp_app, restrictAdjunction_unit_app_app, pushforward_map_app,
    pushforwardRestrictIso_inv_app]

set_option backward.isDefEq.respectTransparency false in
/-- The two restriction routes through a repeated member agree literally. -/
theorem overlapRestrictionIso_self (i : ι) :
    overlapRestrictionIso (isPullback_opens_inf (U i) (U i)) = Iso.refl _ := by
  apply Iso.ext
  apply NatTrans.ext
  funext N
  apply Scheme.Modules.hom_ext
  intro W
  simp only [overlapRestrictionIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Hom.comp_app, restrictFunctorComp_inv_app_app, restrictFunctorCongr_hom_app_app,
    restrictFunctorComp_hom_app_app, Iso.refl_hom, NatTrans.id_app, Hom.id_app]
  simp only [← Functor.map_comp]
  exact N.presheaf.map_id _

set_option backward.isDefEq.respectTransparency false in
/-- Normalization of the original transition supplies the diagonal local component law. -/
theorem localComponent_diagonal (d : Datum U M) (i : ι) :
    localComponent U M d i i ≫ (restrictAdjunction (U i).ι).counit.app (M i) = 𝟙 _ := by
  dsimp only [localComponent]
  apply (cancel_mono (inv ((restrictAdjunction (U i).ι).counit.app (M i)))).mp
  simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id, Category.id_comp]
  apply (cancel_mono (overlapComparison (isPullback_opens_inf (U i) (U i))
    (M i) (M i) (d.transition i i)).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [overlapComparison_hom_eq_mate, overlapRestrictionIso_self, d.identity]
  simp [Adjunction.homEquiv_unit]

end AlgebraicGeometry.Scheme.Modules.Gluing.FiniteOpenCover
