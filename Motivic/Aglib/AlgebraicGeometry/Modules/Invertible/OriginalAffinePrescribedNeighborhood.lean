/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.AffinePrescribedNeighborhood
public import Aglib.AlgebraicGeometry.Modules.IsomorphismFunctors

/-! # Prescribed boundary frames on the original affine scheme -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules.Invertible

variable {X Z : Scheme.{u}} [IsAffine X] [IsAffine Z]

/-- The exact boundary comparison in affine coordinates detects the original
boundary value, since canonical affine pullback is faithful. -/
theorem pullbackUnitMap_eq_of_affineBoundaryFrame (z : Z ⟶ X) (L : LineBundle X)
    (e : (Modules.pullback z).obj L.val ≅ SheafOfModules.unit Z.ringCatSheaf)
    (F : L.val ⟶ SheafOfModules.unit X.ringCatSheaf)
    (h : pullbackUnitMap (Spec.map z.appTop) (pullbackUnitMap X.isoSpec.inv F) =
      (affineBoundaryFrame z L e).hom) : pullbackUnitMap z F = e.hom := by
  let : (Modules.pullback Z.isoSpec.inv).IsEquivalence :=
    Modules.pullback_isEquivalence_of_isIso Z.isoSpec.inv
  apply (Modules.pullback Z.isoSpec.inv).map_injective
  apply (cancel_mono (pullbackUnitIso Z.isoSpec.inv).hom).mp
  change pullbackUnitMap Z.isoSpec.inv (pullbackUnitMap z F) =
    pullbackUnitMap Z.isoSpec.inv e.hom
  rw [← pullbackUnitMap_comp (Spec.map z.appTop) X.isoSpec.inv F] at h
  change _ = (Modules.pullbackComp (Spec.map z.appTop) X.isoSpec.inv).hom.app L.val ≫
    (Modules.pullbackCongr (Scheme.isoSpec_inv_naturality z)).hom.app L.val ≫
    (Modules.pullbackComp Z.isoSpec.inv z).inv.app L.val ≫
    pullbackUnitMap Z.isoSpec.inv e.hom at h
  have h₁ := (cancel_epi
    ((Modules.pullbackComp (Spec.map z.appTop) X.isoSpec.inv).hom.app L.val)).mp h
  rw [← pullbackUnitMap_congr (Scheme.isoSpec_inv_naturality z) F] at h₁
  have h₂ := (cancel_epi
    ((Modules.pullbackCongr (Scheme.isoSpec_inv_naturality z)).hom.app L.val)).mp h₁
  rw [← pullbackUnitMap_comp Z.isoSpec.inv z F, h₂]
  exact Iso.hom_inv_id_assoc ((Modules.pullbackComp Z.isoSpec.inv z).app L.val) _

/-- The original affine line has an actual functional with precisely the given
whole-boundary value, invertible on a principal chart of its canonical spectrum. -/
theorem exists_original_globalFunctional_prescribed_boundary
    (z : Z ⟶ X) [IsClosedImmersion z] (L : LineBundle X)
    (e : (Modules.pullback z).obj L.val ≅ SheafOfModules.unit Z.ringCatSheaf) :
    ∃ F : L.val ⟶ SheafOfModules.unit X.ringCatSheaf,
      pullbackUnitMap z F = e.hom ∧
      ∃ r : Γ(X, ⊤), z.appTop r = 1 ∧
        IsIso (pullbackUnitMap
          (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, ⊤) (Localization.Away r))) ≫
            X.isoSpec.inv) F) := by
  let : Algebra Γ(X, ⊤) Γ(Z, ⊤) := z.appTop.hom.toAlgebra
  obtain ⟨G, hG, r, hr, hi⟩ := exists_globalFunctional_prescribed_boundary
    Γ(X, ⊤) Γ(Z, ⊤) (z.app_surjective ⊤ (isAffineOpen_top X))
    (pullbackLineBundle X.isoSpec.inv L) (affineBoundaryFrame z L e)
  let : (Modules.pullback X.isoSpec.inv).IsEquivalence :=
    Modules.pullback_isEquivalence_of_isIso X.isoSpec.inv
  let F : L.val ⟶ SheafOfModules.unit X.ringCatSheaf :=
    (Modules.pullback X.isoSpec.inv).preimage (G ≫ (pullbackUnitIso X.isoSpec.inv).inv)
  have hF : pullbackUnitMap X.isoSpec.inv F = G := by
    dsimp only [pullbackUnitMap, F]
    rw [CategoryTheory.Functor.map_preimage]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  refine ⟨F, pullbackUnitMap_eq_of_affineBoundaryFrame z L e F (by rwa [hF]), r, hr, ?_⟩
  let j := Spec.map (CommRingCat.ofHom (algebraMap Γ(X, ⊤) (Localization.Away r)))
  have he := pullbackUnitMap_comp j X.isoSpec.inv F
  rw [hF] at he
  have : IsIso (pullbackUnitMap j G) := hi
  have : IsIso ((Modules.pullbackComp j X.isoSpec.inv).hom.app L.val ≫
      pullbackUnitMap (j ≫ X.isoSpec.inv) F) :=
    he.symm ▸ (inferInstance : IsIso (pullbackUnitMap j G))
  exact IsIso.of_isIso_comp_left ((Modules.pullbackComp j X.isoSpec.inv).hom.app L.val) _

/-- Extend the specified frame to an actual affine open neighborhood in the
original scheme. The entire original boundary factors through that neighborhood
and its pulled-back frame is exactly the given one. -/
theorem exists_original_affine_open_prescribed_frame
    (z : Z ⟶ X) [IsClosedImmersion z] (L : LineBundle X)
    (e : (Modules.pullback z).obj L.val ≅ SheafOfModules.unit Z.ringCatSheaf) :
    ∃ (U : Scheme.{u}) (_ : IsAffine U) (v : U ⟶ X) (_ : IsOpenImmersion v)
      (b : Z ⟶ U) (hb : b ≫ v = z)
      (d : (Modules.pullback v).obj L.val ≅ SheafOfModules.unit U.ringCatSheaf),
      ((Modules.pullbackCongr hb).app L.val).symm ≪≫
        ((Modules.pullbackComp b v).app L.val).symm ≪≫
        (Modules.pullback b).mapIso d ≪≫ pullbackUnitIso b = e := by
  obtain ⟨F, hF, r, hr, hi⟩ := exists_original_globalFunctional_prescribed_boundary z L e
  let : Algebra Γ(X, ⊤) Γ(Z, ⊤) := z.appTop.hom.toAlgebra
  let U := Spec (.of (Localization.Away r))
  let j : U ⟶ Spec Γ(X, ⊤) :=
    Spec.map (CommRingCat.ofHom (algebraMap Γ(X, ⊤) (Localization.Away r)))
  let q : Spec Γ(Z, ⊤) ⟶ U :=
    Spec.map (CommRingCat.ofHom (IsLocalization.Away.lift r (hr ▸ isUnit_one)))
  have hq : q ≫ j = Spec.map z.appTop := by
    dsimp only [q, j]
    rw [← Spec.map_comp]
    congr 1
    ext x
    exact IsLocalization.Away.lift_eq r (hr ▸ isUnit_one) x
  let v := j ≫ X.isoSpec.inv
  let b := Z.isoSpec.hom ≫ q
  have hb : b ≫ v = z := by
    dsimp only [b, v]
    rw [Category.assoc, ← Category.assoc q, hq, ← Category.assoc,
      Scheme.isoSpec_hom_naturality, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have : IsIso (pullbackUnitMap v F) := hi
  obtain ⟨d, hd⟩ := exists_unitIso_of_globalFunctional v b z hb L.val e F hF
  exact ⟨U, inferInstance, v, inferInstance, b, hb, d, hd⟩

end AlgebraicGeometry.Scheme.Modules.Invertible
