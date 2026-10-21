/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Sections.Normalized.FixedOpen.FiniteFlatPair
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Sections.PairNormalization

/-! # The actual normalized fixed-open ψ pair -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u

namespace AlgebraicGeometry.Scheme.Modules.Invertible

/-- Conjugated boundary scalar action becomes literal precomposition after
normalization through the native right unitor. -/
theorem rightUnit_normalize_conjugate {X : Scheme.{u}} {T O : X.Modules}
    (v : SheafOfModules.unit X.ringCatSheaf ⟶ tensorSheaf X T O)
    (e : O ≅ SheafOfModules.unit X.ringCatSheaf)
    (c : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf) :
    v ≫ tensorSheafMap X (𝟙 T) (e.hom ≫ c ≫ e.inv) ≫
      tensorSheafMap X (𝟙 T) e.hom ≫ (tensorSheafRightUnit X T).hom =
    c ≫ v ≫ tensorSheafMap X (𝟙 T) e.hom ≫ (tensorSheafRightUnit X T).hom := by
  let σ := v ≫ tensorSheafMap X (𝟙 T) e.hom ≫ (tensorSheafRightUnit X T).hom
  have h : tensorUnitSection σ c = v ≫ tensorSheafMap X (𝟙 T) (e.hom ≫ c) :=
    tensorUnitSection_normalized v e c
  have hi : tensorUnitSection σ (𝟙 _) ≫ (tensorSheafRightUnit X T).hom = σ := by
    rw [tensorUnitSection_eq_rightUnit]
    have hid : tensorSheafMap X (𝟙 T)
        (𝟙 (SheafOfModules.unit X.ringCatSheaf)) = 𝟙 _ := by
      change (SheafOfModulesOfCommRing.associatedSheaf X.sheaf).map
        (CategoryTheory.MonoidalCategory.tensorHom (𝟙 _) (𝟙 _)) = _
      simp
      rfl
    simp only [hid, Category.comp_id, Category.assoc, Iso.inv_hom_id]
  have hc : tensorUnitSection σ c ≫ (tensorSheafRightUnit X T).hom = c ≫ σ := by
    have hh := tensorUnitSection_precomp σ (𝟙 _) c
    simp only [Category.comp_id] at hh
    rw [hh, Category.assoc, hi]
  rw [h] at hc
  rw [tensorSheafMap_comp_assoc]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact hc

end AlgebraicGeometry.Scheme.Modules.Invertible

namespace AlgebraicGeometry.Scheme.AffineLineEtaleCompactification
variable (k : Type u) [Field k] {Y : Scheme.{u}}
  (p : Y ⟶ Spec (.of (Polynomial k))) [Etale p] [QuasiCompact p] [IsSeparated p]

/-- The original fixed-open pair normalizes to actual sections of the twist
bundle, with exact full-boundary ratio and whole regular finite-flat zeros. -/
theorem exists_actualNormalizedFixedOpenPair {R : Type u} [CommRing R]
    [IsNoetherianRing R] (a : Spec (.of R) ⟶ Spec (.of (Polynomial k)))
    [IsOpenImmersion a] (B : Type u) [CommRing B] (z : Polynomial k →+* B)
    (h : Disjoint (Set.range a) (Set.range (Hom.boundaryCoordinateMap k B z)))
    [IsClosedImmersion (Hom.boundaryCoordinateMap k B z)]
    [IsFinite (Hom.boundaryCoordinateMap k B z ≫ Hom.boundaryLineProjection k)]
    (s : Spec (.of B) ⟶ Y) (hs : s ≫ p = Hom.boundaryCoordinateMap k B z)
    (H : IsPullback s (𝟙 _) p (Hom.boundaryCoordinateMap k B z))
    (U : (Spec (.of (Polynomial k))).Opens)
    (hz : Set.range (Hom.boundaryCoordinateMap k B z) =
      (U : Set (Spec (.of (Polynomial k))))ᶜ) :
    let C := fixedAmbient k p a
    let zD := fixedBoundaryMap k p a B z s hs
    let E := fixedBoundaryUnit k p a B z h
    ∃ N : ℕ, ∀ d : ℕ, N ≤ d →
      let T := fixedTwistBundle k p a d
      ∃ n t : SheafOfModules.unit C.ringCatSheaf ⟶ T.val,
        pullbackSectionMap zD n = E.hom ≫ pullbackSectionMap zD t ∧
        IsIso (pullbackSectionMap zD n) ∧ IsIso (pullbackSectionMap zD t) ∧
        FixedRetainedSectionFiniteFlat k p a U T n ∧
        FixedRetainedSectionFiniteFlat k p a U T t := by
  obtain ⟨N, hN⟩ := exists_actualFixedOpenFiniteFlatSectionPair k p a B z h s hs H U hz
  refine ⟨N, fun d hd => ?_⟩
  obtain ⟨v, hv, n, t, hn, ht, hIn, hIt, _, _⟩ := hN d hd
  let T := fixedTwistBundle k p a d
  let zD := fixedBoundaryMap k p a B z s hs
  let n0 := rightNormalizeSection T.val n
  let t0 := rightNormalizeSection T.val t
  have : IsIso (pullbackSectionMap zD n) := hIn
  have : IsIso (pullbackSectionMap zD t) := hIt
  have hn0 : IsIso (pullbackSectionMap zD n0) := by
    change IsIso ((pullbackUnitIso _).inv ≫ (Modules.pullback _).map
      (n ≫ (tensorSheafRightUnit _ T.val).hom))
    rw [CategoryTheory.Functor.map_comp, ← Category.assoc]
    infer_instance
  have ht0 : IsIso (pullbackSectionMap zD t0) := by
    change IsIso ((pullbackUnitIso _).inv ≫ (Modules.pullback _).map
      (t ≫ (tensorSheafRightUnit _ T.val).hom))
    rw [CategoryTheory.Functor.map_comp, ← Category.assoc]
    infer_instance
  refine ⟨n0, t0, ?_, hn0, ht0, ?_, ?_⟩
  · change pullbackSectionMap zD (rightNormalizeSection T.val n) =
      (fixedBoundaryUnit k p a B z h).hom ≫
        pullbackSectionMap zD (rightNormalizeSection T.val t)
    rw [pullbackSectionMap_rightNormalize, pullbackSectionMap_rightNormalize]
    have hn' : pullbackSectionMap zD n ≫ pullbackTensorMap zD T.val _ =
        v ≫ tensorSheafMap _ (𝟙 _) ((pullbackUnitIso zD).hom ≫
          (fixedBoundaryUnit k p a B z h).hom ≫ (pullbackUnitIso zD).inv) := hn
    have ht' : pullbackSectionMap zD t ≫ pullbackTensorMap zD T.val _ = v := ht
    rw [← Category.assoc, hn', Category.assoc,
      ← Category.assoc (pullbackSectionMap zD t), ht']
    exact rightUnit_normalize_conjugate v (pullbackUnitIso zD) _
  · exact actualFixedSectionDivisor_finite_mono_flat k p a B z s hs U H hz T n0
  · exact actualFixedSectionDivisor_finite_mono_flat k p a B z s hs U H hz T t0

end AlgebraicGeometry.Scheme.AffineLineEtaleCompactification
