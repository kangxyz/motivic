/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.AffineEtaleClosedSectionNeighborhood

/-! # Whole closed neighborhoods after the actual zero-fiber base change -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.Hom

/-- Affine opens of the ambient source induce affine opens of its actual closed
fiber. The base neighborhood is on that fiber, not on the original base. -/
theorem exists_affine_open_on_closed_fiber
    {W L S : Scheme.{u}} (p : W ⟶ L) (z : S ⟶ L) [IsClosedImmersion z]
    (w : (pullback p z : Scheme)) :
    ∃ O : W.Opens, IsAffineOpen O ∧ pullback.fst p z w ∈ O ∧
      IsAffineOpen ((pullback.fst p z) ⁻¹ᵁ O) := by
  obtain ⟨O, hO, hw, _⟩ := exists_isAffineOpen_mem_and_subset
    (show pullback.fst p z w ∈ (⊤ : W.Opens) from trivial)
  exact ⟨O, hO, hw, hO.preimage (pullback.fst p z)⟩

/-- Base change along an actual closed-fiber marking supplies a diagonal section.
A principal affine refinement then becomes an isomorphism over the entire new
closed fiber, while retaining the map to the original ambient neighborhood. -/
theorem exists_affine_whole_closed_refinement
    {K W L V L' : Scheme.{u}} [IsAffine K] [IsAffine W] [IsAffine L']
    (b : L ⟶ K) [IsSeparated b]
    (p : W ⟶ L) [Etale p] [IsSeparated p]
    (j : L' ⟶ L) (z' : V ⟶ L') [IsClosedImmersion z']
    (c : V ⟶ W) (hc : c ≫ p = z' ≫ j) :
    ∃ (E : Scheme.{u}) (_ : IsAffine E) (e : E ⟶ W) (q : E ⟶ L')
      (a : V ⟶ E), Etale q ∧ QuasiCompact q ∧ IsSeparated q ∧
      e ≫ p = q ≫ j ∧ a ≫ e = c ∧ IsPullback a (𝟙 V) q z' := by
  have : IsAffineHom p := IsAffineHom.of_comp p b
  let Y := pullback p j
  let q : Y ⟶ L' := pullback.snd p j
  let s : V ⟶ Y := pullback.lift c z' hc
  have hs : s ≫ q = z' := pullback.lift_snd _ _ _
  let d : V ⟶ pullback q z' := pullback.lift s (𝟙 V) (by simpa using hs)
  have hd : d ≫ pullback.snd q z' = 𝟙 V := pullback.lift_snd _ _ _
  obtain ⟨r, a, ha, hA, hIso⟩ :=
    exists_basicOpen_iso_over_closed_of_section q z' d hd
  let A := Y.basicOpen r
  let : IsAffine A.toScheme := hA
  let : IsIso (pullback.snd (A.ι ≫ q) z') := hIso
  have ha' : a ≫ A.ι = s := by
    simpa only [d, pullback.lift_fst] using ha
  have hap : a ≫ (A.ι ≫ q) = z' := by rw [← Category.assoc, ha', hs]
  let l : V ⟶ pullback (A.ι ≫ q) z' :=
    pullback.lift a (𝟙 V) (by simpa using hap)
  have hl : l ≫ pullback.snd (A.ι ≫ q) z' = 𝟙 V := pullback.lift_snd _ _ _
  have : IsIso (l ≫ pullback.snd (A.ι ≫ q) z') := by rw [hl]; infer_instance
  have : IsIso l := IsIso.of_isIso_comp_right l (pullback.snd (A.ι ≫ q) z')
  refine ⟨A.toScheme, inferInstance, A.ι ≫ pullback.fst p j, A.ι ≫ q,
    a, inferInstance, inferInstance, inferInstance, ?_, ?_, ?_⟩
  · simp only [Category.assoc, pullback.condition]
    rfl
  · rw [← Category.assoc, ha']
    exact pullback.lift_fst _ _ _
  · exact IsPullback.of_iso_pullback ⟨by simpa using hap⟩ (asIso l)
      (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)

/-- A neighborhood on the original closed fiber, followed by its genuine base
change, retains the original marking and every point of the new closed fiber. -/
theorem exists_affine_whole_zeroFiber_refinement
    {K W L S : Scheme.{u}} [IsAffine K]
    (b : L ⟶ K) [IsSeparated b]
    (p : W ⟶ L) [Etale p] [IsSeparated p]
    (z : S ⟶ L) [IsClosedImmersion z] (w : (pullback p z : Scheme)) :
    ∃ O : W.Opens, IsAffineOpen O ∧ pullback.fst p z w ∈ O ∧
      IsAffineOpen ((pullback.fst p z) ⁻¹ᵁ O) ∧
      ∀ (L' : Scheme.{u}) [IsAffine L'] (j : L' ⟶ L)
        (z' : ((pullback.fst p z) ⁻¹ᵁ O).toScheme ⟶ L') [IsClosedImmersion z'],
        z' ≫ j = ((pullback.fst p z) ⁻¹ᵁ O).ι ≫ pullback.snd p z ≫ z →
        ∃ (E : Scheme.{u}) (_ : IsAffine E) (e : E ⟶ W) (q : E ⟶ L')
          (a : ((pullback.fst p z) ⁻¹ᵁ O).toScheme ⟶ E),
          Etale q ∧ QuasiCompact q ∧ IsSeparated q ∧ e ≫ p = q ≫ j ∧
          a ≫ e = ((pullback.fst p z) ⁻¹ᵁ O).ι ≫ pullback.fst p z ∧
          IsPullback a (𝟙 _) q z' := by
  obtain ⟨O, hO, hw, hV⟩ := exists_affine_open_on_closed_fiber p z w
  refine ⟨O, hO, hw, hV, ?_⟩
  intro L' hL' j z' hz' hcompat
  let : IsAffine O.toScheme := hO
  let c := (pullback.fst p z) ∣_ O
  have hc : c ≫ (O.ι ≫ p) = z' ≫ j := by
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, pullback.condition, hcompat]
  obtain ⟨E, hE, e, q, a, hq, hqc, hqs, he, ha, H⟩ :=
    exists_affine_whole_closed_refinement b (O.ι ≫ p) j z' c hc
  refine ⟨E, hE, e ≫ O.ι, q, a, hq, hqc, hqs, ?_, ?_, H⟩
  · simpa only [Category.assoc] using he
  · rw [← Category.assoc, ha]
    exact morphismRestrict_ι _ _

end AlgebraicGeometry.Scheme.Hom
