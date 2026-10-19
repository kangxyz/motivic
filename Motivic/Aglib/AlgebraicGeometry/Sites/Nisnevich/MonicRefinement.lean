/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Nisnevich.GenericSection
public import Motivic.Aglib.AlgebraicGeometry.AffineLine.Open.AffineLineOpenMonicShrinking
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Sections.MonicNisnevichSectionSpread
public import Motivic.Aglib.AlgebraicGeometry.Spec.PolynomialQuotient.PolynomialQuotientComplement
public import Mathlib.RingTheory.Localization.Algebra

/-!
# A monic refinement of an original Nisnevich cover

After two nonzero principal restrictions of the base, the original cover has a
section on the complement of a monic divisor and an étale refinement isomorphic
over the entire closed divisor. The quotient is not reduced, and the ambient
scheme remains the whole polynomial line. This is geometric cover refinement,
not descent or whole-cylinder lifting for transfer coefficients.


Intended upstream module: `Aglib.AlgebraicGeometry.Sites.Nisnevich.MonicRefinement`.
Incoming project consumers:
`Motivic.Transfers.Presheaf.Sheafification.Representatives.Distinguished`.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial TopologicalSpace
open AlgebraicGeometry.Scheme.GenericSection AlgebraicGeometry.PolynomialOpenQuotient

universe u

namespace AlgebraicGeometry.Nisnevich

attribute [local instance] Polynomial.algebra

private theorem lineAwayMap_isOpenImmersion (R : Type u) [CommRing R] (r : R) :
    IsOpenImmersion (lineAwayMap R r) := by
  let : IsLocalization.Away (C r : R[X]) (Localization.Away r)[X] := by
    simpa only [Submonoid.map_powers] using
      (Polynomial.isLocalization (Submonoid.powers r) (Localization.Away r))
  exact IsOpenImmersion.of_isLocalization (S := (Localization.Away r)[X]) (C r)

/-- Both pieces factor through the original cover. The closed-fibre assertion is
an isomorphism on the full mapped polynomial quotient, not pointwise agreement. -/
theorem exists_monic_refinement (R : Type u) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] {Y : Scheme.{u}} (q : Y ⟶ Spec (.of R[X]))
    (hq : Presieve.singleton q ∈ _root_.AlgebraicGeometry.Nisnevich.precoverage (Spec (.of R[X]))) :
    ∃ r : R, r ≠ 0 ∧ ∃ p : (Localization.Away r)[X], p.Monic ∧
      ∃ t : Localization.Away r, t ≠ 0 ∧
        let f := p.map (algebraMap (Localization.Away r) (Localization.Away t))
        let b := lineAwayMap (Localization.Away r) t ≫ lineAwayMap R r
        ∃ (V : Scheme.{u}) (v : V ⟶ Spec (.of (Localization.Away t)[X]))
          (a : V ⟶ Y), Etale v ∧ IsOpenImmersion a ∧ a ≫ q = v ≫ b ∧
          IsIso (pullback.snd v (inclusion f)) ∧
          ∃ s : (principalOpen f).toScheme ⟶ Y,
            s ≫ q = (principalOpen f).ι ≫ b := by
  let : Etale q := (mem_precoverage_iff.mp hq).1 q (Presieve.singleton_self q)
  obtain ⟨W, hW, s, hs⟩ := _root_.AlgebraicGeometry.Nisnevich.exists_generic_open_section q hq
  obtain ⟨r, hr, g, hg, _, hsub⟩ :=
    AffineLineOpenMonicShrinking.exists_monic_punctured_open R W ⟨_, hW⟩
  let A := Localization.Away r
  let : IsDomain A := Localization.Away.isDomain hr
  let p : A[X] := X * g
  have hp : p.Monic := monic_X.mul hg
  let b₁ := lineAwayMap R r
  let : IsOpenImmersion b₁ := lineAwayMap_isOpenImmersion R r
  let q₁ := pullback.snd q b₁
  have hq₁ : Presieve.singleton q₁ ∈ _root_.AlgebraicGeometry.Nisnevich.precoverage _ := by
    simpa only [Presieve.pullback_singleton] using
      Precoverage.pullbackArrows_mem b₁ hq
  obtain ⟨t, ht, c, hc⟩ := exists_monic_lift_after_localization A p hp q₁ hq₁
  let f := p.map (algebraMap A (Localization.Away t))
  let b₂ := lineAwayMap A t
  let : IsOpenImmersion b₂ := lineAwayMap_isOpenImmersion A t
  let q₂ := pullback.snd q₁ b₂
  let z := inclusion f
  let c' : _ ⟶ pullback q₂ z := pullback.lift c (𝟙 _) (by simpa using hc)
  have hc' : c' ≫ pullback.snd q₂ z = 𝟙 _ := pullback.lift_snd _ _ _
  obtain ⟨V, hV⟩ := Scheme.Hom.exists_open_iso_over_closed_of_section q₂ z c' hc'
  let a := V.ι ≫ pullback.fst q₁ b₂ ≫ pullback.fst q b₁
  have ha : a ≫ q = (V.ι ≫ q₂) ≫ (b₂ ≫ b₁) := by
    simp only [a, q₂, q₁, Category.assoc, pullback.condition_assoc, pullback.condition]
  let U := principalOpen f
  have hU : Set.range (U.ι ≫ b₂ ≫ b₁) ⊆ Set.range W.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    apply hsub
    exact x.property
  let d : U.toScheme ⟶ W.toScheme := IsOpenImmersion.lift W.ι (U.ι ≫ b₂ ≫ b₁) hU
  refine ⟨r, hr, p, hp, t, ht, V.toScheme, V.ι ≫ q₂, a,
    inferInstance, inferInstance, ha, hV, d ≫ s, ?_⟩
  rw [Category.assoc, hs]
  exact IsOpenImmersion.lift_fac _ _ _

end AlgebraicGeometry.Nisnevich
