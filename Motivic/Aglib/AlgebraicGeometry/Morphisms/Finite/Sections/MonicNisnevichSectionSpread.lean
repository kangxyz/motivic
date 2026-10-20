/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Sections.MonicGenericSectionSpread
public import Motivic.Aglib.AlgebraicGeometry.Spec.PolynomialQuotient.PolynomialQuotientTargetBaseChange
public import Motivic.Aglib.AlgebraicGeometry.Sites.Nisnevich.Lifting.ArtinianNeighborhood

/-! # A genuine Nisnevich cover splits over the whole monic divisor after base localization -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Polynomial
universe u
namespace AlgebraicGeometry.Scheme.GenericSection
open PolynomialOpenQuotient
variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]

/-- The affine-line coefficient map `Spec R[1/r][X] ⟶ Spec R[X]` induced by
localization at `r`. -/
abbrev lineAwayMap (r : R) : Spec (.of (Localization.Away r)[X]) ⟶ Spec (.of R[X]) :=
  Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap R (Localization.Away r))))

/-- The original quotient inclusion commutes with the literal polynomial scalar map. -/
lemma coefficient_inclusion {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (p : A[X]) :
    coefficientMap φ p ≫ inclusion p =
      inclusion (p.map φ) ≫ Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom φ)) := by
  unfold coefficientMap inclusion
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact coefficient_mk φ p r

/-- The whole mapped quotient is canonically the actual localized original fibre. -/
def monicAwayIso (p : R[X]) (r : R) :
    Spec (.of (AdjoinRoot (p.map (algebraMap R (Localization.Away r))))) ≅
      awayFiber R (AdjoinRoot p) r :=
  (coefficient_isPullback (algebraMap R (Localization.Away r)) p).flip.isoPullback

omit [IsDomain R] [IsNoetherianRing R] in
@[reassoc (attr := simp)]
lemma monicAwayIso_hom_fst (p : R[X]) (r : R) :
    (monicAwayIso R p r).hom ≫ pullback.fst (baseMap R (AdjoinRoot p)) (awayMap R r) =
      coefficientMap (algebraMap R (Localization.Away r)) p :=
  IsPullback.isoPullback_hom_fst _

/-- Nisnevich residue lifting is used only on the actual Artinian generic divisor;
its section is then spread back geometrically over the original base. -/
theorem exists_monic_lift_after_localization (p : R[X]) (hp : p.Monic)
    {Y : Scheme.{u}} (q : Y ⟶ Spec (.of R[X])) [Etale q]
    (hq : Presieve.singleton q ∈ Nisnevich.precoverage (Spec (.of R[X]))) :
    ∃ (r : R), r ≠ 0 ∧
      ∃ a : Spec (.of (AdjoinRoot (p.map (algebraMap R (Localization.Away r))))) ⟶
          pullback q (lineAwayMap R r),
        a ≫ pullback.snd q (lineAwayMap R r) =
          inclusion (p.map (algebraMap R (Localization.Away r))) := by
  have : IsFinite (baseMap R (AdjoinRoot p)) := source_finite p hp
  have : Flat (baseMap R (AdjoinRoot p)) := source_flat p hp
  have : IsLocallyArtinian (genericFiber R (AdjoinRoot p)) :=
    IsLocallyArtinian.of_locallyQuasiFinite
      (pullback.snd (baseMap R (AdjoinRoot p)) (genericMap R))
  let z := inclusion p
  let g : genericFiber R (AdjoinRoot p) ⟶ Spec (.of R[X]) :=
    pullback.fst (baseMap R (AdjoinRoot p)) (genericMap R) ≫ z
  have hl : ∀ c : genericFiber R (AdjoinRoot p),
      ∃ a : Spec ((genericFiber R (AdjoinRoot p)).residueField c) ⟶ pullback q g,
        a ≫ pullback.snd q g = (genericFiber R (AdjoinRoot p)).fromSpecResidueField c := by
    intro c
    obtain ⟨_, _, hf, b, hb⟩ := Nisnevich.mem_fieldLiftingPrecoverage_iff.mp hq.2
      ((genericFiber R (AdjoinRoot p)).residueField c)
      ((genericFiber R (AdjoinRoot p)).fromSpecResidueField c ≫ g)
    cases hf
    exact ⟨pullback.lift b ((genericFiber R (AdjoinRoot p)).fromSpecResidueField c) hb,
      pullback.lift_snd _ _ _⟩
  obtain ⟨s, hs⟩ :=
      _root_.AlgebraicGeometry.Scheme.Hom.ArtinianEtale.exists_section_of_etale_of_isLocallyArtinian
    (pullback.snd q g) hl
  let sZ : genericFiber R (AdjoinRoot p) ⟶ pullback q z :=
    pullback.lift (s ≫ pullback.fst q g)
      (pullback.fst (baseMap R (AdjoinRoot p)) (genericMap R)) (by
        rw [Category.assoc, pullback.condition, ← Category.assoc, hs, Category.id_comp])
  obtain ⟨r, hr, t, ht, _⟩ := exists_monic_section_over_away R p hp
    (pullback.snd q z) sZ (pullback.lift_snd _ _ _)
  let b := (monicAwayIso R p r).hom ≫ t ≫ pullback.fst q z
  have hb : b ≫ q = inclusion (p.map (algebraMap R (Localization.Away r))) ≫
      lineAwayMap R r := by
    simp only [b, Category.assoc, pullback.condition]
    rw [← Category.assoc t, ht, ← Category.assoc, monicAwayIso_hom_fst]
    exact coefficient_inclusion _ p
  exact ⟨r, hr, pullback.lift b (inclusion (p.map (algebraMap R (Localization.Away r)))) hb,
    pullback.lift_snd _ _ _⟩

end AlgebraicGeometry.Scheme.GenericSection
