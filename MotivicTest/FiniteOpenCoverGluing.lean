/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Modules.FiniteOpenCoverGluingSigned
public import MotivicTest.OpenCoverGluing
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.AlgebraicGeometry.Properties

/-!
# Three-open signed finite-descent consumers

The actual affine opens D(r), D(1-r), and D(r(1-r)) form a three-member
cover. The signed transitions satisfy the ordinary triple cocycle; their
finite equalizer sheaf has all three local inverses and actual refinements.
For the rational affine line, the transition between the first two opens is
proved different from the canonical transition on an inhabited overlap.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.MotivicTest.FiniteOpenCoverGluing

open Scheme.Modules Motivic.FiniteOpenModuleGluing

variable (R : CommRingCat.{0}) (r : R)

/-- Three actual principal affine opens, including their genuine triple overlap. -/
def threeOpens (i : Fin 3) : (Spec R).Opens :=
  if i = 0 then PrimeSpectrum.basicOpen r
  else if i = 1 then PrimeSpectrum.basicOpen (1 - r)
  else PrimeSpectrum.basicOpen (r * (1 - r))

/-- The first two of the three actual opens already cover the affine spectrum. -/
theorem threeOpens_cover : ⨆ i, threeOpens R r i = ⊤ := by
  apply top_unique
  rw [← OpenCoverGluing.principal_cover R r]
  apply sup_le
  · simpa [threeOpens, OpenCoverGluing.firstOpen] using le_iSup (threeOpens R r) 0
  · simpa [threeOpens, OpenCoverGluing.secondOpen] using le_iSup (threeOpens R r) 1

/-- All three members of the actual covering family are affine. -/
theorem threeOpens_affine (i : Fin 3) : IsAffineOpen (threeOpens R r i) := by
  by_cases h₀ : i = 0
  · simpa [threeOpens, h₀] using IsAffineOpen.Spec_basicOpen r
  · by_cases h₁ : i = 1
    · simpa [threeOpens, h₀, h₁] using IsAffineOpen.Spec_basicOpen (1 - r)
    · simpa [threeOpens, h₀, h₁] using IsAffineOpen.Spec_basicOpen (r * (1 - r))

/-- The actual structure module supplies the local coefficient action. -/
abbrev structureModule : (Spec R).Modules := SheafOfModules.unit (Spec R).ringCatSheaf

/-- The original module sheaves on all three covering schemes. -/
abbrev localModules (i : Fin 3) : (threeOpens R r i).toScheme.Modules :=
  (restrictFunctor (threeOpens R r i).ι).obj (structureModule R)

/-- Only the first local trivialization changes sign. -/
def localSigns (i : Fin 3) : Bool := decide (i = 0)

/-- Genuine signed descent data with its standard cocycle proved by the construction. -/
def threeDatum : Datum (threeOpens R r) (localModules R r) :=
  signedDatum _ _ (canonicalDatum (threeOpens R r) (structureModule R)) localSigns

/-- The constructed finite-family module sheaf on the entire affine spectrum. -/
def threeGlued : (Spec R).Modules := glued _ _ (threeDatum R r)

/-- Every one of the three local modules is recovered by the actual inverse. -/
def threeLocalIso (i : Fin 3) :
    (restrictFunctor (threeOpens R r i).ι).obj (threeGlued R r) ≅ localModules R r i :=
  localIso _ _ (threeDatum R r) i

/-- The actual triple-overlap cocycle is consumed on every common smaller open. -/
theorem three_cocycle (W : (Spec R).Opens) (hi : W ≤ threeOpens R r 0)
    (hj : W ≤ threeOpens R r 1) (hk : W ≤ threeOpens R r 2) :
    transitionOn _ _ (threeDatum R r).transition 0 1 hi hj ≪≫
      transitionOn _ _ (threeDatum R r).transition 1 2 hj hk =
        transitionOn _ _ (threeDatum R r).transition 0 2 hi hk :=
  (threeDatum R r).cocycle W 0 1 2 hi hj hk

set_option backward.isDefEq.respectTransparency false in
/-- A genuine further restriction inside all three members retains its original module. -/
def tripleRefinementIso :
    (restrictFunctor ((Spec R).homOfLE (show
      threeOpens R r 0 ⊓ threeOpens R r 1 ⊓ threeOpens R r 2 ≤ threeOpens R r 0 from
        inf_le_left.trans inf_le_left) ≫ (threeOpens R r 0).ι)).obj (threeGlued R r) ≅
      (restrictFunctor ((Spec R).homOfLE (show
        threeOpens R r 0 ⊓ threeOpens R r 1 ⊓ threeOpens R r 2 ≤ threeOpens R r 0 from
          inf_le_left.trans inf_le_left))).obj (localModules R r 0) :=
  localRefinementIso (threeOpens R r) (localModules R r) (threeDatum R r) 0
    ((Spec R).homOfLE (inf_le_left.trans inf_le_left))

/-- The first transition contains a literal nontrivial sign. -/
theorem transition_01_signed : ((threeDatum R r).transition 0 1).hom =
    -(canonicalTransition (threeOpens R r) (structureModule R) 0 1).hom := by
  simp [threeDatum, signedDatum, signedTransition, localSigns, canonicalDatum, negatedIso]

/-- The rational affine line provides an inhabited, nontrivial triple-overlap example. -/
abbrev rationalPolynomialRing : CommRingCat := CommRingCat.of (Polynomial ℚ)

/-- The generic point lies in the overlap of the first two proper principal opens. -/
theorem polynomial_overlap_nonempty : Nonempty
    ↥(threeOpens rationalPolynomialRing Polynomial.X 0 ⊓
      threeOpens rationalPolynomialRing Polynomial.X 1) := by
  let p : PrimeSpectrum (Polynomial ℚ) := ⟨⊥, inferInstance⟩
  refine ⟨⟨p, ?_⟩⟩
  change Polynomial.X ∉ p.asIdeal ∧ 1 - Polynomial.X ∉ p.asIdeal
  change Polynomial.X ≠ 0 ∧ 1 - Polynomial.X ≠ 0
  refine ⟨Polynomial.X_ne_zero, ?_⟩
  intro h
  have hc := congrArg (fun q : Polynomial ℚ => q.coeff 0) h
  simp [Polynomial.coeff_sub] at hc

/-- An actual section of the rational affine line detects negation on every inhabited open. -/
theorem polynomial_section_neg_one_ne_one (V : (Spec rationalPolynomialRing).Opens)
    [Nonempty V] : -(1 : Γ(Spec rationalPolynomialRing, V)) ≠ 1 := by
  let f : ℚ →+* Γ(Spec rationalPolynomialRing, V) :=
    ((Spec rationalPolynomialRing).presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op).hom.comp
      ((Scheme.ΓSpecIso rationalPolynomialRing).inv.hom.comp (algebraMap ℚ (Polynomial ℚ)))
  intro h
  have hh : f (-1) = f 1 := by simpa using h
  have hq := f.injective hh
  norm_num at hq

set_option backward.isDefEq.respectTransparency false in
/-- On the actual affine-line overlap the signed transition differs from the canonical one. -/
theorem polynomial_transition_nonidentity :
    ((threeDatum rationalPolynomialRing Polynomial.X).transition 0 1).hom ≠
      (canonicalTransition (threeOpens rationalPolynomialRing Polynomial.X)
        (structureModule rationalPolynomialRing) 0 1).hom := by
  let U := threeOpens rationalPolynomialRing Polynomial.X
  let a := (Spec rationalPolynomialRing).homOfLE (inf_le_left : U 0 ⊓ U 1 ≤ U 0)
  let P := (restrictFunctor a).obj (localModules rationalPolynomialRing Polynomial.X 0)
  let V : (Spec rationalPolynomialRing).Opens := (U 0).ι ''ᵁ (a ''ᵁ ⊤)
  have hV : V = U 0 ⊓ U 1 := by
    dsimp only [V, a]
    simp only [← Scheme.Hom.comp_image, Scheme.homOfLE_ι, Scheme.Opens.ι_image_top]
  have : Nonempty V := by rw [hV]; exact polynomial_overlap_nonempty
  have hneg := OpenCoverGluing.negationIso_hom_ne_id P ⊤
    (1 : Γ(Spec rationalPolynomialRing, V)) (polynomial_section_neg_one_ne_one V)
  intro h
  rw [transition_01_signed] at h
  have hh := congrArg (fun φ => φ ≫
    (canonicalTransition U (structureModule rationalPolynomialRing) 0 1).inv) h
  apply hneg
  dsimp only [U] at hh
  simpa only [OpenCoverGluing.negationIso, Preadditive.neg_comp, Iso.hom_inv_id] using hh

end Motivic.MotivicTest.FiniteOpenCoverGluing
