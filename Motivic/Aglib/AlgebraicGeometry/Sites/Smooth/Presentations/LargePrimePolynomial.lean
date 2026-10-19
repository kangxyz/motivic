/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Presentation.Quadratic.LargePrimePolynomialZeroOriginalEtalePresentation
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Presentations.ScalarPolynomialZeroFiber
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Pullbacks

/-! # Actual two-prime polynomial presentations in the original native scalar sites

The original integral-affine whole-zero diagram produces both presentations.
All coordinate changes are canonical, the mapped nonreduced closed quotient is
literal, and the full zero lift is separate from closed-point fiber uniqueness.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.RelativeCurve AlgebraicGeometry.PolynomialOpenQuotient
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates

open _root_.AlgebraicGeometry.PolynomialOpenQuotient.Laurent
open _root_.AlgebraicGeometry.Scheme.PolynomialLaurent
open _root_.AlgebraicGeometry.Scheme.SmoothSite
open _root_.AlgebraicGeometry.PolynomialOpenQuotient.SmoothSite
open QuadraticIncidence.InfinityChart

variable (k R L : Type u) [Field k] [CommRing R] [Field L]
  [Algebra k R] [Algebra k L] [Algebra.Smooth k R]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

local instance : Algebra.Smooth L (R ⊗[k] L) :=
  Algebra.Smooth.of_equiv (Algebra.TensorProduct.commRight k L R)

local instance : Algebra.Smooth k (Polynomial R) := by
  let : Algebra.Smooth R (Polynomial R) := {}
  exact Algebra.Smooth.comp k R (Polynomial R)

local instance : Algebra.Smooth L ((Polynomial R) ⊗[k] L) :=
  Algebra.Smooth.of_equiv (Algebra.TensorProduct.commRight k L (Polynomial R))

/-- A literal whole-zero lift has its forced original smooth-site structure. -/
def polynomialZeroLiftSite {Y : SmoothSite (Spec (.of k))}
    (p : Y ⟶ lineSite (k := k) (R := R)) (s₀ : Spec (.of R) ⟶ Y.left)
    (hs₀ : s₀ ≫ p.left = Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) :
    affineSite k R ⟶ Y :=
  homMk s₀ (by
    have h := MorphismProperty.Over.w
      (a1Section (.of k) (affineSite k R) 0 ≫
        (lineCylinderIso (k := k) (R := R)).inv)
    rw [polynomial_zero_left] at h
    calc
      s₀ ≫ Y.hom = s₀ ≫ p.left ≫ (lineSite (k := k) (R := R)).hom := by
        rw [MorphismProperty.Over.w]
      _ = Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R))) ≫
          (lineSite (k := k) (R := R)).hom := by rw [← Category.assoc, hs₀]
      _ = (affineSite k R).hom := h)

/-- The full original lift retains the literal zero map as a smooth-site equation. -/
@[reassoc]
theorem polynomialZeroLiftSite_eq {Y : SmoothSite (Spec (.of k))}
    (p : Y ⟶ lineSite (k := k) (R := R)) (s₀ : Spec (.of R) ⟶ Y.left)
    (hs₀ : s₀ ≫ p.left = Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) :
    polynomialZeroLiftSite k R p s₀ hs₀ ≫ p =
      a1Section (.of k) (affineSite k R) 0 ≫
        (lineCylinderIso (k := k) (R := R)).inv := by
  apply MorphismProperty.Over.Hom.ext
  change s₀ ≫ p.left = _
  rw [polynomial_zero_left]
  exact hs₀

/-- The original full polynomial-zero diagram gives actual native presentations
and whole scalar zero lifts over the same two coprime prime extensions. -/
theorem exists_two_prime_nativePolynomial_presentations
    [Finite k] [IsDomain R]
    (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ]
    (w : Spec (.of R))
    [(PrimeSpectrum.comap (Polynomial.evalRingHom (0 : R)) w).asIdeal.IsMaximal]
    {Y : SmoothSite (Spec (.of k))} [IsAffine Y.left]
    (p : Y ⟶ lineSite (k := k) (R := R)) [Etale p.left]
    (s₀ : Spec (.of R) ⟶ Y.left)
    (hs₀ : s₀ ≫ p.left = Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R))))
    (H₀ : IsPullback s₀ (𝟙 _) p.left
      (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))))
    (N₀ : ℕ) :
    let pA := (p ≫ (polynomialAffineIso k R).hom).left
    let J : Ideal (Polynomial R) := Ideal.span {Polynomial.X}
    let s := source (Polynomial.X : Polynomial R) ≫ s₀
    let hs : s ≫ pA = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) := by
      change (source (Polynomial.X : Polynomial R) ≫ s₀) ≫ (p.left ≫ 𝟙 _) =
        inclusion (Polynomial.X : Polynomial R)
      rw [Category.comp_id, Category.assoc, hs₀, polynomial_zero_quotient_inclusion]
    ∃ n m : ℕ, N₀ < n ∧ N₀ < m ∧ n.Coprime m ∧
      ∀ (r : ℕ) [NeZero r], r = n ∨ r = m →
        let L := ULift.{u} (FiniteField.Extension k ℓ r)
        let S := (Polynomial R) ⊗[k] L
        let F := fieldBaseChange (algebraMap k L)
        let pL := F.map p ≫ (scalarLineIso k R L).hom
        let z := Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk (J.map (algebraMap (Polynomial R) S))))
        let σ := Scheme.quotientBaseChangeEtaleLift (Polynomial R) S J pA s hs
        Module.finrank k L = r ∧ IsAffine (F.obj Y).left ∧ Etale pL.left ∧
          ∃ wL : Spec (.of (R ⊗[k] L)),
            Spec.map (CommRingCat.ofHom (algebraMap R (R ⊗[k] L))) wL = w ∧
            (∀ v : Spec (.of (R ⊗[k] L)),
              Spec.map (CommRingCat.ofHom (algebraMap R (R ⊗[k] L))) v = w → v = wL) ∧
            Nonempty (OriginalEtalePresentation L
              (lineSite (k := L) (R := R ⊗[k] L)).hom pL.left
              (openInclusion (k := L) (Polynomial.X : Polynomial (R ⊗[k] L))).left
              (z ≫ (tensorPolynomialLineIso k R L).hom.left)
              (σ ≫ (scalarPolynomialSourceIso k R L p).inv)
              (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R ⊗[k] L))) wL)) ∧
            ((affineScalarIso k R L).inv ≫
              F.map (polynomialZeroLiftSite k R p s₀ hs₀)).left ≫ pL.left =
                Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R ⊗[k] L))) := by
  let pA := (p ≫ (polynomialAffineIso k R).hom).left
  have hpA : pA = p.left := by
    change p.left ≫ 𝟙 _ = p.left
    exact Category.comp_id _
  have : Etale pA := hpA.symm ▸ inferInstance
  have hsA : s₀ ≫ pA = Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R))) := by
    rw [hpA, hs₀]
  have HA : IsPullback s₀ (𝟙 _) pA
      (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) := hpA.symm ▸ H₀
  obtain ⟨n, m, hn, hm, hnm, hdata⟩ :=
    exists_two_prime_polynomialZero_originalEtalePresentations k R ℓ
      (PrimeSpectrum.comap (Polynomial.evalRingHom (0 : R)) w) pA s₀ hsA HA N₀
  refine ⟨n, m, hn, hm, hnm, ?_⟩
  intro r _ hr
  let L := ULift.{u} (FiniteField.Extension k ℓ r)
  let F := fieldBaseChange (algebraMap k L)
  let S := (Polynomial R) ⊗[k] L
  let ρ := Spec.map (CommRingCat.ofHom (algebraMap (Polynomial R) S))
  let a := openInclusion (k := k) (Polynomial.X : Polynomial R)
  have ha : (a ≫ (polynomialAffineIso k R).hom).left = a.left := by
    change a.left ≫ 𝟙 _ = a.left
    exact Category.comp_id _
  have : IsOpenImmersion a.left := inferInstanceAs (IsOpenImmersion
    (Scheme.Opens.ι (X := Spec (.of (Polynomial R))) (PrimeSpectrum.basicOpen Polynomial.X)))
  have : IsOpenImmersion (a ≫ (polynomialAffineIso k R).hom).left := by rw [ha]; infer_instance
  obtain ⟨hdeg, _hdom, y, _hy, hu, ⟨e⟩⟩ := hdata r hr
  obtain ⟨wL, hwL, huniq, hpoint⟩ := exists_unique_scalar_zero_point k R L w y hu
  let e' := e.withPuncture (pullback.snd (a ≫ (polynomialAffineIso k R).hom).left ρ)
    (by rw [ha]; rfl)
  let eN := nativeScalarPolynomialPresentation k R L p _ _ y e'
  have heN := eN
  rw [hpoint] at heN
  have hpL : Etale (F.map p ≫ (scalarLineIso k R L).hom).left := by
    rw [← scalarPolynomialSourceIso_native]
    infer_instance
  let : IsAffine ((𝟭 Scheme).obj Y.left) := inferInstanceAs (IsAffine Y.left)
  let : IsAffine ((Functor.fromPUnit (Spec (.of k))).obj Y.right) :=
    inferInstanceAs (IsAffine (Spec (.of k)))
  refine ⟨hdeg, Scheme.Pullback.isAffine_of_isAffine_isAffine_isAffine Y.hom
    (Spec.map (CommRingCat.ofHom (algebraMap k L))), hpL, wL, hwL, huniq, ⟨heN⟩, ?_⟩
  have h := congrArg (fun f => f.left) (scalarLineIso_wholeSection k R L p
    (polynomialZeroLiftSite k R p s₀ hs₀) (polynomialZeroLiftSite_eq k R p s₀ hs₀))
  rw [polynomial_zero_left] at h
  simpa only [MorphismProperty.Comma.comp_left, Category.assoc] using h

end AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates
