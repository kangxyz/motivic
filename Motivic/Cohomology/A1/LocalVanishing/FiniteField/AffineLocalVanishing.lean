/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.LocalVanishing.FiniteField.ScalarPresentationLocalZero
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Presentation.Quadratic.LargePrimeOriginalEtalePresentation
public import Motivic.Aglib.RingTheory.Kaehler.SmoothCotangentTrdeg

/-! # Finite-field closed-point zeros from actual two-prime presentations

The identity etale diagram is fed to the geometric producer. Its two actual
presentations and unique entire closed fibers give scalar zero neighborhoods;
actual coprime scalar traces descend these to one original affine neighborhood.
No presentation family, scalar zero family, or presheaf separation is assumed.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic Module
open _root_.AlgebraicGeometry.PolynomialOpenQuotient.Laurent
open _root_.AlgebraicGeometry.Scheme.PolynomialLaurent
open _root_.AlgebraicGeometry.Scheme.SmoothSite
open QuadraticIncidence.InfinityChart
open scoped TensorProduct

universe u w

namespace Motivic.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme (SmoothSite)

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Positive-dimensional closed-point local vanishing over a finite field.
The finite generators, residue basis, prime characteristic and both actual
presentations are constructed from the original smooth affine domain. -/
theorem exists_finite_affine_zero_neighborhood_of_positive_trdeg
    (k B : Type u) [Field k] [Finite k] [CommRing B] [IsDomain B]
    [Algebra k B] [Algebra.Smooth k B]
    (x : PrimeSpectrum B) [x.asIdeal.IsMaximal]
    (J : Ideal B) (hJ : J ≠ ⊥) (d : ℕ)
    (hd : Algebra.trdeg k B = (d + 1 : ℕ))
    {A : SmoothSite (Spec (.of k))} [IsAffine A.left]
    (a : A ⟶ affineSite k B) [IsOpenImmersion a.left]
    (ha : Disjoint (Set.range a.left)
      (Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))))
    (hcover : ∀ y : Spec (.of B), y ∈ Set.range a.left ∨
      y ∈ Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))))
    (P : PresheafWithTransfers.{w} k) (hP : P.IsA1Invariant)
    (v : P.sections (Cor.mk (affineSite k B)))
    (hv : P.transfer ((Cor.graphFunctor k).map a) v = 0) :
    ∃ (O : (Spec (.of B)).Opens) (hO : IsAffineOpen O), x ∈ O ∧
      let : IsAffine O.toScheme := hO
      P.transfer ((Cor.graphFunctor k).map
        (homMk (X := mk (O.ι ≫ (affineSite k B).hom))
          (Y := affineSite k B) O.ι rfl)) v = 0 := by
  classical
  let ℓ := ringChar k
  let : Fact ℓ.Prime := ⟨CharP.prime_ringChar k⟩
  obtain ⟨G, hG⟩ := Algebra.FiniteType.out (R := k) (A := B)
  have hg : Algebra.adjoin k (Set.range (fun t : G => (t : B))) = ⊤ := by
    convert hG using 1
    congr 1
    ext b
    simp
  have hdim : Module.finrank x.asIdeal.ResidueField
      (x.asIdeal.ResidueField ⊗[B] KaehlerDifferential k B) = d + 1 := by
    rw [Algebra.residue_cotangent_finrank_eq_trdeg_toNat k B x.asIdeal,
      hd, Cardinal.toNat_natCast]
  obtain ⟨_, basis, _⟩ := KaehlerDifferential.exists_residue_basis_fin_original_functions
    k B x.asIdeal.ResidueField (d + 1) hdim
  let z := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))
  have : IsClosedImmersion z :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have H : IsPullback z (𝟙 _) (𝟙 _) z := IsPullback.of_vert_isIso ⟨by simp⟩
  obtain ⟨n, m, hn, hm, hcoprime, hdata⟩ :=
    exists_two_prime_originalEtalePresentations k B ℓ x J hJ
      (fun t : G => (t : B)) hg d hd basis (𝟙 _) a.left z
      (by simp only [Category.comp_id]; rfl) H ha hcover 0
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let : NeZero m := ⟨Nat.ne_of_gt hm⟩
  let E := ULift.{u} (FiniteField.Extension k ℓ n)
  let L := ULift.{u} (FiniteField.Extension k ℓ m)
  obtain ⟨hdegE, hdomE, hE⟩ := hdata n (Or.inl rfl)
  obtain ⟨hdegL, hdomL, hL⟩ := hdata m (Or.inr rfl)
  let : IsDomain (B ⊗[k] E) := hdomE
  let : IsDomain (B ⊗[k] L) := hdomL
  let : Algebra.Smooth E (B ⊗[k] E) :=
    Algebra.Smooth.of_equiv (Algebra.TensorProduct.commRight k E B)
  let : Algebra.Smooth L (B ⊗[k] L) :=
    Algebra.Smooth.of_equiv (Algebra.TensorProduct.commRight k L B)
  obtain ⟨yE, _hyE, huE, ⟨eE⟩⟩ := hE
  obtain ⟨yL, _hyL, huL, ⟨eL⟩⟩ := hL
  have := @IsClosedImmersion.spec_of_quotient_mk (.of (B ⊗[k] E))
    (J.map (algebraMap B (B ⊗[k] E)))
  have := @IsClosedImmersion.spec_of_quotient_mk (.of (B ⊗[k] L))
    (J.map (algebraMap B (B ⊗[k] L)))
  obtain ⟨V, hxV, hzV⟩ := exists_scalar_zero_open_of_affine_presentation
    (L := E) a P hP v hv x yE huE _ _ _ eE
  obtain ⟨W, hxW, hzW⟩ := exists_scalar_zero_open_of_affine_presentation
    (L := L) a P hP v hv x yL huL _ _ _ eL
  have hdegrees : (Module.finrank k E).Coprime (Module.finrank k L) := by
    rw [hdegE, hdegL]
    exact hcoprime
  obtain ⟨O, hO, hxO, hz⟩ :=
    exists_affine_zero_open_of_coprime_scalar_zero_opens P (affineSite k B) v x
      V W hxV hxW hzV hzW hdegrees
  exact ⟨O, hO, hxO, hz⟩

end Motivic.PresheafWithTransfers
