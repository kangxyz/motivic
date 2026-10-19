/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.TensorProduct.PolynomialRelations
public import Mathlib.RingTheory.Localization.Algebra
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Unramified.Basic

/-!
# The actual local diagonal kernel in unramified polynomial coordinates

For an essentially finite type, formally unramified polynomial algebra `S`,
the coordinate differences generate the kernel of the actual localized
multiplication map `(S ⊗[R] S)_q → S_p`, where `q` is the inverse image of `p`.
The proof uses the explicit relative tensor quotient and an idempotent generator
of the relative diagonal kernel. Its complementary element becomes a unit at
the diagonal point. The coefficient rings may have nilpotents.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

namespace Algebra.TensorProduct.RelativePolynomial

section SurjectiveMaps

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]

/-- After localizing at a point over `C`, an idempotent-generated relative kernel disappears. -/
theorem ker_localRingHom_comp_of_idempotent
    (f : A →+* B) (g : B →+* C) (hf : Function.Surjective f)
    (hg : Function.Surjective g) (e : B) (he : IsIdempotentElem e)
    (hker : RingHom.ker g = Ideal.span {e}) (p : Ideal C) [p.IsPrime] :
    RingHom.ker (Localization.localRingHom (p.comap (g.comp f)) p (g.comp f) rfl) =
      (RingHom.ker f).map (algebraMap A (Localization.AtPrime (p.comap (g.comp f)))) := by
  rw [Localization.localRingHom, IsLocalization.ker_map _ _
    (p.map_primeCompl_comap_of_surjective (g.comp f) (hg.comp hf))]
  obtain ⟨a, ha⟩ := hf e
  have hge : g e = 0 := by
    change e ∈ RingHom.ker g
    rw [hker]
    exact Ideal.subset_span (Set.mem_singleton e)
  apply le_antisymm
  · apply Ideal.map_le_iff_le_comap.mpr
    intro x hx
    apply (IsLocalization.algebraMap_mem_map_algebraMap_iff
      (p.comap (g.comp f)).primeCompl _ (RingHom.ker f) x).mpr
    refine ⟨1 - a, ?_, ?_⟩
    · change g (f (1 - a)) ∉ p
      simpa [ha, hge] using p.one_notMem
    · have hfx : f x ∈ Ideal.span {e} := by
        rw [← hker]
        exact hx
      obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hfx
      change f ((1 - a) * x) = 0
      rw [map_mul, map_sub, map_one, ha, ← hb, mul_left_comm, he.one_sub_mul_self, mul_zero]
  · apply Ideal.map_mono
    intro x hx
    change g (f x) = 0
    rw [show f x = 0 from hx, map_zero]

end SurjectiveMaps

variable (R σ S : Type*) [CommRing R] [CommRing S] [Algebra R S]
  [Algebra (MvPolynomial σ R) S] [IsScalarTower R (MvPolynomial σ R) S]

/-- The canonical map to the relative tensor product is surjective. -/
theorem toRelative_surjective : Function.Surjective (toRelative R σ S) := by
  intro y
  obtain ⟨x, hx⟩ := (quotientEquiv R σ S).surjective y
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨x, hx⟩

/-- The actual multiplication map of the absolute tensor square. -/
abbrev multiplication : S ⊗[R] S →+* S :=
  (Algebra.TensorProduct.lmul' R).toRingHom

/-- The actual prime of the tensor square lying over the chosen diagonal point. -/
def diagonalPrime (p : Ideal S) : Ideal (S ⊗[R] S) := p.comap (multiplication R S)

instance diagonalPrime_isPrime (p : Ideal S) [p.IsPrime] : (diagonalPrime R S p).IsPrime :=
  Ideal.IsPrime.comap _

/-- Localizing tensor multiplication at the diagonal point gives the actual local ring map. -/
def localMultiplication (p : Ideal S) [p.IsPrime] :
    Localization.AtPrime (diagonalPrime R S p) →+* Localization.AtPrime p :=
  Localization.localRingHom (diagonalPrime R S p) p (multiplication R S) rfl

@[simp]
theorem localMultiplication_algebraMap (p : Ideal S) [p.IsPrime] (x : S ⊗[R] S) :
    localMultiplication R S p (algebraMap _ _ x) =
      algebraMap S (Localization.AtPrime p) (multiplication R S x) :=
  Localization.localRingHom_to_map _ _ _ _ x

/-- In unramified polynomial coordinates the coordinate ideal is the local diagonal kernel. -/
theorem ker_localMultiplication
    [Algebra.EssFiniteType (MvPolynomial σ R) S]
    [Algebra.FormallyUnramified (MvPolynomial σ R) S]
    (p : Ideal S) [p.IsPrime] :
    RingHom.ker (localMultiplication R S p) =
      (ideal R σ S).map (algebraMap (S ⊗[R] S)
        (Localization.AtPrime (diagonalPrime R S p))) := by
  obtain ⟨e, he, hker⟩ : ∃ e, IsIdempotentElem e ∧
      KaehlerDifferential.ideal (MvPolynomial σ R) S = Ideal.span {e} :=
    (Ideal.isIdempotentElem_iff_of_fg _
      (KaehlerDifferential.ideal_fg (MvPolynomial σ R) S)).mp <|
        (Ideal.cotangent_subsingleton_iff _).mp <| inferInstanceAs <|
          Subsingleton (KaehlerDifferential (MvPolynomial σ R) S)
  have hmul :
      (Algebra.TensorProduct.lmul' (MvPolynomial σ R) :
        S ⊗[MvPolynomial σ R] S →ₐ[MvPolynomial σ R] S).toRingHom.comp
        (toRelative R σ S).toRingHom = multiplication R S :=
    congrArg AlgHom.toRingHom (lmul_comp_toRelative R σ S)
  have hs : Function.Surjective (Algebra.TensorProduct.lmul' (MvPolynomial σ R) :
      S ⊗[MvPolynomial σ R] S →ₐ[MvPolynomial σ R] S) :=
    fun s => ⟨s ⊗ₜ 1, by simp⟩
  have h := ker_localRingHom_comp_of_idempotent (toRelative R σ S).toRingHom
    (Algebra.TensorProduct.lmul' (MvPolynomial σ R)).toRingHom
    (toRelative_surjective R σ S) hs e he hker p
  rw [hmul] at h
  have hk : RingHom.ker (toRelative R σ S).toRingHom = ideal R σ S :=
    ker_toRelative R σ S
  rw [hk] at h
  exact h

end Algebra.TensorProduct.RelativePolynomial
