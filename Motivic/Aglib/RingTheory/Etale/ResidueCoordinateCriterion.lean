module
public import Motivic.Aglib.RingTheory.Etale.AdaptedPolynomialChart
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # The original polynomial coordinate map is étale near a residue basis

A basis in the actual residue cotangent fiber is lifted at the same prime.
The original chosen functions, rather than a newly selected chart, define the map.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Module TensorProduct KaehlerDifferential
universe u v
namespace Algebra

/-- Original functions whose residue differentials form a basis define an étale
polynomial map in an actual principal neighborhood of the same prime. -/
theorem exists_etale_polynomial_map_of_residue_differential_basis
    (k : Type u) (R : Type v) [Field k] [CommRing R] [Algebra k R] [Smooth k R]
    (p : Ideal R) [p.IsPrime] {d : ℕ} (g : Fin d → R)
    (bK : Basis (Fin d) (IsLocalRing.ResidueField (Localization.AtPrime p))
      (IsLocalRing.ResidueField (Localization.AtPrime p) ⊗[R] Ω[R⁄k]))
    (hbK : ∀ j, bK j = 1 ⊗ₜ[R] D k R (g j)) :
    ∃ r ∉ p, ((algebraMap R (Localization.Away r)).comp
      (MvPolynomial.aeval (R := k) g).toRingHom).Etale := by
  let Rp := Localization.AtPrime p
  let K := IsLocalRing.ResidueField Rp
  let M := Rp ⊗[R] Ω[R⁄k]
  let v : Fin d → M := fun j => 1 ⊗ₜ[R] D k R (g j)
  let E := AlgebraTensorModule.cancelBaseChange R Rp K K Ω[R⁄k]
  let bKK : Basis (Fin d) K (K ⊗[Rp] M) := bK.map E.symm
  have hbKK (j : Fin d) : bKK j = 1 ⊗ₜ[Rp] v j := by
    apply E.injective
    simp only [bKK, Basis.map_apply, hbK]
    rw [E.apply_symm_apply]
    change 1 ⊗ₜ[R] D k R (g j) = (1 : Rp) • (1 : K) ⊗ₜ[R] D k R (g j)
    rw [one_smul]
  have hli : LinearIndependent Rp v := IsLocalRing.linearIndependent_of_flat _ (by
    simpa only [Function.comp_def, TensorProduct.mk_apply, ← hbKK] using bKK.linearIndependent)
  let b : Basis (Fin d) Rp M := Basis.mk hli
    (IsLocalRing.span_eq_top_of_tmul_eq_basis _ bKK (fun j => (hbKK j).symm)).ge
  have hb (j : Fin d) : b j = 1 ⊗ₜ[R] D k R (g j) := Basis.mk_apply _ _ _
  let P := MvPolynomial (Fin d) k
  let f : P →ₐ[k] R := MvPolynomial.aeval (R := k) g
  let : Algebra P R := f.toRingHom.toAlgebra
  have : IsScalarTower k P R := .of_algebraMap_eq' f.comp_algebraMap.symm
  let e := tensorKaehlerEquivOfFormallyEtale k R Rp
  let bR := b.map e
  have hbR (j : Fin d) : bR j = D k Rp (algebraMap P Rp (.X j)) := by
    change e (b j) = _
    rw [hb]
    change mapBaseChange k R Rp (1 ⊗ₜ D k R (g j)) = _
    rw [mapBaseChange_tmul, one_smul, map_D]
    congr 1
    rw [IsScalarTower.algebraMap_apply P R Rp]
    change (algebraMap R Rp) (g j) = (algebraMap R Rp) (f (.X j))
    exact congrArg (algebraMap R Rp) (MvPolynomial.aeval_X (R := k) g j).symm
  have : FormallyEtale P Rp :=
    FormallyEtale.of_polynomial_differential_basis k Rp (Fin d) bR hbR
  have : FiniteType P R := FiniteType.of_restrictScalars_finiteType k P R
  have : FinitePresentation P R := FinitePresentation.of_finiteType.mp inferInstance
  obtain ⟨r, hr, he⟩ := exists_etale_of_isEtaleAt (R := P) p
  refine ⟨r, hr, ?_⟩
  have h := (RingHom.etale_algebraMap (R := P) (S := Localization.Away r)).mpr he
  convert h using 1

end Algebra
