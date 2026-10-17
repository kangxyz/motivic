module
public import Motivic.Aglib.RingTheory.FiniteEliminationDimensionRelation
public import Motivic.Aglib.RingTheory.FiniteCoordinatesDifferentialSelection

/-! # Iterated finite elimination preserving the same residue differential minors

The excess-generator count decreases. Each nonzero relation is obtained from the
actual transcendence-degree bound; each parameter is selected against the current
restrictions of the original residue functionals.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
universe u v w
namespace ParameterizedNoetherNormalization

/-- The last `d` coordinates after `e` excess generators. -/
def tailCoordinate (d e : ℕ) (j : Fin d) : Fin (d + e) := ⟨e + j.val, by omega⟩

@[simp] theorem tailCoordinate_zero (d : ℕ) (j : Fin d) : tailCoordinate d 0 j = j := by
  apply Fin.ext
  simp [tailCoordinate]

@[simp] theorem tailCoordinate_succ (d e : ℕ) (j : Fin d) :
    tailCoordinate d (e + 1) j = (tailCoordinate d e j).succ := by
  apply Fin.ext
  simp [tailCoordinate]
  omega

/-- Genuine iteration on the excess number of generators. The returned map is
into the original polynomial algebra and retains the original residue functionals. -/
theorem exists_iterated_finite_projection_preserving_differential_minors
    {k B : Type u} [Field k] [Infinite k] [CommRing B] [Algebra k B]
    (d e : ℕ) (q : MvPolynomial (Fin (d + e)) k →ₐ[k] B)
    (hq : q.Finite) (hd : Algebra.trdeg k B ≤ d)
    {ι : Type v} [Finite ι] (K : ι → Type w)
    [∀ i, Field (K i)] [∀ i, Algebra k (K i)]
    (D : (i : ι) → Fin d → MvPolynomial (Fin (d + e)) k →ₗ[k] K i)
    (hD : ∀ i, Matrix.det (fun a b => D i a (X (tailCoordinate d e b))) ≠ 0) :
    ∃ φ : MvPolynomial (Fin d) k →ₐ[k] MvPolynomial (Fin (d + e)) k,
      (q.comp φ).Finite ∧
      ∀ i, Matrix.det (fun a b => D i a (φ (X b))) ≠ 0 := by
  induction e with
  | zero =>
      refine ⟨AlgHom.id k _, hq, ?_⟩
      simpa only [tailCoordinate_zero, AlgHom.id_apply] using! hD
  | succ e ih =>
      obtain ⟨f, hf, hIf⟩ := exists_nonzero_kernel_relation_of_trdeg_le q hd (by omega)
      obtain ⟨c, _hc, hfin, hminor⟩ :=
        exists_finite_projection_preserving_differential_minors f (RingHom.ker q) hf hIf
          K D (fun _ => tailCoordinate d e) (by simpa only [tailCoordinate_succ] using! hD)
      let φ := (coordinateChange f c).symm.toAlgHom.comp (MvPolynomial.rename Fin.succ)
      let qbar := Ideal.kerLiftAlg q
      have hfactor : qbar.comp (Ideal.Quotient.mkₐ k (RingHom.ker q)) = q := by
        apply AlgHom.ext
        intro x
        exact Ideal.kerLiftAlg_mk q x
      have hqbar : qbar.Finite := AlgHom.Finite.of_comp_finite (hfactor ▸ hq)
      have hqφ : (q.comp φ).Finite := by
        rw [← hfactor, AlgHom.comp_assoc]
        exact hqbar.comp hfin
      let D' (i : ι) (a : Fin d) := (D i a).comp φ.toLinearMap
      have hD' : ∀ i,
          Matrix.det (fun a b => D' i a (X (tailCoordinate d e b))) ≠ 0 := by
        intro i
        change Matrix.det (fun a b => D i a (φ (X (tailCoordinate d e b)))) ≠ 0
        simpa only [φ, AlgHom.comp_apply, rename_X, AlgEquiv.coe_toAlgHom] using! hminor i
      obtain ⟨ψ, hψfin, hψminor⟩ := ih (q.comp φ) hqφ D' hD'
      refine ⟨φ.comp ψ, ?_, ?_⟩
      · simpa only [AlgHom.comp_assoc] using! hψfin
      · simpa only [D', LinearMap.comp_apply, AlgHom.toLinearMap_apply,
          AlgHom.comp_apply] using! hψminor

end ParameterizedNoetherNormalization
