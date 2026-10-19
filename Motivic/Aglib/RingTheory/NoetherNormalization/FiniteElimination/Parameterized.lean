module
public import Motivic.Aglib.RingTheory.NoetherNormalization.Parameterized

/-! # Finite projections from the parameterized coordinate change -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.MvPolynomial Polynomial Ideal RingHom
universe u
namespace ParameterizedNoetherNormalization

/-- Transport monic elimination back to the actual original quotient. -/
theorem finite_projection_of_monicRelation
    {k : Type u} [Field k] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) k))
    (e : MvPolynomial (Fin (n + 1)) k ≃ₐ[k] MvPolynomial (Fin (n + 1)) k)
    (g : (MvPolynomial (Fin n) k)[X]) (hg : g.Monic)
    (hIg : g ∈ (I.map e).map (finSuccEquiv k n)) :
    ((Ideal.Quotient.mkₐ k I).comp
      (e.symm.toAlgHom.comp (MvPolynomial.rename Fin.succ))).Finite := by
  let E := e.trans (finSuccEquiv k n)
  let J := (I.map e).map (finSuccEquiv k n)
  have hmap : I = J.map E.symm := by
    change I = ((I.map e.toRingHom).map (finSuccEquiv k n).toRingHom).map
      ((finSuccEquiv k n).symm.trans e.symm).toRingHom
    rw [Ideal.map_map, Ideal.map_map]
    have hh : (((finSuccEquiv k n).symm.trans e.symm).toRingHom.comp
        (finSuccEquiv k n).toRingHom).comp e.toRingHom = RingHom.id _ := by
      apply RingHom.ext
      intro x
      change e.symm ((finSuccEquiv k n).symm ((finSuccEquiv k n) (e x))) = x
      simp
    rw [hh, Ideal.map_id]
  let Q : ((MvPolynomial (Fin n) k)[X] ⧸ J) ≃ₐ[k]
      MvPolynomial (Fin (n + 1)) k ⧸ I :=
    Ideal.quotientEquivAlg J I E.symm hmap
  let a : MvPolynomial (Fin n) k →ₐ[MvPolynomial (Fin n) k]
      (MvPolynomial (Fin n) k)[X] ⧸ J :=
    (Ideal.Quotient.mkₐ (MvPolynomial (Fin n) k) J).comp
      (Algebra.ofId (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) k)[X])
  have ha : a.IsIntegral := hg.quotient_isIntegral hIg
  have hq : RingHom.IsIntegral
      (R := (MvPolynomial (Fin n) k)[X] ⧸ J)
      (A := MvPolynomial (Fin (n + 1)) k ⧸ I) Q.toAlgHom.toRingHom := by
    intro x
    obtain ⟨y, rfl⟩ := Q.surjective x
    exact RingHom.isIntegralElem_map
      (R := (MvPolynomial (Fin n) k)[X] ⧸ J)
      (S := MvPolynomial (Fin (n + 1)) k ⧸ I) Q.toAlgHom.toRingHom
  have hb : (Q.toAlgHom.comp (a.restrictScalars k)).IsIntegral := by
    change (Q.toAlgHom.toRingHom.comp a.toRingHom).IsIntegral
    exact RingHom.IsIntegral.trans
      (R := MvPolynomial (Fin n) k)
      (S := (MvPolynomial (Fin n) k)[X] ⧸ J)
      (T := MvPolynomial (Fin (n + 1)) k ⧸ I)
      a.toRingHom Q.toAlgHom.toRingHom ha hq
  have hc : Q.toAlgHom.comp (a.restrictScalars k) =
      (Ideal.Quotient.mkₐ k I).comp
        (e.symm.toAlgHom.comp (MvPolynomial.rename Fin.succ)) := by
    apply MvPolynomial.algHom_ext
    intro j
    simp only [AlgHom.comp_apply, rename_X]
    change Q (a (X j)) = _
    have haj : a (X j) = Ideal.Quotient.mk J (Polynomial.C (X j)) := by
      simp only [a, AlgHom.comp_apply, Algebra.ofId_apply]
      rfl
    rw [haj]
    change Q (Ideal.Quotient.mk J (Polynomial.C (X j))) =
      Ideal.Quotient.mk I (e.symm (X j.succ))
    rw [show Q (Ideal.Quotient.mk J (Polynomial.C (X j))) =
        Ideal.Quotient.mk I (E.symm (Polynomial.C (X j))) from
      Ideal.quotientEquivAlg_mk (I := J) (J := I) E.symm hmap _]
    congr 1
    change e.symm ((finSuccEquiv k n).symm (Polynomial.C (X j))) = _
    rw [← finSuccEquiv_X_succ, AlgEquiv.symm_apply_apply]
  have hd : ((Ideal.Quotient.mkₐ k I).comp
      (e.symm.toAlgHom.comp (MvPolynomial.rename Fin.succ))).IsIntegral := by
    rw [← hc]
    exact hb
  refine hd.to_finite ?_
  let b := (Ideal.Quotient.mkₐ k I).comp
    (e.symm.toAlgHom.comp (MvPolynomial.rename Fin.succ))
  have ht : algebraMap k (MvPolynomial (Fin (n + 1)) k ⧸ I) =
      b.toRingHom.comp (algebraMap k (MvPolynomial (Fin n) k)) := b.comp_algebraMap.symm
  exact (ht ▸ RingHom.finiteType_algebraMap.mpr inferInstance).of_comp_finiteType

/-- Every nonzero parameter gives a finite map to the original closed subscheme. -/
theorem coordinateChange_finite_projection
    {k : Type u} [Field k] {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) k)
    (I : Ideal (MvPolynomial (Fin (n + 1)) k))
    (c : k) (hc : c ≠ 0) (hf : f ≠ 0) (hIf : f ∈ I) :
    ((Ideal.Quotient.mkₐ k I).comp
      ((coordinateChange f c).symm.toAlgHom.comp (MvPolynomial.rename Fin.succ))).Finite := by
  obtain ⟨g, hg, hIg⟩ := coordinateChange_monicRelation f I c hc hf hIf
  exact finite_projection_of_monicRelation I (coordinateChange f c) g hg hIg

end ParameterizedNoetherNormalization
