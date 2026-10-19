module
public import Motivic.Aglib.RingTheory.NoetherNormalization.Centered

/-! # Finite elimination on the original quotient with preserved first jets -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.MvPolynomial Polynomial Ideal RingHom
universe u
namespace CenteredNoetherNormalization

/-- The surviving coordinates after a first-jet-preserving automorphism give a
finite map into the original quotient, not merely a different presented algebra. -/
theorem exists_finite_projection_closedBoundaryJets
    {k : Type u} [Field k] {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) k)
    (I J₀ : Ideal (MvPolynomial (Fin (n + 1)) k)) (hf : f ≠ 0) (hIf : f ∈ I)
    (hJ : X (0 : Fin (n + 1)) ∈ J₀) :
    ∃ e : MvPolynomial (Fin (n + 1)) k ≃ₐ[k] MvPolynomial (Fin (n + 1)) k,
      (Ideal.Quotient.mkₐ k (J₀ ^ 2)).comp e.toAlgHom =
        Ideal.Quotient.mkₐ k (J₀ ^ 2) ∧
      ((Ideal.Quotient.mkₐ k I).comp
        (e.symm.toAlgHom.comp (MvPolynomial.rename Fin.succ))).Finite := by
  obtain ⟨e, he, g, hg, hIg⟩ :=
    exists_coordinateChange_closedBoundaryJets_monicRelation f I J₀ hf hIf hJ
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
  refine ⟨e, he, hd.to_finite ?_⟩
  let b := (Ideal.Quotient.mkₐ k I).comp
    (e.symm.toAlgHom.comp (MvPolynomial.rename Fin.succ))
  have ht : algebraMap k (MvPolynomial (Fin (n + 1)) k ⧸ I) =
      b.toRingHom.comp (algebraMap k (MvPolynomial (Fin n) k)) := b.comp_algebraMap.symm
  exact (ht ▸ RingHom.finiteType_algebraMap.mpr inferInstance).of_comp_finiteType

/-- Centered rational-point specialization of full closed-boundary jet preservation. -/
theorem exists_finite_projection_firstJets
    {k : Type u} [Field k] {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) k)
    (I : Ideal (MvPolynomial (Fin (n + 1)) k)) (hf : f ≠ 0) (hIf : f ∈ I) :
    ∃ e : MvPolynomial (Fin (n + 1)) k ≃ₐ[k] MvPolynomial (Fin (n + 1)) k,
      (Ideal.Quotient.mkₐ k ((idealOfVars (Fin (n + 1)) k) ^ 2)).comp e.toAlgHom =
        Ideal.Quotient.mkₐ k ((idealOfVars (Fin (n + 1)) k) ^ 2) ∧
      ((Ideal.Quotient.mkₐ k I).comp
        (e.symm.toAlgHom.comp (MvPolynomial.rename Fin.succ))).Finite :=
  exists_finite_projection_closedBoundaryJets f I (idealOfVars (Fin (n + 1)) k)
    hf hIf (Ideal.subset_span ⟨0, rfl⟩)

/-- Actual surviving coordinate functions on the original polynomial algebra:
their first jets are the prescribed surviving variables, and their restriction
to the original quotient is finite. -/
theorem exists_finite_projection_preserving_closedBoundary_jets
    {k : Type u} [Field k] {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) k)
    (I J : Ideal (MvPolynomial (Fin (n + 1)) k)) (hf : f ≠ 0) (hIf : f ∈ I)
    (hJ : X (0 : Fin (n + 1)) ∈ J) :
    ∃ p : MvPolynomial (Fin n) k →ₐ[k] MvPolynomial (Fin (n + 1)) k,
      ((Ideal.Quotient.mkₐ k I).comp p).Finite ∧
      (Ideal.Quotient.mkₐ k (J ^ 2)).comp p =
        (Ideal.Quotient.mkₐ k (J ^ 2)).comp
          (MvPolynomial.rename Fin.succ) := by
  obtain ⟨e, he, hfin⟩ := exists_finite_projection_closedBoundaryJets f I J hf hIf hJ
  let q := Ideal.Quotient.mkₐ k (J ^ 2)
  have hinv : q.comp e.symm.toAlgHom = q := by
    apply AlgHom.ext
    intro x
    have h := congrArg (fun h => h (e.symm x)) he
    simpa only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
      AlgEquiv.apply_symm_apply] using h.symm
  refine ⟨e.symm.toAlgHom.comp (MvPolynomial.rename Fin.succ), hfin, ?_⟩
  change q.comp (e.symm.toAlgHom.comp (MvPolynomial.rename Fin.succ)) = _
  rw [← AlgHom.comp_assoc, hinv]

/-- Rational-origin specialization, preserving the previous consumer interface. -/
theorem exists_finite_projection_preserving_surviving_jets
    {k : Type u} [Field k] {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) k)
    (I : Ideal (MvPolynomial (Fin (n + 1)) k)) (hf : f ≠ 0) (hIf : f ∈ I) :
    ∃ p : MvPolynomial (Fin n) k →ₐ[k] MvPolynomial (Fin (n + 1)) k,
      ((Ideal.Quotient.mkₐ k I).comp p).Finite ∧
      (Ideal.Quotient.mkₐ k ((idealOfVars (Fin (n + 1)) k) ^ 2)).comp p =
        (Ideal.Quotient.mkₐ k ((idealOfVars (Fin (n + 1)) k) ^ 2)).comp
          (MvPolynomial.rename Fin.succ) :=
  exists_finite_projection_preserving_closedBoundary_jets f I
    (idealOfVars (Fin (n + 1)) k) hf hIf (Ideal.subset_span ⟨0, rfl⟩)

end CenteredNoetherNormalization
