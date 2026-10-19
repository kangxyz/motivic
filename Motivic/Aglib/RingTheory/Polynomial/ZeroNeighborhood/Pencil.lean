module
public import Motivic.Aglib.RingTheory.Polynomial.ZeroNeighborhood.Interpolation
public import Mathlib.RingTheory.AdjoinRoot
/-! # The literal finite-free pencil for a zero-section neighborhood

All equalities hold in the original polynomial rings and whole quotient.
The base ring may have nilpotents. No finite-flat family or unit on that
family is supplied as a hypothesis.
-/
@[expose] public noncomputable section
open Polynomial
universe u
namespace Polynomial.ZeroNeighborhoodInterpolation
variable {R : Type u} [CommRing R]

/-- The inner variable is the homotopy parameter; the outer variable is the target. -/
def pencil (p q : R[X]) : R[X][X] := C (1 - X) * p.map C + C X * q.map C

lemma pencil_coeff (p q : R[X]) (n : ℕ) :
    (pencil p q).coeff n = (1 - X) * C (p.coeff n) + X * C (q.coeff n) := by
  simp only [pencil, coeff_add, coeff_C_mul, coeff_map]

lemma pencil_monic_natDegree [Nontrivial R] {p q : R[X]}
    (hp : p.Monic) (hq : q.Monic) (hdeg : q.natDegree = p.natDegree) :
    (pencil p q).Monic ∧ (pencil p q).natDegree = p.natDegree := by
  have hle : (pencil p q).natDegree ≤ p.natDegree := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro n hn
    rw [pencil_coeff, coeff_eq_zero_of_natDegree_lt hn,
      coeff_eq_zero_of_natDegree_lt (hdeg ▸ hn)]
    simp
  have hc : (pencil p q).coeff p.natDegree = 1 := by
    rw [pencil_coeff, hp.coeff_natDegree, ← hdeg, hq.coeff_natDegree]
    simp
  exact ⟨monic_of_natDegree_le_of_coeff_eq_one _ hle hc,
    natDegree_eq_of_le_of_coeff_ne_zero hle (hc.trans_ne one_ne_zero)⟩

lemma pencil_specialize (p q : R[X]) (t : R) :
    (pencil p q).map (evalRingHom t) = C (1 - t) * p + C t * q := by
  simp only [pencil, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
    coe_evalRingHom, eval_sub, eval_one, eval_X, Polynomial.map_map]
  have h : (evalRingHom t).comp C = RingHom.id R := by ext; simp
  simp only [h, Polynomial.map_id]

@[simp] lemma pencil_zero (p q : R[X]) : (pencil p q).map (evalRingHom 0) = p := by
  simp [pencil_specialize]

@[simp] lemma pencil_one (p q : R[X]) : (pencil p q).map (evalRingHom 1) = q := by
  simp [pencil_specialize]

lemma pencil_boundary (f p q : R[X]) (hp : f ∣ p - 1) (hq : f ∣ q - 1) :
    f.map C ∣ pencil p q - 1 := by
  obtain ⟨r, hr⟩ := hp
  obtain ⟨s, hs⟩ := hq
  refine ⟨C (1 - X) * r.map C + C X * s.map C, ?_⟩
  have hr' := congrArg (Polynomial.map C) hr
  have hs' := congrArg (Polynomial.map C) hs
  simp only [Polynomial.map_sub, Polynomial.map_one, Polynomial.map_mul] at hr' hs'
  dsimp only [pencil]
  rw [C_sub, C_1]
  linear_combination (1 - C X) * hr' + C X * hs'

/-- The original polynomial boundary coordinate is a unit on the whole family. -/
lemma pencil_boundary_unit (f p q : R[X]) (hp : f ∣ p - 1) (hq : f ∣ q - 1) :
    IsUnit (AdjoinRoot.mk (pencil p q) (f.map C)) := by
  obtain ⟨r, hr⟩ := pencil_boundary f p q hp hq
  have hc : IsCoprime (pencil p q) (f.map C) := by
    refine ⟨1, -r, ?_⟩
    linear_combination hr
  have hu := hc.map (AdjoinRoot.mk (pencil p q))
  simpa only [AdjoinRoot.mk_self, isCoprime_zero_left] using hu

lemma pencil_coeff_zero (p q : R[X]) (a : R)
    (hp : p.eval 0 = -a) (hq : q.eval 0 = -a) :
    (pencil p q).coeff 0 = C (-a) := by
  rw [pencil_coeff, coeff_zero_eq_eval_zero, coeff_zero_eq_eval_zero, hp, hq]
  ring

/-- Equal-degree monic endpoints produce an actual finite free algebra over R[t]. -/
theorem pencil_finite_free [Nontrivial R] {p q : R[X]}
    (hp : p.Monic) (hq : q.Monic) (hdeg : q.natDegree = p.natDegree) :
    Module.Finite R[X] (AdjoinRoot (pencil p q)) ∧
      Module.Free R[X] (AdjoinRoot (pencil p q)) :=
  ⟨(pencil_monic_natDegree hp hq hdeg).1.finite_adjoinRoot,
    (pencil_monic_natDegree hp hq hdeg).1.free_adjoinRoot⟩
/-- The punctured target remains punctured when the source coordinate is a unit. -/
lemma pencil_root_isUnit (p q : R[X]) (a : R)
    (hp : p.eval 0 = -a) (hq : q.eval 0 = -a) (ha : IsUnit a) :
    IsUnit (AdjoinRoot.root (pencil p q)) := by
  let F := pencil p q
  have h0 : IsUnit (F.coeff 0) := by
    rw [pencil_coeff_zero p q a hp hq]
    exact (ha.neg.map C)
  have hrel : AdjoinRoot.root F * AdjoinRoot.mk F F.divX =
      -AdjoinRoot.of F (F.coeff 0) := by
    have h := congrArg (AdjoinRoot.mk F) (X_mul_divX_add F)
    apply eq_neg_iff_add_eq_zero.mpr
    simpa only [map_add, map_mul, AdjoinRoot.mk_self, AdjoinRoot.root,
      AdjoinRoot.of, RingHom.comp_apply] using h
  have hu : IsUnit (AdjoinRoot.root F * AdjoinRoot.mk F F.divX) := by
    rw [hrel]
    exact (h0.map (AdjoinRoot.of F)).neg
  exact (IsUnit.mul_iff.mp hu).1

/-- Construct the actual finite-free pair homotopy, rather than assuming its properties. -/
theorem exists_finite_free_pencil [Nontrivial R] (f : R[X]) (hf : f.Monic)
    (a : R) (h0 : IsUnit (f.eval 0)) (ha : IsUnit (f.eval a)) :
    ∃ d g : R[X], d.Monic ∧ g.Monic ∧ d.eval 0 = 1 ∧ g.eval 0 = -a ∧
      (pencil ((X - C a) * d) g).Monic ∧
      Module.Finite R[X] (AdjoinRoot (pencil ((X - C a) * d) g)) ∧
      Module.Free R[X] (AdjoinRoot (pencil ((X - C a) * d) g)) ∧
      IsUnit (AdjoinRoot.mk (pencil ((X - C a) * d) g) (f.map C)) ∧
      (IsUnit a → IsUnit (AdjoinRoot.root (pencil ((X - C a) * d) g))) := by
  obtain ⟨d, g, hd, hg, hdeg, hd0, hg0, hdb, hgb⟩ :=
    exists_monic_pair f hf a h0 ha
  have hp : ((X - C a) * d).Monic := (monic_X_sub_C a).mul hd
  have hdeg' : g.natDegree = ((X - C a) * d).natDegree := by
    rw [Monic.natDegree_mul (monic_X_sub_C a) hd, natDegree_X_sub_C, hdeg]
    omega
  have hp0 : ((X - C a) * d).eval 0 = -a := by simp [hd0]
  exact ⟨d, g, hd, hg, hd0, hg0, (pencil_monic_natDegree hp hg hdeg').1,
    (pencil_finite_free hp hg hdeg').1, (pencil_finite_free hp hg hdeg').2,
    pencil_boundary_unit f _ _ hdb hgb, pencil_root_isUnit _ _ a hp0 hg0⟩

end Polynomial.ZeroNeighborhoodInterpolation
