/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.AlgebraicGeometry.Correspondences.RelativePolynomialPencilSpecialization
public import Motivic.AlgebraicGeometry.Correspondences.RelativePolynomialOpenRestriction
public import Motivic.Cohomology.A1.Basic
/-! # The actual polynomial moving correspondence acts as the original restriction -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
open AlgebraicGeometry.PolynomialOpenQuotient Polynomial.ZeroNeighborhoodInterpolation
universe v u
namespace Motivic.RelativePolynomialOpenSpans
variable {k R A : Type u} [Field k] [CommRing R] [CommRing A]
    [Algebra k R] [Algebra.Smooth k R] [Algebra R A] [Algebra k A]
    [IsScalarTower k R A] [Algebra.Smooth k A]

/-- Equal-degree boundary-one polynomials give equal actual actions
by a constructed finite-flat pencil. -/
theorem transfer_cycle_eq_of_boundary_one
    (P : PresheafWithTransfers.{v} k) (hP : P.IsA1Invariant)
    (p q : A[X]) (hp : p.Monic) (hq : q.Monic) (hdeg : q.natDegree = p.natDegree)
    (f : R[X]) (hpf : f.map (algebraMap R A) ∣ p - 1)
    (hqf : f.map (algebraMap R A) ∣ q - 1)
    (hpu : IsUnit (AdjoinRoot.mk p (f.map (algebraMap R A))))
    (hqu : IsUnit (AdjoinRoot.mk q (f.map (algebraMap R A)))) [Nontrivial A] :
    P.transfer (cycle p hp f hpu) = P.transfer (cycle q hq f hqu) := by
  have hm := (pencil_monic_natDegree hp hq hdeg).1
  have hu : IsUnit (AdjoinRoot.mk (pencil p q)
      (f.map (parameterCoefficients (R := R) (A := A)))) := by
    simpa only [Polynomial.map_map] using pencil_boundary_unit (f.map (algebraMap R A))
      p q hpf hqf
  have h := P.transfer_homotopy_endpoints hP (sourceSite (k := k) (A := A))
    (Cor.mk (openSite (k := k) f)) (familyCycle (pencil p q) hm f hu) 0 1
  simpa only [graph_familyCycle, map_zero, map_one, pencil_zero, pencil_one] using h

variable [IsDomain A] [IsNoetherianRing A]

/-- A genuine signed correspondence into the smaller open factors the original coordinate action.
The field may be finite and P need not be a sheaf. -/
theorem exists_moving_action (f g : R[X]) (hf : f.Monic) (hg : g.Monic)
    (hfg : IsCoprime f g) (a : A)
    (ha : IsUnit ((f.map (algebraMap R A)).eval a))
    (j : sourceSite (k := k) (A := A) ⟶ openSite (k := k) f)
    (hj : j ≫ openInclusion (k := k) f = coordinateMorphism (k := k) (R := R) a) :
    ∃ β : Cor.mk (sourceSite (k := k) (A := A)) ⟶ Cor.mk (openSite (k := k) (f * g)),
      ∀ (P : PresheafWithTransfers.{v} k), P.IsA1Invariant →
        P.transfer ((Cor.graphFunctor k).map j) =
          P.transfer ((Cor.graphFunctor k).map (narrowInclusion (k := k) f g)) ≫ P.transfer β := by
  let F := f.map (algebraMap R A)
  let G := g.map (algebraMap R A)
  obtain ⟨d, q, hd, hq, hdeg, hfd, hgd, hfgq⟩ :=
    OpenMovingPair.exists_monic_pair F G (hf.map _) (hg.map _)
      (hfg.map (Polynomial.mapRingHom (algebraMap R A))) a ha
  let p := (X - C a) * d
  have hp : p.Monic := (monic_X_sub_C a).mul hd
  have heq : q.natDegree = p.natDegree := by
    rw [show p = (X - C a) * d from rfl,
      Monic.natDegree_mul (monic_X_sub_C a) hd, natDegree_X_sub_C, hdeg]
    omega
  have hduf := OpenMovingPair.boundary_unit d F (X - C a) hfd
  have hdug := OpenMovingPair.boundary_unit d G 1 (by simpa using hgd)
  have hqu := OpenMovingPair.boundary_unit q (F * G) 1 (by simpa using hfgq)
  have hdu : IsUnit (AdjoinRoot.mk d ((f * g).map (algebraMap R A))) := by
    rw [Polynomial.map_mul, map_mul]
    exact hduf.mul hdug
  have hqu' : IsUnit (AdjoinRoot.mk q ((f * g).map (algebraMap R A))) := by
    simpa only [Polynomial.map_mul] using hqu
  have hpu := OpenMovingPair.boundary_unit p F 1 (by simpa [p] using hfd)
  obtain ⟨r, hr⟩ := OpenMovingPair.exists_diagonal_inverse F a ha
  have hlu := OpenMovingPair.boundary_unit (X - C a) F r (by simpa [mul_comm] using hr)
  refine ⟨cycle q hq (f * g) hqu' - cycle d hd (f * g) hdu, ?_⟩
  intro P hP
  have hc := transfer_cycle_eq_of_boundary_one P hP p q hp hq heq f hfd
    (dvd_trans (dvd_mul_right F G) hfgq) hpu (old_boundary_unit q f g hqu')
  have hmul := cycle_mul (k := k) (X - C a) d (monic_X_sub_C a) hd f hlu hduf hpu
  rw [cycle_linear_graph (k := k) a f hlu j hj] at hmul
  have he : (show P.sections (Cor.mk (openSite (k := k) f)) ⟶
      P.sections (Cor.mk (sourceSite (k := k) (A := A))) from
      P.transfer ((Cor.graphFunctor k).map j)) + P.transfer (cycle d hd f hduf) =
      P.transfer (cycle q hq f (old_boundary_unit q f g hqu')) := by
    rw [← PresheafWithTransfers.transfer_add, ← hmul]
    exact hc
  rw [← PresheafWithTransfers.transfer_comp, Preadditive.sub_comp,
    cycle_narrowInclusion, cycle_narrowInclusion, PresheafWithTransfers.transfer_sub]
  exact eq_sub_iff_add_eq.mpr he

end Motivic.RelativePolynomialOpenSpans
