/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.CoordinateRing
public import Aglib.AlgebraicGeometry.Properties.Normal.Affine
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.RingTheory.Polynomial.RationalRoot

/-! # Actual affine charts and normality of the projective line -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.ProjectiveLine

attribute [local instance] MvPolynomial.gradedAlgebra

universe u
variable (k : Type u) [Field k]

/-- The complementary homogeneous coordinate is unique. -/
local instance otherUnique (i : ULift.{u} (Fin 2)) :
    Unique {j : ULift.{u} (Fin 2) // j ≠ i} where
  default := ⟨⟨1 - i.down⟩, by rcases i with ⟨i⟩; fin_cases i <;> decide⟩
  uniq j := by
    rcases i with ⟨i⟩
    rcases j with ⟨⟨j⟩, hj⟩
    fin_cases i <;> fin_cases j <;>
      simp_all only [Fin.zero_eta, Fin.mk_one, Fin.isValue, ne_eq, sub_zero, sub_self,
        Subtype.mk.injEq, ULift.up.injEq, zero_ne_one, one_ne_zero] <;> exact (hj rfl).elim

/-- The actual homogeneous coordinate ring, identified with the one-variable polynomial ring. -/
def chartRingEquiv (i : ULift.{u} (Fin 2)) :
    ProjectiveSpace.coordinateRing k (ULift.{u} (Fin 2)) i ≃+* Polynomial k :=
  (ProjectiveSpace.coordinateRingEquivPolynomial k (ULift.{u} (Fin 2)) i).trans
    (MvPolynomial.uniqueAlgEquiv k {j : ULift.{u} (Fin 2) // j ≠ i}).toRingEquiv

/-- The affine line included in the actual projective line at coordinate `i`. -/
def chart (i : ULift.{u} (Fin 2)) :
    Spec (.of (Polynomial k)) ⟶ ProjectiveSpace k (ULift.{u} (Fin 2)) :=
  Spec.map (chartRingEquiv k i).toCommRingCatIso.hom ≫
    Proj.awayι (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin 2)) k) (MvPolynomial.X i)
      (MvPolynomial.isHomogeneous_X k i) Nat.zero_lt_one

instance chart_isOpenImmersion (i : ULift.{u} (Fin 2)) : IsOpenImmersion (chart k i) := by
  have : IsIso (Spec.map (chartRingEquiv k i).toCommRingCatIso.hom) := inferInstance
  unfold chart
  infer_instance

@[reassoc]
theorem chart_toSpec (i : ULift.{u} (Fin 2)) :
    chart k i ≫ ProjectiveSpace.toSpec k (ULift.{u} (Fin 2)) =
    Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k)) := by
  rw [chart, Category.assoc, ProjectiveSpace.coordinateChart_toSpec, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  change chartRingEquiv k i
    (ProjectiveSpace.coordinateRingCoefficient k (ULift.{u} (Fin 2)) i a) = _
  simp [chartRingEquiv, ProjectiveSpace.coordinateRingEquivPolynomial,
    ProjectiveSpace.coordinateRingToPolynomial_coefficient]

/-- The chart image is exactly the native homogeneous coordinate open. -/
theorem chart_opensRange (i : ULift.{u} (Fin 2)) :
    (chart k i).opensRange = ProjectiveSpace.coordinateOpen k (ULift.{u} (Fin 2)) i := by
  have : IsIso (Spec.map (chartRingEquiv k i).toCommRingCatIso.hom) := inferInstance
  unfold chart
  rw [Scheme.Hom.opensRange_comp_of_isIso, Proj.opensRange_awayι]
  rfl

/-- These actual affine-line charts cover the projective line. -/
theorem iSup_chart_opensRange : (⨆ i, (chart k i).opensRange) = ⊤ := by
  simp only [chart_opensRange]
  exact ProjectiveSpace.iSup_coordinateOpen_eq_top k (ULift.{u} (Fin 2))

/-- Every projective-line stalk is an integrally closed domain. -/
theorem stalk_normal_domain (x : ProjectiveSpace k (ULift.{u} (Fin 2))) :
    IsIntegrallyClosed ((ProjectiveSpace k (ULift.{u} (Fin 2))).presheaf.stalk x) ∧
      IsDomain ((ProjectiveSpace k (ULift.{u} (Fin 2))).presheaf.stalk x) := by
  let cov := ProjectiveSpace.coordinateAffineOpenCover k (ULift.{u} (Fin 2))
  obtain ⟨y, hy⟩ := cov.covers x
  let i := cov.idx x
  let e := ProjectiveSpace.coordinateRingEquivPolynomial k (ULift.{u} (Fin 2)) i
  have : IsDomain (ProjectiveSpace.coordinateRing k (ULift.{u} (Fin 2)) i) :=
    e.toMulEquiv.isDomain _
  have : IsIntegrallyClosed (ProjectiveSpace.coordinateRing k (ULift.{u} (Fin 2)) i) :=
    IsIntegrallyClosed.of_equiv e.symm
  have hs := Scheme.isIntegrallyClosed_and_isDomain_stalk_Spec
    (ProjectiveSpace.coordinateRing k (ULift.{u} (Fin 2)) i) y
  have : IsIntegrallyClosed ((Spec (cov.X i)).presheaf.stalk y) := hs.1
  have : IsDomain ((Spec (cov.X i)).presheaf.stalk y) := hs.2
  rw [← hy]
  let ρ := (asIso ((cov.f i).stalkMap y)).symm.commRingCatIsoToRingEquiv
  exact ⟨IsIntegrallyClosed.of_equiv ρ, ρ.symm.toMulEquiv.isDomain _⟩

instance instIsIntegrallyClosedStalk (x : ProjectiveSpace k (ULift.{u} (Fin 2))) :
    IsIntegrallyClosed ((ProjectiveSpace k (ULift.{u} (Fin 2))).presheaf.stalk x) :=
  (stalk_normal_domain k x).1

instance instIsDomainStalk (x : ProjectiveSpace k (ULift.{u} (Fin 2))) :
    IsDomain ((ProjectiveSpace k (ULift.{u} (Fin 2))).presheaf.stalk x) :=
  (stalk_normal_domain k x).2

/-- The zero homogeneous prime is a genuine projective point over a field. -/
def zeroPoint : ProjectiveSpace k (ULift.{u} (Fin 2)) where
  asHomogeneousIdeal := ⊥
  isPrime := by
    change (⊥ : Ideal (MvPolynomial (ULift.{u} (Fin 2)) k)).IsPrime
    infer_instance
  not_irrelevant_le h := by
    have hm := h (HomogeneousIdeal.mem_irrelevant_of_mem
      (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin 2)) k) Nat.zero_lt_one
      (MvPolynomial.isHomogeneous_X k (ULift.up (0 : Fin 2))))
    exact MvPolynomial.X_ne_zero (ULift.up (0 : Fin 2)) hm

instance instIrreducibleSpace : IrreducibleSpace (ProjectiveSpace k (ULift.{u} (Fin 2))) := by
  apply (irreducibleSpace_def _).mpr
  have hcl : closure ({zeroPoint k} : Set (ProjectiveSpace k (ULift.{u} (Fin 2)))) =
      Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    exact (ProjectiveSpectrum.le_iff_mem_closure _ _ _).mp
      (show (zeroPoint k).asHomogeneousIdeal ≤ x.asHomogeneousIdeal from bot_le)
  change IsIrreducible (Set.univ : Set (ProjectiveSpace k (ULift.{u} (Fin 2))))
  rw [← hcl]
  exact isIrreducible_singleton.closure

instance instIsIntegral : IsIntegral (ProjectiveSpace k (ULift.{u} (Fin 2))) := by
  have : IsReduced (ProjectiveSpace k (ULift.{u} (Fin 2))) :=
    isReduced_of_isReduced_stalk _
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end AlgebraicGeometry.ProjectiveLine
