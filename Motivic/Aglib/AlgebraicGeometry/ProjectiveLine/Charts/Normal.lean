module

public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Charts.Basic
public import Aglib.AlgebraicGeometry.Properties.Normal.Affine
public import Mathlib.RingTheory.Polynomial.IsIntegral

/-! # Normal-domain stalks of the relative projective line

The literal affine charts prove normality over any integrally closed domain.
No field or regularity hypothesis is imposed on the coefficient ring.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory TopologicalSpace
namespace AlgebraicGeometry.RelativeProjectiveLine
attribute [local instance] MvPolynomial.gradedAlgebra
universe u
variable (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]

/-- Every projective-line stalk is an integrally closed domain. -/
theorem stalk_normal_domain (x : ProjectiveSpace R (ULift.{u} (Fin 2))) :
    IsIntegrallyClosed ((ProjectiveSpace R (ULift.{u} (Fin 2))).presheaf.stalk x) ∧
      IsDomain ((ProjectiveSpace R (ULift.{u} (Fin 2))).presheaf.stalk x) := by
  let cov := ProjectiveSpace.coordinateAffineOpenCover R (ULift.{u} (Fin 2))
  obtain ⟨y, hy⟩ := cov.covers x
  let i := cov.idx x
  let e := chartRingEquiv R i
  have : IsDomain (ProjectiveSpace.coordinateRing R (ULift.{u} (Fin 2)) i) :=
    e.toMulEquiv.isDomain _
  have : IsIntegrallyClosed (ProjectiveSpace.coordinateRing R (ULift.{u} (Fin 2)) i) :=
    IsIntegrallyClosed.of_equiv e.symm
  have hs := Scheme.isIntegrallyClosed_and_isDomain_stalk_Spec
    (ProjectiveSpace.coordinateRing R (ULift.{u} (Fin 2)) i) y
  have : IsIntegrallyClosed ((Spec (cov.X i)).presheaf.stalk y) := hs.1
  have : IsDomain ((Spec (cov.X i)).presheaf.stalk y) := hs.2
  rw [← hy]
  let ρ := (asIso ((cov.f i).stalkMap y)).symm.commRingCatIsoToRingEquiv
  exact ⟨IsIntegrallyClosed.of_equiv ρ, ρ.symm.toMulEquiv.isDomain _⟩

instance instIsIntegrallyClosedStalk (x : ProjectiveSpace R (ULift.{u} (Fin 2))) :
    IsIntegrallyClosed ((ProjectiveSpace R (ULift.{u} (Fin 2))).presheaf.stalk x) :=
  (stalk_normal_domain R x).1

instance instIsDomainStalk (x : ProjectiveSpace R (ULift.{u} (Fin 2))) :
    IsDomain ((ProjectiveSpace R (ULift.{u} (Fin 2))).presheaf.stalk x) :=
  (stalk_normal_domain R x).2

/-- The zero homogeneous prime is a genuine projective point over a domain. -/
def zeroPoint : ProjectiveSpace R (ULift.{u} (Fin 2)) where
  asHomogeneousIdeal := ⊥
  isPrime := by
    change (⊥ : Ideal (MvPolynomial (ULift.{u} (Fin 2)) R)).IsPrime
    infer_instance
  not_irrelevant_le h := by
    have hm := h (HomogeneousIdeal.mem_irrelevant_of_mem
      (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin 2)) R) Nat.zero_lt_one
      (MvPolynomial.isHomogeneous_X R (ULift.up (0 : Fin 2))))
    exact MvPolynomial.X_ne_zero (ULift.up (0 : Fin 2)) hm

instance instIrreducibleSpace : IrreducibleSpace (ProjectiveSpace R (ULift.{u} (Fin 2))) := by
  apply (irreducibleSpace_def _).mpr
  have hcl : closure ({zeroPoint R} : Set (ProjectiveSpace R (ULift.{u} (Fin 2)))) =
      Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    exact (ProjectiveSpectrum.le_iff_mem_closure _ _ _).mp
      (show (zeroPoint R).asHomogeneousIdeal ≤ x.asHomogeneousIdeal from bot_le)
  change IsIrreducible (Set.univ : Set (ProjectiveSpace R (ULift.{u} (Fin 2))))
  rw [← hcl]
  exact isIrreducible_singleton.closure

instance instIsIntegral : IsIntegral (ProjectiveSpace R (ULift.{u} (Fin 2))) := by
  have : IsReduced (ProjectiveSpace R (ULift.{u} (Fin 2))) :=
    isReduced_of_isReduced_stalk _
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end AlgebraicGeometry.RelativeProjectiveLine
