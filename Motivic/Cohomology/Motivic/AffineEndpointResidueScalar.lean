/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Motivic.DiagonalResiduePointEvaluation
public import Motivic.KTheory.MilnorK.AffineEndpointGeometry

/-! The original affine fiber scalar map and original branch residue equivalence. -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.FiniteFlatCurve AlgebraicGeometry.FiniteAffineEndpointBranches
open Motivic.KTheory.MilnorK Motivic.KTheory.MilnorK.AffineEndpointGeometry
open IsDedekindDomain Motivic.KTheory
open scoped Polynomial

universe u
namespace Motivic.AffineEndpointResidueScalar
open DiagonalResiduePointEvaluation
variable (k S : Type u) [Field k] [CommRing S] [IsDedekindDomain S]
  [Algebra k[X] S] [Module.Finite k[X] S] [Module.IsTorsionFree k[X] S]
  [Algebra k S] [IsScalarTower k k[X] S]

/-- The actual structural projection of the original endpoint fiber. -/
abbrev fiberBase (a : k) : fiber (baseMap S) a ⟶ Spec (.of k) :=
  pullback.fst (endpoint a) (baseMap S)

omit [IsDedekindDomain S] [Module.Finite k[X] S] [Module.IsTorsionFree k[X] S] in
/-- The fiber projection and inclusion have the same original base-field map. -/
theorem fiberBase_eq (a : k) :
    fiberBase k S a = fiberInclusion (baseMap S) a ≫
      Spec.map (CommRingCat.ofHom (algebraMap k S)) := by
  have h := congrArg (fun f => f ≫ Spec.map
    (CommRingCat.ofHom (algebraMap k k[X])))
    (pullback.condition (f := endpoint a) (g := baseMap S))
  simpa only [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← IsScalarTower.algebraMap_eq k k[X] S,
    show (Polynomial.evalRingHom a).comp (algebraMap k k[X]) = RingHom.id k by ext; simp,
    CommRingCat.ofHom_id, Spec.map_id, Category.comp_id] using h

/-- Restriction of an original global scalar to the whole endpoint fiber. -/
def restrictScalar (a : k) : S →+* Γ(fiber (baseMap S) a, ⊤) :=
  (fiberInclusion (baseMap S) a).appTop.hom.comp (Scheme.ΓSpecIso (.of S)).inv.hom

omit [IsDedekindDomain S] [Module.Finite k[X] S] [Module.IsTorsionFree k[X] S] in
/-- The whole fiber retains the original base-field action. -/
theorem schemeScalar_eq (a : k) :
    WeightOneFundamentalNorm.schemeScalarMap (fiberBase k S a) =
      (restrictScalar k S a).comp (algebraMap k S) := by
  unfold WeightOneFundamentalNorm.schemeScalarMap restrictScalar
  rw [fiberBase_eq, Scheme.Hom.comp_appTop]
  apply RingHom.ext
  intro r
  change (fiberInclusion (baseMap S) a).appTop
    ((Spec.map (CommRingCat.ofHom (algebraMap k S))).appTop
      ((Scheme.ΓSpecIso (.of k)).inv r)) = _
  have h := ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap k S))) r
  exact congrArg (fiberInclusion (baseMap S) a).appTop h.symm

omit [Algebra k S] [IsScalarTower k k[X] S] in
/-- The branch residue equivalence agrees with literal evaluation after restriction. -/
theorem originalBranchResidueEquiv_evaluation (a : k) (x : fiber (baseMap S) a) (s : S) :
    originalBranchResidueEquiv k S a x
        (IsLocalRing.residue _ (algebraMap S _ s)) =
      (fiber (baseMap S) a).Γevaluation x (restrictScalar k S a s) := by
  have h := fiberResidueEquiv_Γevaluation S a x ((Scheme.ΓSpecIso (.of S)).inv s)
  rw [originalBranchResidueEquiv, RingEquiv.trans_apply,
    DedekindPointStalk.residueEquiv_algebraMap]
  exact h

/-- The residue-field equivalence preserves the original ground-field scalar map. -/
theorem originalBranchResidueEquiv_base (a : k) (x : fiber (baseMap S) a) (r : k) :
    originalBranchResidueEquiv k S a x
        (IsLocalRing.residue _ (algebraMap S _ (algebraMap k S r))) =
      residueScalar (fiberBase k S a) x r := by
  rw [originalBranchResidueEquiv_evaluation]
  unfold residueScalar
  rw [schemeScalar_eq]
  rfl

local instance finiteType : Algebra.FiniteType k S :=
  Algebra.FiniteType.trans (S := k[X])
    (inferInstanceAs (Algebra.FiniteType k k[X]))
    (inferInstanceAs (Algebra.FiniteType k[X] S))

local instance localResidueFinite (Q : HeightOneSpectrum S) :
    FiniteDimensional k (IsLocalRing.ResidueField (Localization.AtPrime Q.asIdeal)) :=
  Localization.finiteType_localResidue_finite k S Q.asIdeal

local instance baseFinite : IsFinite (baseMap (k := k) S) :=
  (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)

/-- The unchanged original branch point of the actual endpoint fiber. -/
abbrev branchPoint (a : k) (x : fiber (baseMap S) a) : HeightOneSpectrum S :=
  DedekindResidue.branchPoint k[X] S
    (PolynomialDedekindResidue.point (DedekindResidue.endpointPolynomial k a))
    (originalBranchEquiv k S a x)

variable [CharZero k]

/-- Actual residue norms commute with the original branch-to-fiber identification. -/
theorem norm_originalBranch (a : k) (x : fiber (baseMap S) a) (n : ℕ)
    (v : K (IsLocalRing.ResidueField
      (Localization.AtPrime (branchPoint k S a x).asIdeal)) n) :
    let : Algebra k ((fiber (baseMap S) a).residueField x) :=
      residueAlgebra (fiberBase k S a) x
    let : Module.Finite k ((fiber (baseMap S) a).residueField x) :=
      residueFinite (fiberBase k S a) x
    finiteExtensionNorm k (IsLocalRing.ResidueField
      (Localization.AtPrime (branchPoint k S a x).asIdeal)) n v =
      finiteExtensionNorm k ((fiber (baseMap S) a).residueField x) n
        (MilnorK.map n (originalBranchResidueEquiv k S a x).toRingHom v) := by
  let : Algebra k ((fiber (baseMap S) a).residueField x) :=
    residueAlgebra (fiberBase k S a) x
  let : Module.Finite k ((fiber (baseMap S) a).residueField x) :=
    residueFinite (fiberBase k S a) x
  have hs (r : k) : originalBranchResidueEquiv k S a x
      (algebraMap k (IsLocalRing.ResidueField
        (Localization.AtPrime (branchPoint k S a x).asIdeal)) r) =
        algebraMap k ((fiber (baseMap S) a).residueField x) r := by
    exact originalBranchResidueEquiv_base k S a x r
  have h := finiteExtensionNorm_equiv (RingEquiv.refl k)
    (originalBranchResidueEquiv k S a x) hs n v
  have hid : (RingEquiv.refl k).toRingHom = RingHom.id k := rfl
  simpa only [hid, MilnorK.map_id, LinearMap.id_apply] using h

/-- The intrinsic fiber value of original global units is their original local-branch norm. -/
theorem residueValue_original_units (a : k) (x : fiber (baseMap S) a)
    (n : ℕ) (u : Fin n → Sˣ) :
    residueValue (fiberBase k S a)
      (fun i => Units.map (restrictScalar k S a).toMonoidHom (u i)) x =
      finiteExtensionNorm k (IsLocalRing.ResidueField
        (Localization.AtPrime (branchPoint k S a x).asIdeal)) n
        (symbol (fun i => Units.map
          ((IsLocalRing.residue (Localization.AtPrime (branchPoint k S a x).asIdeal)).comp
            (algebraMap S (Localization.AtPrime (branchPoint k S a x).asIdeal))).toMonoidHom
          (u i))) := by
  let : Algebra k ((fiber (baseMap S) a).residueField x) :=
    residueAlgebra (fiberBase k S a) x
  let : Module.Finite k ((fiber (baseMap S) a).residueField x) :=
    residueFinite (fiberBase k S a) x
  rw [norm_originalBranch]
  dsimp only [residueValue]
  rw [MilnorK.map_symbol]
  apply congrArg (finiteExtensionNorm k ((fiber (baseMap S) a).residueField x) n)
  apply congrArg symbol
  funext i
  apply Units.ext
  exact (originalBranchResidueEquiv_evaluation k S a x (u i).val).symm

end Motivic.AffineEndpointResidueScalar
