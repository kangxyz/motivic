/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Homology.Koszul.FiniteProjection.Extension
public import Motivic.Aglib.Algebra.Homology.Koszul.ScalarRestriction.Basic
public import Motivic.Aglib.Algebra.Homology.Koszul.FiniteTor
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Flat.Stability

/-!
# Literal exterior coefficients and finite Koszul extension

Scalar extension from P to P tensor E cancels against a coefficient algebra
T with its specified P-action. The cancellation retains the literal exterior
scalar map. Restriction from P tensor W along the quotient on W then gives
an actual chain comparison on the mapped finite list. Flatness is used only
for extension along P to P tensor E over a field.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct ChangeOfRings

namespace ChainComplex.Koszul

variable {k P T E W : Type u} [CommRing k] [CommRing P] [CommRing T]
  [CommRing E] [CommRing W] [Algebra k P] [Algebra k T] [Algebra k E] [Algebra k W]

/-- The literal action on an exterior coefficient algebra. -/
def exteriorCoefficientMap (σ : P →ₐ[k] T) : P ⊗[k] E →ₐ[k] T ⊗[k] E :=
  Algebra.TensorProduct.map σ (AlgHom.id k E)

set_option backward.isDefEq.respectTransparency false in
/-- Cancellation with the specified P-action, promoted to the literal exterior
P tensor E action rather than merely a k-linear equivalence. -/
def exteriorCoefficientIso (σ : P →ₐ[k] T) :
    (ModuleCat.extendScalars (Algebra.TensorProduct.includeLeft : P →ₐ[k] P ⊗[k] E).toRingHom).obj
        ((ModuleCat.restrictScalars σ.toRingHom).obj (ModuleCat.of T T)) ≅
      (ModuleCat.restrictScalars (exteriorCoefficientMap (E := E) σ).toRingHom).obj
        (ModuleCat.of (T ⊗[k] E) (T ⊗[k] E)) := by
  letI : Algebra P T := σ.toRingHom.toAlgebra
  letI : IsScalarTower k P T := IsScalarTower.of_algHom σ
  let c : ((P ⊗[k] E) ⊗[P] T) ≃ₐ[P] T ⊗[k] E :=
    (Algebra.TensorProduct.comm P (P ⊗[k] E) T).trans
      (Algebra.TensorProduct.cancelBaseChange k P P T E)
  have hc (s : P ⊗[k] E) :
      c (s ⊗ₜ[P] (1 : T)) = exteriorCoefficientMap σ s := by
    induction s using TensorProduct.inductionOn with
    | tmul p e =>
      simp [c, exteriorCoefficientMap, Algebra.smul_def]
      rfl
    | add s t hs ht => simp [TensorProduct.add_tmul, hs, ht]
  let Q := (ModuleCat.restrictScalars
    (Algebra.TensorProduct.includeLeft : P →ₐ[k] P ⊗[k] E).toRingHom).obj
    (ModuleCat.of (P ⊗[k] E) (P ⊗[k] E))
  letI : IsScalarTower P (P ⊗[k] E) Q := IsScalarTower.of_compHom P (P ⊗[k] E) _
  let eQ : Q ≃ₗ[P ⊗[k] E] P ⊗[k] E := LinearEquiv.refl _ _
  let eT : ((ModuleCat.restrictScalars σ.toRingHom).obj (ModuleCat.of T T)) ≃ₗ[P] T :=
    LinearEquiv.refl _ _
  let d := TensorProduct.AlgebraTensorModule.congr eQ eT
  refine d.toModuleIso ≪≫ ?_
  exact LinearEquiv.toModuleIso
    (X₁ := ModuleCat.of (P ⊗[k] E) ((P ⊗[k] E) ⊗[P] T))
    (X₂ := (ModuleCat.restrictScalars (exteriorCoefficientMap (E := E) σ).toRingHom).obj
      (ModuleCat.of (T ⊗[k] E) (T ⊗[k] E)))
    { c.toAddEquiv with
      map_smul' := fun s x => by
        change c (s • x) = exteriorCoefficientMap σ s * c x
        induction x using TensorProduct.inductionOn with
        | tmul s' t =>
          change c ((s * s') ⊗ₜ[P] t) = _
          rw [show (s * s') ⊗ₜ[P] t =
            (s ⊗ₜ[P] (1 : T)) * (s' ⊗ₜ[P] t) by simp]
          rw [map_mul, hc]
        | add x y hx hy => simp [smul_add, hx, hy, mul_add] }

/-- Scalar extension commutes with the actual recursive coefficient complex. -/
def coefficientExtendIso {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (M : ModuleCat R) : (s : List R) →
    crossMappedComplex (ModuleCat.extendScalars f) (coefficientComplex M s) ≅
      coefficientComplex ((ModuleCat.extendScalars f).obj M) (s.map f)
  | [] => (HomologicalComplex.singleMapHomologicalComplex (ModuleCat.extendScalars f)
      (ComplexShape.down ℕ) 0).app M
  | a :: s => singleTensorCrossMapIso (ModuleCat.extendScalars f) a (f a)
      (coefficientComplex M s) (extendScalars_map_lsmul f a) ≪≫
        whiskerLeftIso (singleComplex S (f a)) (coefficientExtendIso f M s)

/-- The literal exterior quotient on the additional factor. -/
def exteriorAmbientMap (q : W →ₐ[k] E) : P ⊗[k] W →ₐ[k] P ⊗[k] E :=
  Algebra.TensorProduct.map (AlgHom.id k P) q

/-- The exterior support map factors through extension in the additional coefficient. -/
theorem exteriorCoefficientMap_comp (σ : P →ₐ[k] T) (q : W →ₐ[k] E) :
    (exteriorCoefficientMap σ).comp (exteriorAmbientMap q) =
      Algebra.TensorProduct.map σ q := by
  ext <;> simp [exteriorCoefficientMap, exteriorAmbientMap]

/-- The first-stage list is literally the same list after the exterior quotient. -/
theorem exterior_mappedList (q : W →ₐ[k] E) (t : List P) :
    (t.map (Algebra.TensorProduct.includeLeft : P →ₐ[k] P ⊗[k] W)).map
        (exteriorAmbientMap q) =
      t.map (Algebra.TensorProduct.includeLeft : P →ₐ[k] P ⊗[k] E) := by
  simp only [List.map_map]
  congr 1
  funext p
  simp [exteriorAmbientMap]

/-- The actual exterior coefficient complex agrees with flat-factor extension,
restricted along the literal additional-factor map. No flatness of q is used. -/
def exteriorCoefficientChainIso (σ : P →ₐ[k] T) (q : W →ₐ[k] E) (t : List P) :
    coefficientComplex
        ((ModuleCat.restrictScalars (Algebra.TensorProduct.map σ q).toRingHom).obj
          (ModuleCat.of (T ⊗[k] E) (T ⊗[k] E)))
        (t.map (Algebra.TensorProduct.includeLeft : P →ₐ[k] P ⊗[k] W)) ≅
      crossMappedComplex (ModuleCat.restrictScalars (exteriorAmbientMap q).toRingHom)
        (crossMappedComplex
          (ModuleCat.extendScalars
            (Algebra.TensorProduct.includeLeft : P →ₐ[k] P ⊗[k] E).toRingHom)
          (coefficientComplex
            ((ModuleCat.restrictScalars σ.toRingHom).obj (ModuleCat.of T T)) t)) := by
  let f := (Algebra.TensorProduct.includeLeft : P →ₐ[k] P ⊗[k] E).toRingHom
  let ρ := (exteriorAmbientMap (P := P) q).toRingHom
  let M := (ModuleCat.restrictScalars σ.toRingHom).obj (ModuleCat.of T T)
  let N := (ModuleCat.extendScalars f).obj M
  let F := (ModuleCat.restrictScalars ρ).mapHomologicalComplex (ComplexShape.down ℕ)
  let e := ModuleCat.restrictScalarsComp'App ρ (exteriorCoefficientMap σ).toRingHom
    (Algebra.TensorProduct.map σ q).toRingHom
    (congrArg AlgHom.toRingHom (exteriorCoefficientMap_comp σ q)).symm
    (ModuleCat.of (T ⊗[k] E) (T ⊗[k] E)) ≪≫
      (ModuleCat.restrictScalars ρ).mapIso (exteriorCoefficientIso σ).symm
  exact coefficientIso e _ ≪≫ coefficientRestrictIso ρ N _ ≪≫
    F.mapIso (eqToIso (congrArg (coefficientComplex N) (exterior_mappedList q t)) ≪≫
      (coefficientExtendIso f M t).symm)

/-- Base change of a flat k-module makes the actual inclusion P to P tensor E flat. -/
theorem exteriorIncludeLeft_flat [Module.Flat k E] :
    (Algebra.TensorProduct.includeLeft : P →ₐ[k] P ⊗[k] E).toRingHom.Flat := by
  change (algebraMap P (P ⊗[k] E)).Flat
  exact RingHom.flat_algebraMap_iff.mpr inferInstance

/-- The exterior chain map commutes with its actual differentials. -/
theorem exteriorCoefficientChainIso_hom_comm (σ : P →ₐ[k] T) (q : W →ₐ[k] E)
    (t : List P) (i j : ℕ) :
    (exteriorCoefficientChainIso σ q t).hom.f i ≫
        (crossMappedComplex (ModuleCat.restrictScalars (exteriorAmbientMap q).toRingHom)
          (crossMappedComplex
            (ModuleCat.extendScalars
              (Algebra.TensorProduct.includeLeft : P →ₐ[k] P ⊗[k] E).toRingHom)
            (coefficientComplex
              ((ModuleCat.restrictScalars σ.toRingHom).obj (ModuleCat.of T T)) t))).d i j =
      (coefficientComplex
        ((ModuleCat.restrictScalars (Algebra.TensorProduct.map σ q).toRingHom).obj
          (ModuleCat.of (T ⊗[k] E) (T ⊗[k] E)))
        (t.map (Algebra.TensorProduct.includeLeft : P →ₐ[k] P ⊗[k] W))).d i j ≫
          (exteriorCoefficientChainIso σ q t).hom.f j :=
  (exteriorCoefficientChainIso σ q t).hom.comm i j

/-- Actual first-stage homology is flat exterior extension followed by exact
restriction. The additional-factor map q need not be flat. -/
def exteriorCoefficientHomologyIso [Module.Flat k E]
    (σ : P →ₐ[k] T) (q : W →ₐ[k] E) (t : List P) (n : ℕ) :
    (coefficientComplex
      ((ModuleCat.restrictScalars (Algebra.TensorProduct.map σ q).toRingHom).obj
        (ModuleCat.of (T ⊗[k] E) (T ⊗[k] E)))
      (t.map (Algebra.TensorProduct.includeLeft : P →ₐ[k] P ⊗[k] W))).homology n ≅
    (ModuleCat.restrictScalars (exteriorAmbientMap q).toRingHom).obj
      ((ModuleCat.extendScalars
        (Algebra.TensorProduct.includeLeft : P →ₐ[k] P ⊗[k] E).toRingHom).obj
        ((coefficientComplex
          ((ModuleCat.restrictScalars σ.toRingHom).obj (ModuleCat.of T T)) t).homology n)) :=
  (HomologicalComplex.homologyFunctor (ModuleCat (P ⊗[k] W)) (ComplexShape.down ℕ) n).mapIso
      (exteriorCoefficientChainIso σ q t) ≪≫
    _root_.ModuleCat.TorComparison.ambientRestrictHomologyIso (exteriorAmbientMap q).toRingHom _ n
        ≪≫
    (ModuleCat.restrictScalars (exteriorAmbientMap q).toRingHom).mapIso
      (_root_.ModuleCat.TorComparison.flatExtendHomologyIso
        (Algebra.TensorProduct.includeLeft : P →ₐ[k] P ⊗[k] E).toRingHom
        exteriorIncludeLeft_flat _ n).symm

end ChainComplex.Koszul
