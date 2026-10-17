/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.KoszulScalarRestriction
public import Motivic.Algebra.Homology.KoszulHyperhomologyExact

/-!
# Finite-list Koszul tensor restriction for arbitrary complexes

For every commutative-ring map, restricting the actual target-ring Koszul
tensor of an arbitrary complex is naturally isomorphic to the source-ring
Koszul tensor of its restriction. The construction uses the genuine
one-equation two-column comparison and the actual tensor associator.
Naturality holds for arbitrary chain maps and the component maps commute
with actual differentials. No finite, flat, or surjective hypothesis occurs.
Exact restriction identifies homology; flat scalar extension and geometric
stalk comparisons remain separate statements.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory

namespace Motivic.Koszul

variable {R S : Type u} [CommRing R] [CommRing S]

/-- The literal termwise restriction functor on nonnegative chain complexes. -/
abbrev restrictChainFunctor (f : R →+* S) :
    ChainComplex (ModuleCat S) ℕ ⥤ ChainComplex (ModuleCat R) ℕ :=
  (ModuleCat.restrictScalars f).mapHomologicalComplex (ComplexShape.down ℕ)

set_option backward.isDefEq.respectTransparency false in
/-- The actual one-equation comparison is natural in arbitrary chain maps. -/
def singleTensorRestrictNatIso (f : R →+* S) (a : R) :
    singleTensorFunctor (f a) ⋙ restrictChainFunctor f ≅
      restrictChainFunctor f ⋙ singleTensorFunctor a :=
  NatIso.ofComponents (fun K => (singleTensorRestrictIso f a K).symm) (by
    intro K L g
    apply HomologicalComplex.Hom.ext
    funext n
    change (ModuleCat.restrictScalars f).map (((singleComplex S (f a)) ◁ g).f n) ≫
        singleTensorCrossMapToX (ModuleCat.restrictScalars f) (f a) a L n =
      singleTensorCrossMapToX (ModuleCat.restrictScalars f) (f a) a K n ≫
        (((singleComplex R a) ◁ (restrictChainFunctor f).map g).f n)
    cases n with
    | zero =>
      apply crossMappedSingleTensor_hom_ext_zero (ModuleCat.restrictScalars f) (f a) K
      rw [← Category.assoc, ← Functor.map_comp, singleTensorιZero_naturality,
        Functor.map_comp, Category.assoc, crossMappedιZero_singleTensorCrossMapToX]
      rw [← Category.assoc, crossMappedιZero_singleTensorCrossMapToX,
        singleTensorιZero_naturality]
      rfl
    | succ n =>
      apply crossMappedSingleTensor_hom_ext (ModuleCat.restrictScalars f) (f a) K n
      · rw [← Category.assoc, ← Functor.map_comp, singleTensorιZero_naturality,
          Functor.map_comp, Category.assoc, crossMappedιZero_singleTensorCrossMapToX]
        rw [← Category.assoc, crossMappedιZero_singleTensorCrossMapToX,
          singleTensorιZero_naturality]
        rfl
      · rw [← Category.assoc, ← Functor.map_comp, singleTensorιOne_naturality,
          Functor.map_comp, Category.assoc, crossMappedιOne_singleTensorCrossMapToX]
        rw [← Category.assoc, crossMappedιOne_singleTensorCrossMapToX,
          singleTensorιOne_naturality]
        rfl)

/-- The finite-list comparison is a natural isomorphism of actual chain functors. -/
def koszulTensorRestrictNatIso (f : R →+* S) : (s : List R) →
    koszulTensorFunctor (s.map f) ⋙ restrictChainFunctor f ≅
      restrictChainFunctor f ⋙ koszulTensorFunctor s
  | [] =>
      Functor.isoWhiskerRight (leftUnitorNatIso (ChainComplex (ModuleCat S) ℕ))
          (restrictChainFunctor f) ≪≫
        Functor.leftUnitor (restrictChainFunctor f) ≪≫
        (Functor.rightUnitor (restrictChainFunctor f)).symm ≪≫
        Functor.isoWhiskerLeft (restrictChainFunctor f)
          (leftUnitorNatIso (ChainComplex (ModuleCat R) ℕ)).symm
  | a :: s =>
      Functor.isoWhiskerRight (tensorLeftTensor (singleComplex S (f a)) (chainComplex (s.map f)))
          (restrictChainFunctor f) ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (koszulTensorFunctor (s.map f)) (singleTensorRestrictNatIso f a) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (koszulTensorRestrictNatIso f s) (singleTensorFunctor a) ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (restrictChainFunctor f)
          (tensorLeftTensor (singleComplex R a) (chainComplex s)).symm

/-- The actual arbitrary-complex finite-list scalar restriction isomorphism. -/
def koszulTensorRestrictIso (f : R →+* S) (s : List R)
    (K : ChainComplex (ModuleCat S) ℕ) :
    crossMappedComplex (ModuleCat.restrictScalars f)
        (HomologicalComplex.tensorObj (chainComplex (s.map f)) K) ≅
      HomologicalComplex.tensorObj (chainComplex s)
        (crossMappedComplex (ModuleCat.restrictScalars f) K) :=
  (koszulTensorRestrictNatIso f s).app K

/-- The finite-list comparison commutes with every actual chain map. -/
theorem koszulTensorRestrictIso_naturality (f : R →+* S) (s : List R)
    {K L : ChainComplex (ModuleCat S) ℕ} (g : K ⟶ L) :
    (restrictChainFunctor f).map ((koszulTensorFunctor (s.map f)).map g) ≫
        (koszulTensorRestrictIso f s L).hom =
      (koszulTensorRestrictIso f s K).hom ≫
        (koszulTensorFunctor s).map ((restrictChainFunctor f).map g) :=
  (koszulTensorRestrictNatIso f s).hom.naturality g

/-- Every component square uses the literal differentials and restriction map. -/
theorem koszulTensorRestrictIso_hom_comm (f : R →+* S) (s : List R)
    (K : ChainComplex (ModuleCat S) ℕ) (i j : ℕ) :
    (koszulTensorRestrictIso f s K).hom.f i ≫
        (HomologicalComplex.tensorObj (chainComplex s)
          (crossMappedComplex (ModuleCat.restrictScalars f) K)).d i j =
      (ModuleCat.restrictScalars f).map
          ((HomologicalComplex.tensorObj (chainComplex (s.map f)) K).d i j) ≫
        (koszulTensorRestrictIso f s K).hom.f j :=
  (koszulTensorRestrictIso f s K).hom.comm i j

/-- Exact restriction compares actual homology for every scalar map.
This is not a flat-base-change assertion or an equality of lengths. -/
def koszulTensorRestrictHomologyIso (f : R →+* S) (s : List R)
    (K : ChainComplex (ModuleCat S) ℕ) (n : ℕ) :
    (HomologicalComplex.tensorObj (chainComplex s)
        (crossMappedComplex (ModuleCat.restrictScalars f) K)).homology n ≅
      (ModuleCat.restrictScalars f).obj
        ((HomologicalComplex.tensorObj (chainComplex (s.map f)) K).homology n) :=
  (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) n).mapIso
      (koszulTensorRestrictIso f s K).symm ≪≫
    Motivic.TorComparison.ambientRestrictHomologyIso f
      (HomologicalComplex.tensorObj (chainComplex (s.map f)) K) n

end Motivic.Koszul
