/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.GenericFiber.GenericFiberSectionNorm
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Frames.FiniteNeighborhood
public import Aglib.AlgebraicGeometry.Modules.StructureSheaf.Hom
public import Aglib.AlgebraicGeometry.Modules.Pullback.FlatMorphism
public import Aglib.AlgebraicGeometry.Modules.IsomorphismFunctors
public import Aglib.AlgebraicGeometry.Cohomology.Proper.StructureSheaf.Localization
public import Mathlib.RingTheory.Artinian.Module

/-!
# Canonical generic ratio of two regular line-bundle maps

A monic line-bundle map on a finite scheme over a field is invertible. Applying
this to the literal generic fiber defines the ratio of the two original maps,
without a source function field or a supplied rational function.


Intended upstream module:
`Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.GenericFiber.GenericFiberLineRatio`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.GenericFiber.GenericFiberChartLineRatio`,
`Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.GenericFiber.GenericFiberFactorizationRatio`,
`Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.GenericFiber.GenericFiberLineRatioInverse`,
`Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.GenericFiber.GenericFiberLineRatioScalar`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- Global structure-module multiplication remembers its original section. -/
theorem unitMul_injective (X : Scheme.{u}) : Function.Injective (unitMul X) := by
  intro a b h
  have h' := congrArg (fun k : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ _ =>
    Hom.app k ⊤ (1 : Γ(X, ⊤))) h
  simpa [unitMul_app] using h'

/-- Every structure-module endomorphism is multiplication by its value on one. -/
theorem unitEnd_eq_unitMul (X : Scheme.{u})
    (θ : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    θ = unitMul X (Hom.app θ ⊤ (1 : Γ(X, ⊤))) := by
  apply (unitHomGlobalSectionsEquiv X _).injective
  simp [unitHomGlobalSectionsEquiv_apply, unitMul_app]

/-- A monic structure-module endomorphism over an Artinian section ring is invertible. -/
theorem isIso_unitEnd_of_mono_of_isArtinianRing (X : Scheme.{u})
    [IsArtinianRing Γ(X, ⊤)]
    (θ : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶
      SheafOfModules.unit X.ringCatSheaf) [Mono θ] : IsIso θ := by
  let a : Γ(X, ⊤) := Hom.app θ ⊤ (1 : Γ(X, ⊤))
  have he : θ = unitMul X a := unitEnd_eq_unitMul X θ
  have hr : IsRightRegular a := by
    intro x y h
    apply unitMul_injective X
    apply (cancel_mono θ).mp
    rw [he, ← unitMul_mul, ← unitMul_mul]
    exact congrArg (unitMul X) h
  obtain ⟨a', ha'⟩ := IsArtinianRing.isUnit_iff_isRightRegular.mpr hr
  rw [he, ← ha']
  exact (unitMulIso X a').isIso_hom

namespace Invertible

/-- On a finite scheme over a field, every original monic line-bundle map
is an isomorphism, including disconnected and nonreduced schemes. -/
theorem isIso_of_mono_of_finite_over_field (K : Type u) [Field K]
    {X : Scheme.{u}} (q : X ⟶ Spec (.of K)) [IsFinite q] (L : LineBundle X)
    (φ : L.val ⟶ SheafOfModules.unit X.ringCatSheaf) [Mono φ] : IsIso φ := by
  have : IsAffine X := isAffine_of_isAffineHom q
  have hs : (Set.univ : Set X).Finite := by
    convert q.finite_preimage_singleton (IsLocalRing.closedPoint K) using 1
    ext x
    simp [Subsingleton.elim (q x) (IsLocalRing.closedPoint K)]
  obtain ⟨U, hU, ⟨e⟩⟩ := exists_open_unitIso_around_finite X L Set.univ hs
  have htop : U = ⊤ := le_antisymm le_top hU
  have : IsIso U.ι := isIso_of_isOpenImmersion_of_opensRange_eq_top U.ι
    (by simpa using htop)
  let θ := e.inv ≫ (restrictFunctor U.ι).map φ ≫ (restrictUnitIso U.ι).hom
  have : Mono θ := by dsimp [θ]; infer_instance
  let : Algebra K Γ(U.toScheme, ⊤) :=
    (FiniteSchemeNormBaseChange.scalarMap (U.ι ≫ q)).toAlgebra
  let : Module.Finite K Γ(U.toScheme, ⊤) :=
    FiniteSchemeNormBaseChange.sections_finite (U.ι ≫ q)
  let : IsArtinianRing Γ(U.toScheme, ⊤) := IsArtinianRing.of_finite K _
  have : IsIso θ := isIso_unitEnd_of_mono_of_isArtinianRing U.toScheme θ
  have : IsIso ((restrictFunctor U.ι).map φ) := by
    simpa only [θ, isIso_comp_left_iff, isIso_comp_right_iff] using this
  have : IsIso ((pullback U.ι).map φ) :=
    (NatIso.isIso_map_iff (restrictFunctorIsoPullback U.ι) φ).mp inferInstance
  let := pullback_isEquivalence_of_isIso U.ι
  exact isIso_of_reflects_iso φ (pullback U.ι)

end Invertible
end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme

open Modules Modules.Invertible

variable {C T : Scheme.{u}} [IsIntegral T] (f : C ⟶ T) [IsFinite f]
  (L : LineBundle C)

/-- The original line-bundle map pulled to the literal whole generic fiber. -/
def genericFiberLineMap (φ : L.val ⟶ SheafOfModules.unit C.ringCatSheaf) :=
  (Modules.pullback (pullback.fst f (T.fromSpecStalk (genericPoint T)))).map φ ≫
    (Modules.pullbackUnitIso (pullback.fst f (T.fromSpecStalk (genericPoint T)))).hom

instance genericFiberLineMap_isIso
    (φ : L.val ⟶ SheafOfModules.unit C.ringCatSheaf) [Mono φ] :
    IsIso (genericFiberLineMap f L φ) := by
  let p := pullback.fst f (T.fromSpecStalk (genericPoint T))
  have : Flat p := by dsimp [p]; infer_instance
  have : Mono (genericFiberLineMap f L φ) := by
    dsimp [genericFiberLineMap]
    infer_instance
  exact Modules.Invertible.isIso_of_mono_of_finite_over_field T.functionField
    (pullback.snd f (T.fromSpecStalk (genericPoint T)))
    (Modules.Invertible.pullbackLineBundle p L) (genericFiberLineMap f L φ)

/-- The canonical ratio has the specified order: inverse denominator followed
by the original numerator map. No frame is chosen in this definition. -/
def genericFiberLineRatioIso
    (φ ψ : L.val ⟶ SheafOfModules.unit C.ringCatSheaf) [Mono φ] [Mono ψ] :=
  let : IsIso (genericFiberLineMap f L φ) := genericFiberLineMap_isIso f L φ
  let : IsIso (genericFiberLineMap f L ψ) := genericFiberLineMap_isIso f L ψ
  (asIso (genericFiberLineMap f L ψ)).symm ≪≫ asIso (genericFiberLineMap f L φ)

/-- The actual invertible global section of the whole generic fiber. -/
def genericFiberLineRatioUnit
    (φ ψ : L.val ⟶ SheafOfModules.unit C.ringCatSheaf) [Mono φ] [Mono ψ] :
    (Γ(pullback f (T.fromSpecStalk (genericPoint T)), ⊤))ˣ := by
  let X := pullback f (T.fromSpecStalk (genericPoint T))
  let e := genericFiberLineRatioIso f L φ ψ
  refine ⟨Modules.Hom.app e.hom ⊤ (1 : Γ(X, ⊤)), Modules.Hom.app e.inv ⊤ (1 : Γ(X, ⊤)), ?_, ?_⟩
  · apply Modules.unitMul_injective X
    rw [Modules.unitMul_mul, ← Modules.unitEnd_eq_unitMul X e.hom,
      ← Modules.unitEnd_eq_unitMul X e.inv, e.hom_inv_id, Modules.unitMul_one]
  · apply Modules.unitMul_injective X
    rw [Modules.unitMul_mul, ← Modules.unitEnd_eq_unitMul X e.inv,
      ← Modules.unitEnd_eq_unitMul X e.hom, e.inv_hom_id, Modules.unitMul_one]

/-- Determinant norm of the canonical original-map ratio in the target function field. -/
def genericFiberLineRatioNorm
    (φ ψ : L.val ⟶ SheafOfModules.unit C.ringCatSheaf) [Mono φ] [Mono ψ] :
    T.functionField :=
  let q := pullback.snd f (T.fromSpecStalk (genericPoint T))
  let : IsFinite q := by dsimp [q]; infer_instance
  let : Algebra T.functionField Γ(pullback f (T.fromSpecStalk (genericPoint T)), ⊤) :=
    (FiniteSchemeNormBaseChange.scalarMap q).toAlgebra
  let : Module.Finite T.functionField
      Γ(pullback f (T.fromSpecStalk (genericPoint T)), ⊤) :=
    FiniteSchemeNormBaseChange.sections_finite q
  Algebra.norm T.functionField (genericFiberLineRatioUnit f L φ ψ).val

end AlgebraicGeometry.Scheme
