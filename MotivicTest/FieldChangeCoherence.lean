/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.SuslinVoevodsky.FieldChangeCoherence

/-!
# Consumers of the actual whole-support field-tower comparisons

These tests use the original signed field-change map and arbitrary field
homomorphisms. They do not infer all-degree raw or derived coherence from the
support comparison alone.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.AlgebraicGeometry.Scheme (fundamentalCycle genericMultiplicity
  isNoetherian_of_finiteType)
open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open _root_.AlgebraicGeometry.Scheme.Cycles.BaseChange.ComponentDecomposition
open scoped BigOperators

universe u

namespace MotivicTest.FieldChangeCoherence
open _root_.AlgebraicGeometry.Scheme (IntegralCycle SmoothSite)

/-- Generic flat tower comparison, with neither a reducedness assumption nor
finite type of either base change. -/
theorem arbitraryFlatTower {P S T U : Scheme.{u}}
    (p : P ⟶ S) (t : T ⟶ S) (s : U ⟶ T)
    [Flat s] [IsNoetherian (pullback p t : Scheme.{u})]
    [IsNoetherian (pullback p (s ≫ t) : Scheme.{u})] :
    let : IsNoetherian (pullback (pullback.snd p t) s : Scheme.{u}) :=
      isNoetherian_of_finiteType (pullbackTowerIso p t s).hom
    let := IntegralCycle.genericPointFintype (pullback p t : Scheme.{u})
    let : ∀ z : genericPoints (pullback p t : Scheme.{u}),
        IsNoetherian (componentExterior (pullback.snd p t) s z) :=
      fun z => isNoetherian_of_finiteType
        (componentExteriorInclusion (pullback.snd p t) s z)
    fundamentalCycle (pullback p (s ≫ t)) =
      ∑ z : genericPoints (pullback p t : Scheme.{u}),
        (genericMultiplicity z : ℤ) •
          IntegralCycle.finitePushforward
            (componentExteriorInclusion (pullback.snd p t) s z ≫
              (pullbackTowerIso p t s).hom)
            (fundamentalCycle (componentExterior (pullback.snd p t) s z)) :=
  fundamentalCycle_pullbackTower_eq_component_sum p t s

variable {k L M : Type u} [Field k] [Field L] [Field M]
  (φ : k →+* L) (ψ : L →+* M)
  {X Y : SmoothSite.overField k} (A : FiniteCorrespondenceGenerator X.hom Y.hom)

/-- The first projection on a literal identity-field support is an isomorphism. -/
example : IsIso (A.fieldBaseChangeSupportToOriginal (RingHom.id k)) := inferInstance

/-- The comparison uses the two literal old-support projections. -/
theorem towerOriginalProjection :
    (A.fieldBaseChangeSupportTowerIso φ ψ).hom ≫
        A.fieldBaseChangeSupportToOriginal (ψ.comp φ) =
      pullback.fst (A.fieldBaseChangeSupportHom φ) (Spec.map (CommRingCat.ofHom ψ)) ≫
        A.fieldBaseChangeSupportToOriginal φ :=
  A.fieldBaseChangeSupportTowerIso_hom_original φ ψ

/-- The original signed composite-field map retains every whole tower
multiplicity, for arbitrary positive or negative integer coefficients. -/
theorem signedCompositeGenerator (n : ℤ) :
    FiniteCorrespondence.toIntegralCycle
      (FiniteCorrespondence.fieldBaseChange (X := X) (Y := Y) (ψ.comp φ)
        (Finsupp.single A n)) =
      n • IntegralCycle.finitePushforward
        ((A.fieldBaseChangeSupportTowerIso φ ψ).hom ≫ A.fieldBaseChangeInclusion (ψ.comp φ))
        (fundamentalCycle (A.fieldBaseChangeTowerSupport φ ψ)) := by
  rw [FiniteCorrespondence.toIntegralCycle_fieldBaseChange_single,
    IntegralCycle.finitePushforward_comp, AddMonoidHom.comp_apply,
    A.finitePushforward_fieldBaseChangeSupportTower_fundamentalCycle φ ψ]

/-- The direct original generator cycle retains the intermediate nonreduced
lengths and every second-pullback branch. -/
theorem compositeGeneratorComponents :
    let := IntegralCycle.genericPointFintype (A.fieldBaseChangeSupport φ)
    let : ∀ z : genericPoints (A.fieldBaseChangeSupport φ),
        IsNoetherian (componentExterior (A.fieldBaseChangeSupportHom φ)
          (Spec.map (CommRingCat.ofHom ψ)) z) :=
      fun z => isNoetherian_of_finiteType
        (componentExteriorInclusion (A.fieldBaseChangeSupportHom φ)
          (Spec.map (CommRingCat.ofHom ψ)) z)
    FiniteCorrespondence.toIntegralCycle (A.fieldBaseChangeCycle (ψ.comp φ)) =
      ∑ z : genericPoints (A.fieldBaseChangeSupport φ), (genericMultiplicity z : ℤ) •
        IntegralCycle.finitePushforward
          (componentExteriorInclusion (A.fieldBaseChangeSupportHom φ)
            (Spec.map (CommRingCat.ofHom ψ)) z ≫
              (A.fieldBaseChangeSupportTowerIso φ ψ).hom ≫
                A.fieldBaseChangeInclusion (ψ.comp φ))
          (fundamentalCycle (componentExterior (A.fieldBaseChangeSupportHom φ)
            (Spec.map (CommRingCat.ofHom ψ)) z)) :=
  A.toIntegralCycle_fieldBaseChangeCycle_comp φ ψ

/-- The original signed map itself satisfies the tower law in its faithful
cycle realization, with the actual canonical smooth-site product comparison. -/
theorem allSignedTower (α : FiniteCorrespondence X.hom Y.hom) :
    IntegralCycle.finitePushforward (SmoothSite.fieldBaseChangeProductTowerIso φ ψ X Y).hom
      (FiniteCorrespondence.toIntegralCycle
        (FiniteCorrespondence.fieldBaseChange
          (X := (SmoothSite.fieldBaseChange φ).obj X)
          (Y := (SmoothSite.fieldBaseChange φ).obj Y) ψ
          (FiniteCorrespondence.fieldBaseChange (X := X) (Y := Y) φ α))) =
      FiniteCorrespondence.toIntegralCycle
        (FiniteCorrespondence.fieldBaseChange (X := X) (Y := Y) (ψ.comp φ) α) :=
  FiniteCorrespondence.toIntegralCycle_fieldBaseChange_comp φ ψ α

/-- The same equality uses the original public correspondence functors. -/
theorem originalCorTower {X Y : Cor k} (α : X ⟶ Y) :
    IntegralCycle.finitePushforward
      (SmoothSite.fieldBaseChangeProductTowerIso φ ψ X.toSmoothSite Y.toSmoothSite).hom
      (FiniteCorrespondence.toIntegralCycle
        (f := ((SmoothSite.fieldBaseChange ψ).obj
          ((SmoothSite.fieldBaseChange φ).obj X.toSmoothSite)).hom)
        (g := ((SmoothSite.fieldBaseChange ψ).obj
          ((SmoothSite.fieldBaseChange φ).obj Y.toSmoothSite)).hom)
        ((Cor.fieldBaseChange ψ).map ((Cor.fieldBaseChange φ).map α))) =
      FiniteCorrespondence.toIntegralCycle
        (f := ((SmoothSite.fieldBaseChange (ψ.comp φ)).obj X.toSmoothSite).hom)
        (g := ((SmoothSite.fieldBaseChange (ψ.comp φ)).obj Y.toSmoothSite).hom)
        ((Cor.fieldBaseChange (ψ.comp φ)).map α) :=
  FiniteCorrespondence.toIntegralCycle_fieldBaseChange_comp φ ψ α

/-- The identity case also uses the original public correspondence functor,
with the canonical ambient comparison given by actual pullback projections. -/
theorem originalCorIdentity {X Y : Cor k} (α : X ⟶ Y) :
    IntegralCycle.finitePushforward
      (SmoothSite.fieldBaseChangeProductIdIso k X.toSmoothSite Y.toSmoothSite).hom
      (FiniteCorrespondence.toIntegralCycle ((Cor.fieldBaseChange (RingHom.id k)).map α)) =
      FiniteCorrespondence.toIntegralCycle α :=
  FiniteCorrespondence.toIntegralCycle_fieldBaseChange_id α

open FiniteCorrespondenceGenerator in
open Lean in
run_cmd do
  for name in #[``AlgebraicGeometry.pullbackIdentityIso,
      ``AlgebraicGeometry.pullbackIdentityIso_inv,
      ``AlgebraicGeometry.pullbackTowerIso,
      ``AlgebraicGeometry.pullbackTowerIso_hom_fst,
      ``AlgebraicGeometry.pullbackTowerIso_hom_snd,
      ``AlgebraicGeometry.finitePushforward_pullbackIdentity_fundamentalCycle,
      ``AlgebraicGeometry.finitePushforward_pullbackTower_fundamentalCycle,
      ``AlgebraicGeometry.fundamentalCycle_pullbackTower_eq_component_sum,
      ``fieldBaseChangeSupportIdIso,
      ``finitePushforward_fieldBaseChangeSupportId_fundamentalCycle,
      ``fieldBaseChangeSupportTowerIso,
      ``fieldBaseChangeSupportTowerIso_hom_original,
      ``fieldBaseChangeSupportTowerIso_hom_base,
      ``finitePushforward_fieldBaseChangeSupportTower_fundamentalCycle,
      ``fieldBaseChangeSupport_comp_fundamentalCycle,
      ``toIntegralCycle_fieldBaseChangeCycle_comp,
      ``fieldBaseChangeComponentSecondIso,
      ``fieldBaseChangeComponentSecondIso_hom_original,
      ``fieldBaseChangeComponentSecondIso_hom_base,
      ``toIntegralCycle_fieldBaseChangeComponentCycle,
      ``toIntegralCycle_fieldBaseChangeCycle_iterated,
      ``_root_.AlgebraicGeometry.Scheme.SmoothSite.fieldBaseChangeComp_inv_original,
      ``_root_.AlgebraicGeometry.Scheme.SmoothSite.fieldBaseChangeComp_inv_base,
      ``_root_.AlgebraicGeometry.Scheme.SmoothSite.fieldBaseChangeProductTowerIso,
      ``_root_.AlgebraicGeometry.Scheme.SmoothSite.fieldBaseChangeProductTowerIso_hom_fst,
      ``_root_.AlgebraicGeometry.Scheme.SmoothSite.fieldBaseChangeProductTowerIso_hom_snd,
      ``fieldBaseChangeComponentSecondIso_hom_ambient,
      ``toIntegralCycle_fieldBaseChange_comp_cycle,
      ``FiniteCorrespondence.toIntegralCycle_fieldBaseChange_comp,
      ``_root_.AlgebraicGeometry.Scheme.IntegralCycle.finitePushforward_congr,
      ``_root_.AlgebraicGeometry.Scheme.SmoothSite.fieldBaseChangeIdProjection_isIso,
      ``_root_.AlgebraicGeometry.Scheme.SmoothSite.fieldBaseChangeObjectIdIso,
      ``_root_.AlgebraicGeometry.Scheme.SmoothSite.fieldBaseChangeObjectIdIso_hom_left,
      ``_root_.AlgebraicGeometry.Scheme.SmoothSite.fieldBaseChangeProductIdIso,
      ``_root_.AlgebraicGeometry.Scheme.SmoothSite.fieldBaseChangeProductIdIso_hom_fst,
      ``_root_.AlgebraicGeometry.Scheme.SmoothSite.fieldBaseChangeProductIdIso_hom_snd,
      ``fieldBaseChangeSupportIdIso_hom_ambient,
      ``toIntegralCycle_fieldBaseChange_id_cycle,
      ``FiniteCorrespondence.toIntegralCycle_fieldBaseChange_id,
      ``arbitraryFlatTower, ``towerOriginalProjection,
      ``signedCompositeGenerator, ``compositeGeneratorComponents,
      ``allSignedTower, ``originalCorTower, ``originalCorIdentity] do
    let dependencies ← collectAxioms name
    for dependency in dependencies do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual field-change cycle identity and tower comparisons use only standard foundations."

end MotivicTest.FieldChangeCoherence
