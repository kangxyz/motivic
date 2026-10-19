/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Cycles.FundamentalCycle

/-!
# Isomorphism invariance of fundamental cycles

The actual generic local lengths are invariant under scheme isomorphisms.
The induced finite pushforward therefore takes the fundamental cycle to the
fundamental cycle, including its nonreduced multiplicities.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.Hom

/-- A ring isomorphism preserves the length of the ring as a module over itself. -/
theorem ringLength_eq_of_ringEquiv {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (e : R ≃+* S) : Module.length R R = Module.length S S := by
  let := RingHomInvPair.of_ringEquiv e
  let := RingHomInvPair.symm (↑e : R →+* S) (e.symm : S →+* R)
  apply WithBot.coe_injective
  rw [Module.coe_length, Module.coe_length]
  exact Order.krullDim_eq_of_orderIso
    (Submodule.orderIsoMapComapOfBijective e.toSemilinearEquiv.toLinearMap e.bijective)

variable {X Y : Scheme.{u}}

/-- An open immersion preserves the actual local-ring length at its points. -/
theorem stalk_length_eq_of_isOpenImmersion (f : X ⟶ Y) [IsOpenImmersion f] (x : X) :
    Module.length (Y.presheaf.stalk (f x)) (Y.presheaf.stalk (f x)) =
      Module.length (X.presheaf.stalk x) (X.presheaf.stalk x) :=
  ringLength_eq_of_ringEquiv (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv

/-- A component generic point in an open subscheme remains generic there. -/
theorem mem_genericPoints_of_isOpenImmersion (f : X ⟶ Y) [IsOpenImmersion f]
    (x : X) (hx : f x ∈ genericPoints Y) : x ∈ genericPoints X := by
  change closure {x} ∈ irreducibleComponents X
  rw [f.isOpenEmbedding.closure_eq_preimage_closure_image, Set.image_singleton]
  exact preimage_mem_irreducibleComponents hx f.isOpenEmbedding
    ⟨f x, subset_closure rfl, x, rfl⟩

/-- An isomorphism preserves the property of being a component generic point. -/
theorem mem_genericPoints_iff_of_isIso (f : X ⟶ Y) [IsIso f] (x : X) :
    f x ∈ genericPoints Y ↔ x ∈ genericPoints X := by
  refine ⟨mem_genericPoints_of_isOpenImmersion f x, fun hx => ?_⟩
  apply mem_genericPoints_of_isOpenImmersion (inv f) (f x)
  have h : inv f (f x) = x := by
    change (f ≫ inv f) x = x
    rw [IsIso.hom_inv_id]
    rfl
  rwa [h]

/-- The induced map between actual component generic points. -/
noncomputable def mapGenericPoint (f : X ⟶ Y) [IsIso f]
    (x : genericPoints X) : genericPoints Y :=
  ⟨f x.val, (mem_genericPoints_iff_of_isIso f x.val).mpr x.property⟩

/-- Actual generic local multiplicities are preserved by isomorphisms. -/
theorem genericMultiplicity_mapGenericPoint (f : X ⟶ Y) [IsIso f]
    (x : genericPoints X) : genericMultiplicity (mapGenericPoint f x) = genericMultiplicity x := by
  unfold genericMultiplicity mapGenericPoint
  rw [stalk_length_eq_of_isOpenImmersion]

/-- Degree-one residue pushforward along a stalk-surjective map is ordinary reindexing. -/
theorem residuePushforward_eq_mapDomain_of_surjectiveOnStalks
    (f : X ⟶ Y) [SurjectiveOnStalks f] :
    FiniteSupportCycle.residuePushforward f = Finsupp.mapDomain.addMonoidHom f := by
  apply Finsupp.addHom_ext
  intro x n
  simp [residueDegree_of_surjectiveOnStalks]

variable [IsNoetherian X] [IsNoetherian Y]

/-- Fundamental point cycles are preserved by the actual residue-weighted pushforward. -/
theorem residuePushforward_fundamentalPointCycle (f : X ⟶ Y) [IsIso f] :
    FiniteSupportCycle.residuePushforward f (fundamentalPointCycle X) =
      fundamentalPointCycle Y := by
  rw [residuePushforward_eq_mapDomain_of_surjectiveOnStalks]
  ext y
  obtain ⟨x, rfl⟩ := f.homeomorph.surjective y
  change Finsupp.mapDomain f (fundamentalPointCycle X) (f x) = fundamentalPointCycle Y (f x)
  rw [Finsupp.mapDomain_apply_of_injective (show Function.Injective f from
      f.homeomorph.injective),
    fundamentalPointCycle_apply, fundamentalPointCycle_apply]
  by_cases hx : x ∈ genericPoints X
  · have hy := (mem_genericPoints_iff_of_isIso f x).mpr hx
    simp only [dite_eq_left hx, dite_eq_left hy]
    exact congrArg (fun n : ℕ => (n : ℤ))
      (genericMultiplicity_mapGenericPoint f ⟨x, hx⟩).symm
  · have hy : f x ∉ genericPoints Y := fun hy => hx
      ((mem_genericPoints_iff_of_isIso f x).mp hy)
    simp [hx, hy]

/-- Finite pushforward by an isomorphism preserves the actual integral fundamental cycle. -/
theorem finitePushforward_fundamentalCycle (f : X ⟶ Y) [IsIso f] :
    IntegralCycle.finitePushforward f (fundamentalCycle X) = fundamentalCycle Y := by
  apply IntegralCycle.toPoints_injective
  rw [← AddMonoidHom.comp_apply, IntegralCycle.toPoints_finitePushforward,
    AddMonoidHom.comp_apply, toPoints_fundamentalCycle, toPoints_fundamentalCycle]
  exact residuePushforward_fundamentalPointCycle f

end AlgebraicGeometry.Scheme
