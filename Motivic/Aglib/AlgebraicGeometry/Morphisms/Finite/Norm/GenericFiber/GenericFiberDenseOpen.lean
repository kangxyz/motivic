/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.FunctionField.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.Topology.NoetherianSpace

/-!
# Dense opens contain the whole generic fiber

A globally dense open in a Noetherian source contains every point above the
generic point of an integral target under a locally quasi-finite morphism.
No integrality, reducedness, dominance or module freeness of the source is used.


Intended upstream module:
`Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.GenericFiber.GenericFiberDenseOpen`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.GenericFiber.GenericFiberSectionNorm`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme

universe u
variable {C T : Scheme.{u}} [NoetherianSpace C] [IsIntegral T]

/-- A dense open of the whole source contains the whole generic fiber. -/
theorem generic_preimage_subset_dense_open (f : C ⟶ T) [LocallyQuasiFinite f]
    (W : C.Opens) (hW : Dense (W : Set C)) :
    f ⁻¹' {genericPoint T} ⊆ (W : Set C) := by
  intro x hx
  have hx' : f x = genericPoint T := hx
  let Z := irreducibleComponent x
  have hZ := irreducibleComponent_mem_irreducibleComponents x
  let hz := isIrreducible_irreducibleComponent (x := x)
  let z := hz.genericPoint
  have hg : IsGenericPoint z Z := hz.isGenericPoint_genericPoint isClosed_irreducibleComponent
  have hzx : z ⤳ x := hg.specializes mem_irreducibleComponent
  have hfz : f z = genericPoint T := by
    have h := hzx.map f.continuous
    rw [hx'] at h
    exact (h.antisymm (genericPoint_specializes (f z))).eq
  have he : z = x := (f.isDiscrete_preimage_singleton (genericPoint T)).eq_of_specializes
    hzx hfz hx'
  obtain ⟨V, hVo, hVn, hVZ⟩ :=
    NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent Z hZ
  obtain ⟨y, hyV, hyW⟩ := hW.inter_open_nonempty V hVo hVn
  have hzW : z ∈ W := (hg.specializes (hVZ hyV)).mem_open W.isOpen hyW
  exact he ▸ hzW

/-- The literal generic pullback projection factors through every globally dense
open in the Noetherian source of a finite morphism. -/
theorem generic_pullback_range_subset_dense_open (f : C ⟶ T) [IsFinite f]
    (W : C.Opens) (hW : Dense (W : Set C)) :
    Set.range (pullback.fst f (T.fromSpecStalk (genericPoint T))) ⊆ Set.range W.ι := by
  rw [Opens.range_ι, Scheme.Pullback.range_fst]
  intro x hx
  obtain ⟨y, hy⟩ := hx
  apply generic_preimage_subset_dense_open f W hW
  change f x = genericPoint T
  rw [← hy]
  exact fromSpecStalk_genericPoint_apply T y

end AlgebraicGeometry.Scheme
