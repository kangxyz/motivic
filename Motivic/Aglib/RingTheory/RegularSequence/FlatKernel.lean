/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.RingHom.Flat

/-!
# Flat transport of regular equations inside an actual kernel

A flat ring map preserves weak regularity of the literal image list. If that
image list lies in the kernel of a map to a nonzero ring, its generated ideal
is proper, so the image list is regular. A commuting square supplies this
kernel containment without any regularity assumption on coefficient modules.
-/

@[expose] public section

open scoped TensorProduct
open RingTheory.Sequence

namespace RingTheory.Sequence

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]

/-- A flat ring homomorphism preserves weak regularity of the literal image list. -/
theorem isWeaklyRegular_map_of_flat (f : R →+* S) (hf : f.Flat)
    {rs : List R} (hrs : IsWeaklyRegular R rs) :
    IsWeaklyRegular S (rs.map f) := by
  let := f.toAlgebra
  have : Module.Flat R S := hf
  have ht : IsWeaklyRegular (R ⊗[R] S) rs := hrs.isWeaklyRegular_rTensor
  have hs : IsWeaklyRegular S rs := ((TensorProduct.lid R S).isWeaklyRegular_congr rs).mp ht
  exact (isWeaklyRegular_map_algebraMap_iff S S rs).mpr hs

/-- A flat image sequence is regular when its generated ideal lies in a proper kernel. -/
theorem isRegular_map_of_flat_of_le_ker [Nontrivial T]
    (f : R →+* S) (g : S →+* T) (hf : f.Flat)
    {rs : List R} (hrs : IsWeaklyRegular R rs)
    (hker : Ideal.ofList (rs.map f) ≤ RingHom.ker g) :
    IsRegular S (rs.map f) := by
  refine ⟨isWeaklyRegular_map_of_flat f hf hrs, ?_⟩
  rw [Ideal.smul_eq_mul, Ideal.mul_top]
  exact Ne.symm <| ne_top_of_le_ne_top (RingHom.ker_ne_top g) hker

/-- A commuting ring square puts the mapped source equations in the actual target kernel. -/
theorem map_ofList_le_ker_of_commSq {U : Type*} [CommRing U]
    (i : R →+* S) (q : R →+* T) (a : S →+* U) (b : T →+* U)
    (h : b.comp q = a.comp i) {rs : List R} (hker : Ideal.ofList rs ≤ RingHom.ker i) :
    Ideal.ofList (rs.map q) ≤ RingHom.ker b := by
  rw [← Ideal.map_ofList, Ideal.map_le_iff_le_comap, RingHom.comap_ker, h]
  intro x hx
  change a (i x) = 0
  rw [show i x = 0 from hker hx, map_zero]

/-- Flat transport and an actual commuting square give a proper regular image list. -/
theorem isRegular_map_of_flat_of_commSq {U : Type*} [CommRing U] [Nontrivial U]
    (i : R →+* S) (q : R →+* T) (a : S →+* U) (b : T →+* U)
    (h : b.comp q = a.comp i) (hq : q.Flat)
    {rs : List R} (hrs : IsWeaklyRegular R rs) (hker : Ideal.ofList rs ≤ RingHom.ker i) :
    IsRegular T (rs.map q) :=
  isRegular_map_of_flat_of_le_ker q b hq hrs (map_ofList_le_ker_of_commSq i q a b h hker)

end RingTheory.Sequence
