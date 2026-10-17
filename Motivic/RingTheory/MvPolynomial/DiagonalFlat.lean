/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.RingTheory.MvPolynomial.Diagonal

/-!
# Flat transport of polynomial diagonal regularity

The proved coordinate-difference sequence remains weakly regular on a flat
ambient module, and after a flat algebra base change. Flatness is explicit;
these statements do not assume or assert regularity on arbitrary supports.
-/

@[expose] public section

open scoped TensorProduct
open RingTheory.Sequence

namespace Motivic.PolynomialDiagonal

variable (R σ : Type*) [CommRing R]

/-- Flat ambient modules preserve the proved coordinate-difference regularity. -/
theorem isWeaklyRegular_differences_on_flat
    (M : Type*) [AddCommGroup M] [Module (Ambient R σ) M] [Module.Flat (Ambient R σ) M]
    (l : List σ) (hl : l.Nodup) : IsWeaklyRegular M (l.map (difference R σ)) := by
  have h : IsWeaklyRegular (Ambient R σ ⊗[Ambient R σ] M) (l.map (difference R σ)) :=
    (isWeaklyRegular_differences R σ l hl).isWeaklyRegular_rTensor
  exact ((TensorProduct.lid (Ambient R σ) M).isWeaklyRegular_congr _).mp h

/-- The actual images of diagonal differences are weakly regular after flat base change. -/
theorem isWeaklyRegular_differences_baseChange
    (S : Type*) [CommRing S] [Algebra (Ambient R σ) S] [Module.Flat (Ambient R σ) S]
    (l : List σ) (hl : l.Nodup) :
    IsWeaklyRegular S (l.map (fun i => algebraMap (Ambient R σ) S (difference R σ i))) := by
  have h := (isWeaklyRegular_map_algebraMap_iff S S (l.map (difference R σ))).mpr
    (isWeaklyRegular_differences_on_flat R σ S l hl)
  simpa only [List.map_map, Function.comp_def] using h

end Motivic.PolynomialDiagonal
