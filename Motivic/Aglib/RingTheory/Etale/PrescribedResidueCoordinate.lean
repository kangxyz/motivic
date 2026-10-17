/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.Kaehler.PrescribedResidueFunctionBasis
public import Motivic.Aglib.RingTheory.Etale.ResidueCoordinateCriterion

/-! # An etale chart retaining a prescribed nonzero residue differential -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Module TensorProduct KaehlerDifferential
universe u v
namespace Algebra

/-- The unchanged prescribed function is a literal coordinate of the resulting
polynomial map, which is etale on an actual principal neighborhood. -/
theorem exists_etale_polynomial_map_containing_of_residue_differential_ne_zero
    (k : Type u) (R : Type v) [Field k] [CommRing R] [Algebra k R] [Smooth k R]
    (p : Ideal R) [p.IsPrime] (f : R)
    (hf : (1 ⊗ₜ[R] D k R f :
      IsLocalRing.ResidueField (Localization.AtPrime p) ⊗[R] Ω[R⁄k]) ≠ 0) :
    ∃ (d : ℕ) (g : Fin d → R) (i : Fin d), g i = f ∧
      ∃ r ∉ p, ((algebraMap R (Localization.Away r)).comp
        (MvPolynomial.aeval (R := k) g).toRingHom).Etale := by
  classical
  let K := IsLocalRing.ResidueField (Localization.AtPrime p)
  obtain ⟨s, hs, hfs, b, hb⟩ :=
    exists_residue_basis_original_functions_containing k R K f hf
  let := hs.fintype
  let d := Fintype.card s
  let e : s ≃ Fin d := Fintype.equivFin s
  let g : Fin d → R := fun j => (e.symm j).val
  let bK := b.reindex e
  have hbK (j : Fin d) : bK j = 1 ⊗ₜ[R] D k R (g j) := by
    simpa only [bK, Basis.reindex_apply, g] using hb (e.symm j)
  refine ⟨d, g, e ⟨f, hfs⟩, ?_, ?_⟩
  · exact congrArg Subtype.val (e.symm_apply_apply ⟨f, hfs⟩)
  · exact exists_etale_polynomial_map_of_residue_differential_basis k R p g bK hbK

end Algebra
