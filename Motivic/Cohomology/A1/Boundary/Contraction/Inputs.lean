/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.LocalVanishing.Coefficient
public import Motivic.Cohomology.A1.Boundary.Contraction.SheafComparison
public import Motivic.Cohomology.A1.Boundary.Contraction.Mono

/-! # Exact canonical boundary consumers with explicit coefficient inputs

The original-presheaf boundary Epi family remains a mathematical input.
The consumers preserve the original coefficient and canonical boundary map.
These conditional statements are valid over any field; they are not finite-field
producers and do not assume a puncture-monomorphism family.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u

namespace Motivic.FiniteEtaleSite.OriginalPresheaf
open _root_.AlgebraicGeometry.Scheme

/-- Epi of the original canonical maps, for every unchanged HI coefficient.
This explicit family is an input, not an assertion of its finite-field producer. -/
def CanonicalBoundaryEpi (k : Type u) [Field k] : Prop :=
  ∀ (X : SmoothSite (Spec (.of k))) (P : PresheafWithTransfers.{u + 1} k),
    P.IsA1Invariant → Epi (contractionToBoundary X P)

end Motivic.FiniteEtaleSite.OriginalPresheaf

namespace Motivic.FiniteEtaleSite
open _root_.AlgebraicGeometry.Scheme
variable {k : Type u} [Field k]

/-- The original PST Epi transports to the same sheaf boundary morphism. -/
theorem contractionToBoundary_epi_of_canonicalBoundaryEpi
    (hE : OriginalPresheaf.CanonicalBoundaryEpi k)
    (X : SmoothSite (Spec (.of k))) (F : SheafWithTransfers.{u + 1} k)
    (hF : F.obj.IsA1Invariant) : Epi (contractionToBoundary X F hF) := by
  let := hE X F.obj hF
  let : Epi ((OriginalPresheaf.contractionSheafIso X F hF).hom ≫
      contractionToBoundary X F hF) := by
    rw [← OriginalPresheaf.contractionToBoundary_sheafIso]
    infer_instance
  exact epi_of_epi (OriginalPresheaf.contractionSheafIso X F hF).hom _

/-- The independently proved original Mono and supplied original Epi give Iso. -/
theorem contractionToBoundary_isIso_of_canonicalBoundaryEpi
    (hE : OriginalPresheaf.CanonicalBoundaryEpi k)
    (X : SmoothSite (Spec (.of k))) (F : SheafWithTransfers.{u + 1} k)
    (hF : F.obj.IsA1Invariant) : IsIso (contractionToBoundary X F hF) := by
  let := contractionToBoundary_epi_of_canonicalBoundaryEpi hE X F hF
  let := contractionToBoundary_mono X F hF
  exact isIso_of_mono_of_epi _

end Motivic.FiniteEtaleSite
