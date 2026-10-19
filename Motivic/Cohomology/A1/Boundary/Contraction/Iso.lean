/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.Boundary.Presheaf.Contraction.Epi
public import Motivic.Cohomology.A1.Boundary.Contraction.SheafComparison
public import Motivic.Cohomology.A1.Boundary.Contraction.Mono

/-! # The original canonical boundary isomorphism for HI transfer sheaves -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Motivic.FiniteEtaleSite
open _root_.AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] [Infinite k]
  (X : SmoothSite (Spec (.of k))) (F : SheafWithTransfers.{u + 1} k)
  (hF : F.obj.IsA1Invariant)

/-- The constructed original-presheaf epimorphism transfers through the explicit
source and target comparisons to the same canonical sheaf morphism. -/
theorem contractionToBoundary_epi : Epi (contractionToBoundary X F hF) := by
  let := OriginalPresheaf.contractionToBoundary_epi X F.obj hF
  let : Epi ((OriginalPresheaf.contractionSheafIso X F hF).hom ≫
      contractionToBoundary X F hF) := by
    rw [← OriginalPresheaf.contractionToBoundary_sheafIso]
    infer_instance
  exact epi_of_epi (OriginalPresheaf.contractionSheafIso X F hF).hom _

/-- The independently constructed original Mono and Epi give the genuine
canonical boundary isomorphism, without a supplied lifting family. -/
theorem contractionToBoundary_isIso : IsIso (contractionToBoundary X F hF) := by
  let := contractionToBoundary_epi X F hF
  let := contractionToBoundary_mono X F hF
  exact isIso_of_mono_of_epi _

end Motivic.FiniteEtaleSite
