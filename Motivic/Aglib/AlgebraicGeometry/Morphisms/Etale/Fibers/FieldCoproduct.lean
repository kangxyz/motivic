/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Properties.Discrete.DiscreteReducedCoproduct

/-! # Canonical finite disjoint decomposition of étale schemes over fields

The original scheme and its structural morphism are retained. Quasi-compactness
is required only for finiteness of the component index type.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

variable {K : Type u} [Field K] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of K)) [Etale f]

/-- An étale scheme over a field is locally quasi-finite. -/
theorem locallyQuasiFinite_of_etale_over_field : LocallyQuasiFinite f := by
  constructor
  intro U hU V hV e
  have h := f.etale_appLE hU hV e
  algebraize [(f.appLE U V e).hom]
  exact RingHom.quasiFinite_algebraMap.mpr inferInstance

include f in
/-- The original underlying topological space is discrete. -/
theorem discreteTopology_of_etale_over_field : DiscreteTopology X := by
  have := locallyQuasiFinite_of_etale_over_field f
  have := IsLocallyArtinian.of_locallyQuasiFinite f
  infer_instance

include f in
/-- The original structure sheaf is reduced. -/
theorem isReduced_of_etale_over_field : IsReduced X :=
  isReduced_of_smooth_over_field f

/-- A quasi-compact étale scheme over a field has finitely many actual points. -/
theorem finite_of_etale_over_field [QuasiCompact f] : Finite X := by
  have := discreteTopology_of_etale_over_field f
  have := QuasiCompact.compactSpace_of_compactSpace f
  exact finite_of_compact_of_discrete

/-- The canonical disjoint decomposition uses the literal residue-field morphisms. -/
def etaleFieldCoproductIso : (∐ fun x : X ↦ Spec (X.residueField x)) ≅ X := by
  have := discreteTopology_of_etale_over_field f
  have := isReduced_of_etale_over_field f
  exact X.residueFieldCoproductIso

@[reassoc (attr := simp)]
theorem etaleFieldCoproductIso_ι_hom (x : X) :
    Sigma.ι (fun x : X ↦ Spec (X.residueField x)) x ≫
      (etaleFieldCoproductIso f).hom = X.fromSpecResidueField x := by
  have := discreteTopology_of_etale_over_field f
  have := isReduced_of_etale_over_field f
  exact X.residueFieldCoproductIso_ι_hom x

/-- Each canonical component retains the original structural morphism to the field. -/
@[reassoc]
theorem etaleFieldCoproductIso_ι_hom_comp (x : X) :
    Sigma.ι (fun x : X ↦ Spec (X.residueField x)) x ≫
      (etaleFieldCoproductIso f).hom ≫ f = X.fromSpecResidueField x ≫ f := by
  rw [etaleFieldCoproductIso_ι_hom_assoc]

end AlgebraicGeometry.Scheme
