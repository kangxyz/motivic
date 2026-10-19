/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Boundary.SectionPairNormIdeal
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.FiniteSchemeNormBaseChange
/-! # The original chart association over its native affine coordinate ring

Intended upstream module:
`Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Norm.SectionPairNormSpec`.

The exact hypotheses are the section variables and declaration signatures below.
Current direct import consumers (unique module suffixes):
`Norm.SectionPairNormNeighborhood`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

variable {S C P X Y V : Scheme.{u}}
  {R : Type u} [CommRing R] [IsDomain R] (π : P ⟶ S) [IsSeparated π]
  (f : C ⟶ P) [IsFinite f] (jB : Y ⟶ C) [IsOpenImmersion jB]
  [SmoothOfRelativeDimension 1 (jB ≫ f ≫ π)]
  (jA : X ⟶ P) [IsOpenImmersion jA] [SmoothOfRelativeDimension 1 (jA ≫ π)]
  (p : Y ⟶ X) [Flat p] (hret : jB ≫ f = p ≫ jA)
  (LA : LineBundle (pullback (jA ≫ π) π))
  (aA : SheafOfModules.unit (pullback (jA ≫ π) π).ringCatSheaf ⟶
    (tensorLineBundle _ LA (dualLineBundle _ (Hom.relativeCompactificationGraphLine π jA))).val)
  (bA : SheafOfModules.unit (pullback (jA ≫ π) π).ringCatSheaf ⟶ LA.val)
  (vA : V ⟶ pullback (jA ≫ π) π)
  [IsIso (Hom.pullbackToUnit (sectionDualFunctional _ LA bA) vA)]
  [IsIso (Hom.pullbackToUnit (sectionDualFunctional _
    (tensorLineBundle _ LA (dualLineBundle _
      (Hom.relativeCompactificationGraphLine π jA))) aA) vA)]
  (w : Spec (.of R) ⟶ pullback (jB ≫ f ≫ π) π)
  (l : Spec (.of R) ⟶ pullback (Hom.retainedParameterProductMap π f jB jA p hret) vA)
  (hl : l ≫ pullback.fst (Hom.retainedParameterProductMap π f jB jA p hret) vA = w)

variable [IsOpenImmersion w]
  (LB : LineBundle (pullback (jB ≫ f ≫ π) (f ≫ π)))
  (aB : SheafOfModules.unit (pullback (jB ≫ f ≫ π) (f ≫ π)).ringCatSheaf ⟶
    (tensorLineBundle _ LB (dualLineBundle _
      (Hom.relativeCompactificationGraphLine (f ≫ π) jB))).val)
  (bB : SheafOfModules.unit (pullback (jB ≫ f ≫ π) (f ≫ π)).ringCatSheaf ⟶ LB.val)
  [IsIso (Hom.pullbackToUnit (sectionDualFunctional _ LB bB)
    (pullback.fst (Hom.graphProductMap π f jB) w))]
  [IsIso (Hom.pullbackToUnit (sectionDualFunctional _
    (tensorLineBundle _ LB (dualLineBundle _
      (Hom.relativeCompactificationGraphLine (f ≫ π) jB))) aB)
    (pullback.fst (Hom.graphProductMap π f jB) w))]

include hl in
/-- The actual graph quotient constructs the association unit in R itself.
The scalar action is the original chart map composed with ΓSpecIso.inv. -/
theorem sectionPairGraph_norm_association_spec :
    let vB := pullback.fst (Hom.graphProductMap π f jB) w
    let cB : Γ(pullback (Hom.graphProductMap π f jB) w, ⊤) := Modules.Hom.app
      (sectionPairGraphCoefficient (f ≫ π) jB LB aB bB vB) ⊤
      (1 : Γ(pullback (Hom.graphProductMap π f jB) w, ⊤))
    let cA : R := (Scheme.ΓSpecIso (.of R)).hom
      ((l ≫ pullback.snd (Hom.retainedParameterProductMap π f jB jA p hret) vA).appTop
        (Modules.Hom.app (sectionPairGraphCoefficient π jA LA aA bA vA) ⊤ (1 : Γ(V, ⊤))))
    let : Algebra R Γ(pullback (Hom.graphProductMap π f jB) w, ⊤) :=
      (FiniteSchemeNormBaseChange.scalarMap (pullback.snd (Hom.graphProductMap π f jB) w)).toAlgebra
    ∀ [Module.Free R Γ(pullback (Hom.graphProductMap π f jB) w, ⊤)],
      ∃ μ : Rˣ, Algebra.norm R cB = (μ : R) * cA := by
  dsimp only
  intro hfree
  let B := Γ(pullback (Hom.graphProductMap π f jB) w, ⊤)
  let n := pullback.snd (Hom.graphProductMap π f jB) w
  let E := (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv
  let : Algebra R B := (FiniteSchemeNormBaseChange.scalarMap n).toAlgebra
  let : Module.Free R B := hfree
  let : Algebra Γ(Spec (.of R), ⊤) B := n.appTop.hom.toAlgebra
  have he : (algebraMap R B).comp E.toRingHom = algebraMap Γ(Spec (.of R), ⊤) B := by
    ext r
    change n.appTop ((Scheme.ΓSpecIso (.of R)).inv
      ((Scheme.ΓSpecIso (.of R)).hom r)) = n.appTop r
    rw [Iso.hom_inv_id_apply]
  let : Module.Free Γ(Spec (.of R), ⊤) B := Module.Free.of_basis
    ((Module.Free.chooseBasis R B).mapCoeffs E.symm (by
      intro r x
      change n.appTop (E.symm r) * x =
        n.appTop ((Scheme.ΓSpecIso (.of R)).inv r) * x
      rfl))
  let : IsDomain Γ(Spec (.of R), ⊤) := E.toMulEquiv.isDomain _
  obtain ⟨μ, hμ⟩ := sectionPairGraph_norm_association
    π f jB jA p hret LA aA bA vA w l hl LB aB bB
  refine ⟨Units.map E.toMonoidHom μ, ?_⟩
  have hm := congrArg E hμ
  rw [Algebra.norm_eq_of_ringEquiv E he, map_mul] at hm
  exact hm

end AlgebraicGeometry.Scheme.RelativeCurvePencil
