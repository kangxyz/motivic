/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Moving.Pencils.BoundaryFunctional.FlatBaseChange
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Frames.Prescribed.Neighborhood.General


/-! # Compactified boundary functionals retain their original parameter pullback

The coefficient-line comparison is precisely the native composition comparison
across the given commuting square. No dual frame or replacement section is chosen.
-/

open _root_.AlgebraicGeometry.Scheme (SmoothSite)

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
open Scheme.Modules.Invertible.PolynomialBoundaryPencil

universe u
namespace Motivic.Cor

/-- The actual parameter pullback of a compactified functional agrees with left
graph composition of its original correspondence. The same functional is pulled
back literally, with no desired cycle equality or new section choice as input. -/
theorem graph_boundaryFunctional_of_cartesian
    {k : Type u} [Field k] (X T Y : SmoothSite (Spec (.of k)))
    [IsAffine X.left] [IsAffine T.left]
    {C B U C' B' U' : Scheme.{u}}
    (i : B ⟶ C) (q : C ⟶ T.left) [IsProper q]
    (j : U ⟶ C) [IsOpenImmersion j] [U.IsQuasiAffine]
    [SmoothOfRelativeDimension 1 (j ≫ q)]
    (i' : B' ⟶ C') (q' : C' ⟶ X.left) [IsProper q']
    (j' : U' ⟶ C') [IsOpenImmersion j'] [U'.IsQuasiAffine]
    [SmoothOfRelativeDimension 1 (j' ≫ q')]
    (c : C' ⟶ C) (v : U' ⟶ U) (hv : v ≫ j = j' ≫ c)
    (L : LineBundle C) (a : L.val ⟶ SheafOfModules.unit C.ringCatSheaf)
    [IsIso ((Scheme.Modules.pullback i).map a)]
    [IsIso ((Scheme.Modules.pullback i').map (Hom.pullbackToUnit a c))]
    (hc : ∀ x : C, x ∈ Set.range j ∨ x ∈ Set.range i)
    (hc' : ∀ x : C', x ∈ Set.range j' ∨ x ∈ Set.range i')
    (g : U ⟶ Y.left) (hb : (j ≫ q) ≫ T.hom = g ≫ Y.hom)
    (α : X ⟶ T) [Flat α.left]
    (H : IsPullback v (j' ≫ q') (j ≫ q) α.left) :
    (graphFunctor k).map α ≫ boundaryFunctional T Y i q j L a hc g hb =
      boundaryFunctional X Y i' q' j' (pullbackLineBundle c L)
        (Hom.pullbackToUnit a c) hc' (v ≫ g)
        (by
          calc
            (j' ≫ q') ≫ X.hom = ((j' ≫ q') ≫ α.left) ≫ T.hom := by
              simp only [Category.assoc, MorphismProperty.Over.w]
            _ = (v ≫ (j ≫ q)) ≫ T.hom := by rw [← H.w]
            _ = (v ≫ g) ≫ Y.hom := by rw [Category.assoc, hb, Category.assoc]) := by
  let aU := Hom.pullbackToUnit a j
  let a₁ := Hom.pullbackToUnit aU v
  let a₂ := Hom.pullbackToUnit (Hom.pullbackToUnit a c) j'
  let E := ((Scheme.Modules.pullbackComp v j).app L.val) ≪≫
    ((Scheme.Modules.pullbackCongr hv).app L.val) ≪≫
    ((Scheme.Modules.pullbackComp j' c).app L.val).symm
  have he : a₁ = E.hom ≫ a₂ := by
    change pullbackUnitMap v (pullbackUnitMap j a) =
      E.hom ≫ pullbackUnitMap j' (pullbackUnitMap c a)
    rw [← pullbackUnitMap_comp v j a, ← pullbackUnitMap_comp j' c a]
    dsimp only [E, Iso.trans_hom, Iso.symm_hom]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [pullbackUnitMap_congr hv a]
  let e : Hom.zeroScheme a₁ ≅ Hom.zeroScheme a₂ :=
    eqToIso (congrArg Hom.zeroScheme he) ≪≫ zeroSchemePrecompIso E a₂
  have hez : e.hom ≫ Hom.zeroInclusion a₂ = Hom.zeroInclusion a₁ := by
    simp only [e, Iso.trans_hom, Category.assoc, zeroSchemePrecompIso_hom_inclusion,
      eqToIso.hom]
    exact zeroScheme_congr_inclusion he
  let : IsFinite (Hom.zeroInclusion aU ≫ (j ≫ q)) :=
    (boundaryFunctional_finite_flat T i q j L a hc).1
  let : Flat (Hom.zeroInclusion aU ≫ (j ≫ q)) :=
    (boundaryFunctional_finite_flat T i q j L a hc).2
  let : IsFinite (Hom.zeroInclusion a₁ ≫ (j' ≫ q')) :=
    (ZeroSectionFlatBaseChange.pulled_finite_flat (j ≫ q) α v (j' ≫ q') H
      (pullbackLineBundle j L) aU).1
  let : Flat (Hom.zeroInclusion a₁ ≫ (j' ≫ q')) :=
    (ZeroSectionFlatBaseChange.pulled_finite_flat (j ≫ q) α v (j' ≫ q') H
      (pullbackLineBundle j L) aU).2
  let : IsFinite (Hom.zeroInclusion a₂ ≫ (j' ≫ q')) :=
    (boundaryFunctional_finite_flat X i' q' j' (pullbackLineBundle c L)
      (Hom.pullbackToUnit a c) hc').1
  let : Flat (Hom.zeroInclusion a₂ ≫ (j' ≫ q')) :=
    (boundaryFunctional_finite_flat X i' q' j' (pullbackLineBundle c L)
      (Hom.pullbackToUnit a c) hc').2
  refine (graph_boundaryFunctional_of_flat X T Y i q j L a hc g hb α v
    (j' ≫ q') H).trans ?_
  unfold boundaryFunctional
  exact PolynomialPencilCycles.span_eq_of_iso e _ _ _ _ _ _
    (by simpa only [Category.assoc] using congrArg (· ≫ (j' ≫ q')) hez)
    (by simpa only [Category.assoc] using congrArg (· ≫ (v ≫ g)) hez)

end Motivic.Cor
