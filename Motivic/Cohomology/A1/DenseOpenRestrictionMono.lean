/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.DenseOpenLocalDetection
public import Motivic.AlgebraicGeometry.SmoothSiteSectionDetection
public import Motivic.Cohomology.A1.BoundaryCokernelSheaf
public import Motivic.Aglib.AlgebraicGeometry.CartierComplementDense
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-! # Original coefficient restriction to dense open complements

Generic detection supplies local zero on actual smooth affine neighborhoods.
Separatedness of the original Nisnevich sheaf then proves injectivity of the
literal coefficient restriction. This is not positive-cohomology injectivity.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace Motivic.SheafWithTransfers
variable {k : Type u} [Field k] [Infinite k]

/-- An original section of an HI Nisnevich transfer sheaf is detected on every
actual dense open of an arbitrary smooth object, including disconnected objects. -/
theorem section_eq_zero_of_dense_open {X A : SmoothSite (Spec (.of k))}
    (a : A ⟶ X) [IsOpenImmersion a.left] (ha : DenseRange a.left)
    (F : SheafWithTransfers.{u + 1} k) (hF : F.obj.IsA1Invariant)
    (s : F.obj.sections (Cor.mk X))
    (hs : F.obj.transfer ((Cor.graphFunctor k).map a) s = 0) : s = 0 := by
  classical
  have hlocal := F.obj.exists_zero_neighborhood_of_dense_open a ha hF s hs
  choose O hO hx hz using hlocal
  exact SmoothSite.section_eq_zero_of_residue_splitting_family
    ((SheafWithTransfers.toSheaf k).obj F)
    (fun x => SmoothSite.mk ((O x).ι ≫ X.hom))
    (fun x => SmoothSite.homMk (O x).ι rfl)
    (fun x => inferInstanceAs (Etale (O x).ι))
    (fun x => ⟨x, ⟨x, hx x⟩, rfl,
      inferInstanceAs (IsIso ((O x).ι.residueFieldMap ⟨x, hx x⟩))⟩) s hz

end Motivic.SheafWithTransfers
namespace Motivic.FiniteEtaleSite
variable {k : Type u} [Field k] [Infinite k]
  {U Y : SmoothSite (Spec (.of k))} (j : U ⟶ Y) [IsOpenImmersion j.left]
  (F : SheafWithTransfers.{u + 1} k) (hF : F.obj.IsA1Invariant)

include hF

/-- The coefficient map is the original restriction on each actual base-changed
étale neighborhood. Density is preserved by that neighborhood's open structure map. -/
theorem restrictionToDirectImage_mono_of_dense (hj : DenseRange j.left) :
    Mono (restrictionToDirectImage ((SheafWithTransfers.toSheaf k).obj F) j) := by
  apply (sheafToPresheaf _ _).mono_of_mono_map
  apply (NatTrans.mono_iff_mono_app _).mpr
  intro V
  apply (AddCommGrpCat.mono_iff_injective _).mpr
  apply (injective_iff_map_eq_zero _).mpr
  intro s hs
  let a := (restrictionProjection j).app V.unop
  let : IsOpenImmersion a.left :=
    inferInstanceAs (IsOpenImmersion (pullback.fst V.unop.hom j.left))
  have ha : DenseRange a.left := by
    change Dense (Set.range (pullback.fst V.unop.hom j.left))
    rw [IsOpenImmersion.range_pullbackFst]
    exact hj.preimage V.unop.hom.isOpenMap
  exact F.section_eq_zero_of_dense_open a ha hF s hs

/-- The actual locally rank-one ideal supplies density of its literal complement,
so the original coefficient restriction is monic without an extra purity premise. -/
theorem restrictionToDirectImage_mono_of_cartier {Z : Scheme.{u}} (i : Z ⟶ Y.left)
    [IsClosedImmersion i] (hI : IsLocallyRankOne Y.left (Scheme.Hom.idealModule i))
    (hcomp : Set.range i = (Set.range j.left)ᶜ) :
    Mono (restrictionToDirectImage ((SheafWithTransfers.toSheaf k).obj F) j) := by
  apply restrictionToDirectImage_mono_of_dense j F hF
  have hd := i.dense_compl_range_of_isLocallyRankOne hI
  rw [hcomp, compl_compl] at hd
  exact hd

end Motivic.FiniteEtaleSite
