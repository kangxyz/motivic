/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Sheaf.H1.AffineLineLocalLifts
public import Motivic.Cohomology.Sheaf.H1.NisnevichSquareDescent

/-! # The actual affine-line H¹ discrepancy consumed by geometric homotopies -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe w u

namespace Motivic.SheafCohomology
open _root_.AlgebraicGeometry.Scheme _root_.CategoryTheory.Sheaf.LargeCohomology

open _root_.AlgebraicGeometry.Scheme.AffineLineReducedComplement

variable {k : Type u} [Field k]
  [HasExt.{w} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [EnoughInjectives
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- Constructible local-lift data for one actual class, retaining the original
ordinary injective presentation and the full closed complement. -/
structure AffineLineH1LiftData
    (F : Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})
    (x : H.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology (Spec (.of k)))
      F 1 (SmoothSite.affineLine (.of k))) where
  /-- A section of the original injective cokernel whose boundary is the class `x`. -/
  s : (cokernel (Injective.ι F)).obj.obj (op (SmoothSite.affineLine (.of k)))
  boundary : injectiveSectionBoundary (SmoothSite.nisnevichTopology (Spec (.of k)))
    F (SmoothSite.affineLine (.of k)) s = x
  /-- The affine open containing the generic point of the original affine line. -/
  U : (line k).Opens
  generic_mem : genericPoint (line k) ∈ U
  affine_open : IsAffineOpen U
  /-- A lift of the restriction of `s` to `openObject U` in the original injective sheaf. -/
  lU : (Injective.under F).obj.obj (op (openObject U))
  quotient_lU : (cokernel.π (Injective.ι F)).hom.app (op (openObject U)) lU =
    (cokernel (Injective.ι F)).obj.map (openInclusion U).op s
  /-- The smooth-site object of the chosen étale neighborhood of the complement of `U`. -/
  Y : SmoothSite (Spec (.of k))
  /-- The chosen étale map from `Y` to the original affine line. -/
  p : Y ⟶ SmoothSite.affineLine (.of k)
  etale : Etale p.left
  iso_complement : IsIso (pullback.snd p.left (inclusion U))
  /-- A lift in the original injective sheaf of the restriction of `s` along `p`. -/
  lY : (Injective.under F).obj.obj (op Y)
  quotient_lY : (cokernel.π (Injective.ι F)).hom.app (op Y) lY =
    (cokernel (Injective.ι F)).obj.map p.op s

attribute [instance] AffineLineH1LiftData.etale AffineLineH1LiftData.iso_complement

/-- Choose data whose existence was proved from the actual class alone. -/
def affineLineH1LiftData
    (F : Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})
    (x : H.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology (Spec (.of k)))
      F 1 (SmoothSite.affineLine (.of k))) : AffineLineH1LiftData F x := by
  apply Classical.choice
  obtain ⟨s, hs, U, hU, hAff, lU, hlU, Y, p, hp, hZ, lY, hlY⟩ :=
    exists_affineLine_affine_local_lifts_of_h_one F x
  exact ⟨⟨s, hs, U, hU, hAff, lU, hlU, Y, p, hp, hZ, lY, hlY⟩⟩

namespace AffineLineH1LiftData
open _root_.AlgebraicGeometry.Scheme _root_.CategoryTheory.Sheaf.LargeCohomology

variable {F : Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}}
  {x : H.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology (Spec (.of k)))
    F 1 (SmoothSite.affineLine (.of k))} (D : AffineLineH1LiftData F x)

instance (U : (line k).Opens) : IsOpenImmersion (openInclusion U).left :=
  inferInstanceAs (IsOpenImmersion U.ι)

/-- Affineness of the fixed generic open comes from its actual construction. -/
instance isAffine_openObject : IsAffine (openObject D.U).left := D.affine_open

/-- The genuine smooth-site overlap of the two constructed arrows. -/
abbrev overlap := pullback (openInclusion D.U) D.p

/-- The canonical distinguished square, with unchanged affine-line base. -/
abbrev square : Square (SmoothSite (Spec (.of k))) where
  f₁₂ := pullback.fst (openInclusion D.U) D.p
  f₁₃ := pullback.snd (openInclusion D.U) D.p
  f₂₄ := openInclusion D.U
  f₃₄ := D.p
  fac := pullback.condition

theorem square_isPullback : D.square.IsPullback := IsPullback.of_hasPullback _ _

/-- Exactness on sections constructs the coefficient discrepancy; it is not an
extra hypothesis about the local lifts. -/
theorem existsUnique_discrepancy :
    ∃! d : F.obj.obj (op D.overlap),
      (Injective.ι F).hom.app (op D.overlap) d =
        (Injective.under F).obj.map D.square.f₁₂.op D.lU -
          (Injective.under F).obj.map D.square.f₁₃.op D.lY := by
  exact Sheaf.existsUnique_localLiftDifference _
    (injectivePresentation_shortExact.{u + 1, u, u + 1} _ F)
    (openInclusion D.U) D.p D.square.f₁₂ D.square.f₁₃ D.square.fac
    D.s D.lU D.lY D.quotient_lU D.quotient_lY

/-- The actual uniquely determined discrepancy on the original overlap. -/
def discrepancy : F.obj.obj (op D.overlap) := D.existsUnique_discrepancy.exists.choose

theorem discrepancy_eq :
    (Injective.ι F).hom.app (op D.overlap) D.discrepancy =
      (Injective.under F).obj.map D.square.f₁₂.op D.lU -
        (Injective.under F).obj.map D.square.f₁₃.op D.lY :=
  D.existsUnique_discrepancy.exists.choose_spec

variable {Y' : SmoothSite (Spec (.of k))} (r : Y' ⟶ D.Y)

/-- Refinement only of the étale leg; the open and affine-line base stay fixed. -/
abbrev refinedSquare : Square (SmoothSite (Spec (.of k))) where
  f₁₂ := pullback.fst (openInclusion D.U) (r ≫ D.p)
  f₁₃ := pullback.snd (openInclusion D.U) (r ≫ D.p)
  f₂₄ := openInclusion D.U
  f₃₄ := r ≫ D.p
  fac := pullback.condition

theorem refinedSquare_isPullback : (D.refinedSquare r).IsPullback :=
  IsPullback.of_hasPullback _ _

/-- The literal map from the refined overlap into the original overlap. -/
def overlapMap : (D.refinedSquare r).X₁ ⟶ D.overlap :=
  pullback.lift (D.refinedSquare r).f₁₂ ((D.refinedSquare r).f₁₃ ≫ r)
    (by simpa only [refinedSquare, Category.assoc] using
      (pullback.condition (f := openInclusion D.U) (g := r ≫ D.p)))

@[reassoc (attr := simp)] theorem overlapMap_fst :
    D.overlapMap r ≫ D.square.f₁₂ = (D.refinedSquare r).f₁₂ :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem overlapMap_snd :
    D.overlapMap r ≫ D.square.f₁₃ = (D.refinedSquare r).f₁₃ ≫ r :=
  pullback.lift_snd _ _ _

/-- Restricting the original discrepancy gives exactly the discrepancy of the
restricted original lift, without surjectivity on sections of the new overlap. -/
theorem restricted_discrepancy_eq :
    (Injective.ι F).hom.app (op (D.refinedSquare r).X₁)
        (F.obj.map (D.overlapMap r).op D.discrepancy) =
      (Injective.under F).obj.map (D.refinedSquare r).f₁₂.op D.lU -
        (Injective.under F).obj.map (D.refinedSquare r).f₁₃.op
          ((Injective.under F).obj.map r.op D.lY) := by
  rw [(Injective.ι F).hom.naturality_apply, D.discrepancy_eq, map_sub,
    ← Functor.map_comp_apply, ← op_comp, D.overlapMap_fst,
    ← Functor.map_comp_apply, ← op_comp, D.overlapMap_snd,
    op_comp, Functor.map_comp, ConcreteCategory.comp_apply]

end AffineLineH1LiftData

/-- With the original base and generic open fixed, a correcting homotopy on a
refined étale leg kills the original class. Local lifts and the discrepancy are
constructed from that class, rather than supplied as additional hypotheses. -/
theorem h_one_eq_zero_of_affineLine_correcting_homotopy
    (F : SheafWithTransfers.{u + 1} k)
    (hF : PresheafWithTransfers.IsA1Invariant F.obj)
    (x : H.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology (Spec (.of k)))
      ((SheafWithTransfers.toSheaf k).obj F) 1 (SmoothSite.affineLine (.of k))) :
    let D := affineLineH1LiftData ((SheafWithTransfers.toSheaf k).obj F) x
    ∀ {Y' : SmoothSite (Spec (.of k))} (r : Y' ⟶ D.Y)
      [Etale (r ≫ D.p).left] [IsIso (pullback.snd (r ≫ D.p).left (inclusion D.U))]
      (lam : Cor.mk Y' ⟶ Cor.mk D.overlap)
      (ψ : Cor.mk (openObject D.U) ⟶ Cor.mk D.overlap)
      (α : Cor.mk (SmoothSite.a1Cylinder (.of k) (D.refinedSquare r).X₁) ⟶ Cor.mk D.overlap),
      (Cor.graphFunctor k).map (SmoothSite.a1Section (.of k) (D.refinedSquare r).X₁ 0) ≫ α =
        (Cor.graphFunctor k).map (D.overlapMap r) →
      (Cor.graphFunctor k).map (SmoothSite.a1Section (.of k) (D.refinedSquare r).X₁ 1) ≫ α =
        (Cor.graphFunctor k).map (D.refinedSquare r).f₁₃ ≫ lam -
          (Cor.graphFunctor k).map (D.refinedSquare r).f₁₂ ≫ ψ →
      x = 0 := by
  intro D Y' r hEt hIso lam ψ α h₀ h₁
  apply h_one_eq_zero_of_nisnevich_square_restricted_homotopy F hF
    (D.refinedSquare r) (D.refinedSquare_isPullback r) (inclusion D.U)
    ((range_inclusion D.U).trans (congrArg Set.compl (Scheme.Opens.range_ι D.U).symm))
    x D.s D.boundary D.lU
    ((Injective.under ((SheafWithTransfers.toSheaf k).obj F)).obj.map r.op D.lY)
    D.quotient_lU ?_ (D.overlapMap r) lam ψ α h₀ h₁ D.discrepancy
    (D.restricted_discrepancy_eq r).symm
  rw [(cokernel.π (Injective.ι ((SheafWithTransfers.toSheaf k).obj F))).hom.naturality_apply,
    D.quotient_lY, ← Functor.map_comp_apply, ← op_comp]

end Motivic.SheafCohomology
