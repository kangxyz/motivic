/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Cohomology.OrdinaryEpiAffineNisnevichLift
public import Motivic.Aglib.AlgebraicGeometry.MonicAffineNisnevichNeighborhood
public import Motivic.Cohomology.A1.RelativeLaurentGenericOpenZero

/-! # Ordinary sections lift near the entire relative monic divisor -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Polynomial
open AlgebraicGeometry.PolynomialOpenQuotient
open AlgebraicGeometry.Scheme.GenericSection
universe u
namespace Motivic.SheafCohomology
open RelativePolynomialOpenSpans
variable {k R : Type u} [Field k] [CommRing R] [IsDomain R]
  [Algebra k R] [Algebra.Smooth k R]
attribute [local instance] away_smooth

/-- The original epi and its section are pulled back along actual maps in Sm/k.
The entire mapped monic divisor, including its nilpotents, is unchanged. -/
theorem exists_relative_monic_neighborhood_lift
    {I Q : Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}}
    (φ : I ⟶ Q) [Epi φ] (f : R[X]) (hf : f.Monic)
    (s : Q.obj.obj (op (lineSite (k := k) (R := R)))) :
    ∃ r : R, r ≠ 0 ∧ ∃ (Y : SmoothSite (Spec (.of k)))
      (p : Y ⟶ lineSite (k := k) (R := Localization.Away r)),
      IsAffine Y.left ∧ Etale p.left ∧
      IsIso (pullback.snd p.left (inclusion (f.map (algebraMap R (Localization.Away r))))) ∧
      ∃ l : I.obj.obj (op Y), φ.hom.app (op Y) l =
        Q.obj.map (p ≫ lineMap (IsScalarTower.toAlgHom k R (Localization.Away r))).op s := by
  let : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  obtain ⟨Y, q, hY, hq, hcov, l, hl⟩ := exists_affine_nisnevich_lift φ _ s
  let := hY
  let := hq
  obtain ⟨r, hr, W, p, a, hW, hp, ha, hi⟩ :=
    exists_affine_monic_neighborhood R f hf q.left hcov
  let := hW
  let := hp
  let L := lineSite (k := k) (R := Localization.Away r)
  let b := lineMap (IsScalarTower.toAlgHom k R (Localization.Away r))
  let V : SmoothSite (Spec (.of k)) := SmoothSite.mk (p ≫ L.hom)
  let v : V ⟶ L := SmoothSite.homMk p rfl
  let a' : V ⟶ Y := SmoothSite.homMk a (by
    rw [← MorphismProperty.Over.w q, ← Category.assoc, ha, Category.assoc]
    exact congrArg (fun z => p ≫ z) (MorphismProperty.Over.w b))
  have hab : a' ≫ q = v ≫ b := by
    ext
    exact ha
  refine ⟨r, hr, V, v, hW, hp, hi, I.obj.map a'.op l, ?_⟩
  rw [φ.hom.naturality_apply, hl, ← Functor.map_comp_apply, ← op_comp, hab]

end Motivic.SheafCohomology
