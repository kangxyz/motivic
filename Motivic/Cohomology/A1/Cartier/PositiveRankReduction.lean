/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.LocalVanishing.Cylinder.OpenComparison
public import Motivic.Cohomology.A1.LocalVanishing.Puncture.LowerRankPersistent
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Cohomology.GenericOpen
public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.Smooth.SmoothCartierAtPrime
public import Motivic.Aglib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Injectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives

/-! # Actual Cartier neighborhoods in the positive-local-rank reduction

The geometric divisor is chosen only on an affine open neighborhood. Its literal
open complement supplies the puncture; the marked-slice comparison returns the
result to the original cylinder germ. The original cohomological restriction
mono remains an explicit, independent premise of the resulting implication.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace Motivic.FiniteEtaleSite
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
open _root_.CategoryTheory.Sheaf

variable {k : Type u} [Field k] [PerfectField k]
  (X : SmoothSite (Spec (.of k))) (K : Type u) [Field K]
  (b : Spec (.of K) ⟶ X.left) (p : Spec (.of K))
  (F : SheafWithTransfers.{u + 1} k)
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- The ordinary Ext instance used in this module. -/
local instance positiveRankReductionHasExt (Y : Scheme.{u}) :
    HasExt.{u + 1} (Sheaf (nisnevichTopology Y) AddCommGrpCat.{u + 1}) :=
  hasExt_of_enoughInjectives _

/-- The positive-rank geometric choice and the lower-rank induction leave exactly
the original cylinder restriction mono on the actual local Cartier complement.
Neither a global divisor nor a cohomological purity theorem is assumed or proved. -/
theorem exists_positive_rank_cartier_restriction_reduction
    (hF : F.obj.IsA1Invariant) (n d : ℕ)
    (hd : ringKrullDim (X.left.presheaf.stalk (b p)) = d) (hpos : 0 < d)
    (hLow : ∀ q : ℕ, 0 < q → q < n + 1 →
      (SheafCohomology.withTransfers k F q).IsA1Invariant)
    (hIH : LowerRankCylinderGermsZero F (n + 1) d) :
    let P := LargeCohomology.presheaf.{u + 1, u + 1, u, u + 1}
      (SmoothSite.nisnevichTopology (Spec (.of k))) ((SheafWithTransfers.toSheaf k).obj F)
        (n + 1)
    ∃ (O : X.left.Opens) (hO : b p ∈ O), IsAffineOpen O ∧
      ∃ (Z : Scheme.{u}) (i : Z ⟶ O.toScheme),
        IsClosedImmersion i ∧ IsLocallyRankOne O.toScheme (Scheme.Hom.idealModule i) ∧
        Smooth (i ≫ O.ι ≫ X.hom) ∧ b p ∈ Set.range (i ≫ O.ι) ∧
        ∃ W : O.toScheme.Opens, Set.range i = (W : Set O.toScheme)ᶜ ∧
          (Mono (colim.map (pointedCylinderRestriction (.of k)
            (SmoothSite.openInclusion ((toSmoothSite X).obj (openObject O)) W)
            (relativeFieldPoint (openFieldPointLift K b p O hO) K (𝟙 _)) P)) →
            IsZero (colimit (pointedCylinderValues (.of k) (relativeFieldPoint b K (𝟙 _)) P
              (pointedBase (.of k) (relativeFieldPoint b K (𝟙 _)))))) := by
  have hpos' : 0 < ringKrullDim (X.left.presheaf.stalk (b p)) := by
    rw [hd]
    exact_mod_cast hpos
  obtain ⟨O, hAffine, hO, Z, i, hi, hI, hs, hz⟩ :=
    Scheme.exists_smooth_cartier_neighborhood X.hom (b p) hpos'
  let : IsClosedImmersion i := hi
  let Y := (toSmoothSite X).obj (openObject O)
  let W : O.toScheme.Opens :=
    ⟨(Set.range i)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  let U := (SmoothSite.opensFunctor Y).obj W
  let j : U ⟶ Y := SmoothSite.openInclusion Y W
  let : IsOpenImmersion j.left := inferInstanceAs (IsOpenImmersion W.ι)
  let bO := openFieldPointLift K b p O hO
  refine ⟨O, hO, hAffine, Z, i, hi, hI, hs, hz, W, ?_, ?_⟩
  · exact (compl_compl (Set.range i)).symm
  · intro hmono
    let : Mono (colim.map (pointedCylinderRestriction (.of k) j
        (relativeFieldPoint bO K (𝟙 _))
        (LargeCohomology.presheaf.{u + 1, u + 1, u, u + 1}
          (SmoothSite.nisnevichTopology (Spec (.of k)))
            ((SheafWithTransfers.toSheaf k).obj F) (n + 1)))) := hmono
    have hbO : O.ι (bO p) = b p :=
      congrArg (fun f : Spec (.of K) ⟶ X.left => f p)
        (openFieldPointLift_ι K b p O hO)
    have hcenter : bO p ∈ Set.range i := by
      obtain ⟨z, hz⟩ := hz
      refine ⟨z, ?_⟩
      apply Subtype.ext
      exact hz.trans hbO.symm
    have hmiss : bO p ∉ Set.range j.left := by
      intro h
      change bO p ∈ Set.range W.ι at h
      rw [Scheme.Opens.range_ι] at h
      exact h hcenter
    let : IsNoetherian X.left := SmoothSite.isNoetherian_left X
    let : IsNoetherianRing (((𝟭 Scheme).obj X.left).presheaf.stalk (O.ι (bO p))) :=
      inferInstanceAs (IsNoetherianRing (X.left.presheaf.stalk (O.ι (bO p))))
    have hdO : ringKrullDim (Y.left.presheaf.stalk (bO p)) = d := by
      exact (Scheme.ringKrullDim_stalk_eq_of_etale O.ι (bO p)).trans
        ((congrArg (fun x : X.left => ringKrullDim (X.left.presheaf.stalk x)) hbO).trans hd)
    have hzero := projectionPointFiber_isZero_of_lowerRank j K bO p F hF n d
      hdO hmiss hLow hIH
    have hlocal := hzero.of_iso (pointedCylinderColimitFiberIso (.of k) Y
      (relativeFieldPoint bO K (𝟙 _)) ((SheafWithTransfers.toSheaf k).obj F) (n + 1))
    exact hlocal.of_iso (openFieldPointCylinderColimitIso X K b p O hO _).symm

end Motivic.FiniteEtaleSite
