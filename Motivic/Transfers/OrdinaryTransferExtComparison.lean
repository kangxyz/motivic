/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.OrdinaryTransferExtSource
public import Motivic.Transfers.OriginalGermEnvelopeAcyclic
public import Motivic.Transfers.EnoughInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective

/-! # Actual transfer Ext and original ordinary cohomology -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite
universe w w' u
namespace Motivic.SheafWithTransfers
variable (k : Type u) [Field k]
  [HasExt.{w} (SheafWithTransfers.{u + 1} k)]
  [HasExt.{w'} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- Forget transfers and pull back along the actual section source morphism. -/
def transferExtComparison (X : SmoothSite (Spec (.of k)))
    (F : SheafWithTransfers.{u + 1} k) (n : ℕ) :
    Ext.{w} ((transferRepresentable k).obj (Cor.mk X)) F n →+
      SheafCohomology.H.{w', u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k))) ((toSheaf k).obj F) n X :=
  ((Ext.mk₀ (ordinaryToTransferSource k X)).precomp ((toSheaf k).obj F) (zero_add n)).comp
    ((toSheaf k).mapExtAddHom _ F n)

@[simp]
theorem transferExtComparison_mk₀ (X : SmoothSite (Spec (.of k)))
    (F : SheafWithTransfers.{u + 1} k)
    (f : (transferRepresentable k).obj (Cor.mk X) ⟶ F) :
    transferExtComparison k X F 0 (Ext.mk₀ f) =
      Ext.mk₀ (ordinaryTransferHomEquiv k X F f) := by
  change (Ext.mk₀ (ordinaryToTransferSource k X)).comp
    ((Ext.mk₀ f).mapExactFunctor (toSheaf k)) (zero_add 0) = _
  rw [Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀, ← ordinaryTransferHomEquiv_apply]

/-- Comparison respects arbitrary Yoneda compositions in the coefficient variable. -/
theorem transferExtComparison_comp (X : SmoothSite (Spec (.of k)))
    {F G : SheafWithTransfers.{u + 1} k} {a b c : ℕ}
    (e : Ext.{w} ((transferRepresentable k).obj (Cor.mk X)) F a)
    (d : Ext.{w} F G b) (h : a + b = c) :
    transferExtComparison k X G c (e.comp d h) =
      (transferExtComparison k X F a e).comp (d.mapExactFunctor (toSheaf k)) h := by
  change (Ext.mk₀ (ordinaryToTransferSource k X)).comp
      ((e.comp d h).mapExactFunctor (toSheaf k)) (zero_add c) = _
  rw [Ext.mapExactFunctor_comp]
  exact (Ext.comp_assoc _ _ _ (zero_add a) h (by lia)).symm

/-- Degree zero is the actual section Hom equivalence. -/
theorem transferExtComparison_zero_bijective (X : SmoothSite (Spec (.of k)))
    (F : SheafWithTransfers.{u + 1} k) :
    Function.Bijective (transferExtComparison k X F 0) := by
  let e := (Ext.addEquiv₀ : Ext.{w} _ F 0 ≃+ (_ ⟶ F)) |>.trans
    ((ordinaryTransferHomEquiv k X F).trans Ext.addEquiv₀.symm)
  have he : ⇑(transferExtComparison k X F 0) = e := by
    funext z
    obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective _ _).surjective z
    rw [transferExtComparison_mk₀]
    change Ext.mk₀ _ = Ext.mk₀ (ordinaryTransferHomEquiv k X F (Ext.addEquiv₀ (Ext.mk₀ f)))
    congr 2
    exact ((Ext.addEquiv₀ : Ext.{w} _ F 0 ≃+ (_ ⟶ F)).apply_symm_apply f).symm
  rw [he]
  exact e.bijective

/-- Transfer-injective acyclicity gives comparison in every degree by dimension shifting. -/
theorem transferExtComparison_bijective (X : SmoothSite (Spec (.of k)))
    (F : SheafWithTransfers.{u + 1} k) (n : ℕ) :
    Function.Bijective (transferExtComparison k X F n) := by
  induction n generalizing F with
  | zero => exact transferExtComparison_zero_bijective k X F
  | succ n hn =>
    let I : InjectivePresentation F := Classical.arbitrary _
    let S := ShortComplex.mk _ _ (cokernel.condition I.f)
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel I.f }
    exact AddMonoidHom.bijective_of_surjective_of_bijective_of_right_exact _ _ _ _
      (transferExtComparison k X S.X₂ n) (transferExtComparison k X S.X₃ n)
      (transferExtComparison k X S.X₁ (n + 1))
      (by
        ext e
        symm
        exact (transferExtComparison_comp k X e (Ext.mk₀ S.g) (add_zero n)).trans
          (by rw [Ext.mapExactFunctor_mk₀]; rfl))
      (by
        ext e
        symm
        exact (transferExtComparison_comp k X e hS.extClass rfl).trans
          (by rw [Ext.mapExactFunctor_extClass]; rfl))
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' _ hS n (n + 1) rfl))
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' _ (hS.map (toSheaf k)) n (n + 1) rfl))
      (hn _).surjective (hn _)
      (fun e ↦ Ext.covariant_sequence_exact₁ _ hS e (Ext.eq_zero_of_injective _) rfl)
      (fun e ↦ Ext.covariant_sequence_exact₁ _ (hS.map (toSheaf k)) e
        (injective_underlying_H_succ_eq_zero k I.J X n _) rfl)

/-- The actual comparison as an additive equivalence, with independent Ext universes. -/
def transferExtEquiv (X : SmoothSite (Spec (.of k)))
    (F : SheafWithTransfers.{u + 1} k) (n : ℕ) :
    Ext.{w} ((transferRepresentable k).obj (Cor.mk X)) F n ≃+
      SheafCohomology.H.{w', u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k))) ((toSheaf k).obj F) n X :=
  AddEquiv.ofBijective (transferExtComparison k X F n) (transferExtComparison_bijective k X F n)

/-- Coefficient naturality uses the original ordinary cohomology coefficient map. -/
theorem transferExtEquiv_naturality_coeff (X : SmoothSite (Spec (.of k)))
    {F G : SheafWithTransfers.{u + 1} k} (f : F ⟶ G) (n : ℕ)
    (e : Ext.{w} ((transferRepresentable k).obj (Cor.mk X)) F n) :
    transferExtEquiv k X G n (e.comp (Ext.mk₀ f) (add_zero n)) =
      ((SheafCohomology.presheafFunctor
        (SmoothSite.nisnevichTopology (Spec (.of k))) n).map ((toSheaf k).map f)).app
          (op X) (transferExtEquiv k X F n e) := by
  change transferExtComparison k X G n (e.comp (Ext.mk₀ f) (add_zero n)) =
    (transferExtComparison k X F n e).comp (Ext.mk₀ ((toSheaf k).map f)) (add_zero n)
  rw [transferExtComparison_comp, Ext.mapExactFunctor_mk₀]

/-- Graph naturality is the unchanged ordinary restriction map. -/
theorem transferExtEquiv_naturality_graph
    {X Y : SmoothSite (Spec (.of k))} (f : X ⟶ Y)
    (F : SheafWithTransfers.{u + 1} k) (n : ℕ)
    (e : Ext.{w} ((transferRepresentable k).obj (Cor.mk Y)) F n) :
    transferExtEquiv k X F n
      ((Ext.mk₀ ((transferRepresentable k).map ((Cor.graphFunctor k).map f))).comp e
        (zero_add n)) =
      (SheafCohomology.presheaf (SmoothSite.nisnevichTopology (Spec (.of k)))
        ((toSheaf k).obj F) n).map f.op (transferExtEquiv k Y F n e) := by
  change (Ext.mk₀ (ordinaryToTransferSource k X)).comp
      (((Ext.mk₀ ((transferRepresentable k).map ((Cor.graphFunctor k).map f))).comp e
        (zero_add n)).mapExactFunctor (toSheaf k)) (zero_add n) =
    (Ext.mk₀ ((Hypercohomology.freeAbelianSheafFunctor
      (SmoothSite.nisnevichTopology (Spec (.of k)))).map f)).comp
        ((Ext.mk₀ (ordinaryToTransferSource k Y)).comp (e.mapExactFunctor (toSheaf k))
          (zero_add n)) (zero_add n)
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    ← Ext.comp_assoc_of_second_deg_zero, ← Ext.comp_assoc_of_second_deg_zero,
    Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀, ordinaryToTransferSource_naturality]

end Motivic.SheafWithTransfers
