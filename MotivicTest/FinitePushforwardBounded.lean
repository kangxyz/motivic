/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Cycles.FinitePushforwardBounded
public import Motivic.AlgebraicGeometry.Correspondences.IntermediateDiagonalLists

/-!
# Genuine whole-fiber boundedness consumers

The actual finite image-product map receives genuinely point-dependent source
bounds. A separate truncated tilde family supplies actual source-stalk vanishing
with completely unrestricted original modules in the remaining degrees.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

universe u

namespace Motivic.MotivicTest.FinitePushforwardBounded

open FiniteSchemeEuler

section Correspondence

variable {S X Y Z W : Scheme.{u}}
  {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S} {i : W ⟶ S}
  (F : FiniteCorrespondenceGenerator f g) (G : FiniteCorrespondenceGenerator g h)
  (H : FiniteCorrespondenceGenerator h i) [IsSeparated h]
  {U : (F.leftIntermediateImageProduct G H).Opens} (hU : IsAffineOpen U)
  (p : Spec Γ(F.leftIntermediateImageProduct G H, U))
  (N : ℕ → (F.leftIntermediateSupportProduct G H).Modules)
  [∀ n, (N n).IsQuasicoherent]

/-- Different original source bounds yield the actual maximum for the correct finite map. -/
theorem actualPointwiseMaximum
    (b : {x : F.leftIntermediateSupportProduct G H //
      F.leftIntermediateImageMap G H x = hU.fromSpec p} → ℕ)
    (hN : ∀ x : {x : F.leftIntermediateSupportProduct G H //
        F.leftIntermediateImageMap G H x = hU.fromSpec p}, ∀ n, b x ≤ n →
      Subsingleton (originalSourceStalkModule (N n) x.1))
    (n : ℕ) (hn : originalFiberDegreeBound (F.leftIntermediateImageMap G H) hU p b ≤ n) :
    Subsingleton (originalWholeLocalizedModule (F.leftIntermediateImageMap G H) hU p (N n)) :=
  originalWholeFamily_zero_ge _ hU p N b hN n hn

/-- A uniform whole coefficient bound is derived from merely pointwise eventual vanishing. -/
theorem actualEventualBound
    (hN : ∀ x : {x : F.leftIntermediateSupportProduct G H //
        F.leftIntermediateImageMap G H x = hU.fromSpec p}, ∃ b : ℕ, ∀ n, b ≤ n →
      Subsingleton (originalSourceStalkModule (N n) x.1)) :
    ∃ b : ℕ, ∀ n, b ≤ n → Subsingleton
      (originalWholeLocalizedModule (F.leftIntermediateImageMap G H) hU p (N n)) :=
  originalWholeFamily_exists_bound _ hU p N hN

/-- The original image-product family has finite outer support without a length premise. -/
theorem actualFiniteOuterSupport
    (hN : ∀ x : {x : F.leftIntermediateSupportProduct G H //
        F.leftIntermediateImageMap G H x = hU.fromSpec p}, ∃ b : ℕ, ∀ n, b ≤ n →
      Subsingleton (originalSourceStalkModule (N n) x.1)) :
    {n : ℕ | ¬ Subsingleton
      (originalWholeLocalizedModule (F.leftIntermediateImageMap G H) hU p (N n))}.Finite :=
  originalWholeFamily_nonzero_finite _ hU p N hN

end Correspondence

section TruncatedTilde

variable (B : CommRingCat.{u}) (L : ℕ → ModuleCat.{u} B) (d : ℕ)

/-- A genuine QC family whose lower-degree original modules are entirely unrestricted. -/
abbrev truncatedTildeFamily (n : ℕ) : (Spec B).Modules :=
  (tilde.functor B).obj (if n < d then L n else ModuleCat.of B (Fin 0 → B))

/-- Every member is the actual tilde of its specified coordinate module. -/
instance truncatedTildeFamily_quasicoherent (n : ℕ) :
    (truncatedTildeFamily B L d n).IsQuasicoherent :=
  inferInstanceAs (((tilde.functor B).obj
    (if n < d then L n else ModuleCat.of B (Fin 0 → B))).IsQuasicoherent)

/-- The actual tilde stalk of a zero module vanishes through the original tensor comparison. -/
theorem zeroTildeSourceStalk (M : ModuleCat.{u} B) [Subsingleton M] (x : Spec B) :
    Subsingleton (originalSourceStalkModule ((tilde.functor B).obj M) x) := by
  have hz : Subsingleton ((AffinePushforward.stalkTensorFunctor B x).obj M) := by
    change Subsingleton ((Spec B).presheaf.stalk x ⊗[B] M)
    infer_instance
  exact ((AffinePushforward.tildeStalkIso B x).app M).toLinearEquiv.toEquiv.subsingleton_congr.mp hz

/-- The original source-stalk bound is proved from the actual family definition. -/
theorem truncatedTildeSourceBound (x : Spec B) (n : ℕ) (hn : d ≤ n) :
    Subsingleton (originalSourceStalkModule (truncatedTildeFamily B L d n) x) := by
  dsimp only [truncatedTildeFamily]
  simp only [Nat.not_lt_of_ge hn, ↓reduceIte]
  exact zeroTildeSourceStalk B (ModuleCat.of B (Fin 0 → B)) x

variable {Y : Scheme.{u}} (f : Spec B ⟶ Y) [IsFinite f]
  {U : Y.Opens} (hU : IsAffineOpen U) (p : Spec Γ(Y, U))

/-- The whole-fiber bound consumes derived stalk vanishing; the surviving
coordinate modules have no finite-generation, finite-length or rank assumptions. -/
theorem unrestrictedTruncatedWholeBound :
    ∃ b : ℕ, ∀ n, b ≤ n →
      Subsingleton (originalWholeLocalizedModule f hU p (truncatedTildeFamily B L d n)) :=
  originalWholeFamily_exists_bound f hU p (truncatedTildeFamily B L d)
    (fun x => ⟨d, fun n hn => truncatedTildeSourceBound B L d x.1 n hn⟩)

/-- The same derived actual bound gives finite outer support of the whole localized family. -/
theorem unrestrictedTruncatedOuterSupport :
    {n : ℕ | ¬ Subsingleton
      (originalWholeLocalizedModule f hU p (truncatedTildeFamily B L d n))}.Finite :=
  originalWholeFamily_nonzero_finite f hU p (truncatedTildeFamily B L d)
    (fun x => ⟨d, fun n hn => truncatedTildeSourceBound B L d x.1 n hn⟩)

end TruncatedTilde

end Motivic.MotivicTest.FinitePushforwardBounded
