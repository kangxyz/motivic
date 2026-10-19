/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Homology.Koszul.TensorQuasiIsoBoundaries

/-!
# Finite K-flatness of the actual Koszul complex

Tensoring an arbitrary nonnegative chain quasi-isomorphism with the constructed
ring Koszul complex preserves quasi-isomorphisms. The proof uses the explicit
two-column argument for one scalar, followed by finite-list induction through
the actual chain tensor associator. No regularity or flatness of the coefficient
complex is assumed.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory

namespace ChainComplex.Koszul

variable {R : Type u} [CommRing R]
variable {K L : ChainComplex (ModuleCat.{u} R) ℕ} (f : K ⟶ L)

set_option backward.isDefEq.respectTransparency false in
/-- The genuine finite Koszul ring complex preserves all nonnegative quasi-isomorphisms. -/
theorem tensor_quasiIso (s : List R) [QuasiIso f] : QuasiIso (chainComplex s ◁ f) := by
  induction s with
  | nil =>
    change QuasiIso ((𝟙_ (ChainComplex (ModuleCat R) ℕ)) ◁ f)
    have : QuasiIso (((𝟙_ (ChainComplex (ModuleCat R) ℕ)) ◁ f) ≫ (λ_ L).hom) := by
      rw [leftUnitor_naturality]
      infer_instance
    exact quasiIso_of_comp_right ((𝟙_ (ChainComplex (ModuleCat R) ℕ)) ◁ f) (λ_ L).hom
  | cons a s ih =>
    change QuasiIso ((singleComplex R a ⊗ chainComplex s) ◁ f)
    have : QuasiIso (chainComplex s ◁ f) := ih
    have : QuasiIso (singleComplex R a ◁ (chainComplex s ◁ f)) :=
      singleTensor_quasiIso a (chainComplex s ◁ f)
    have : QuasiIso (((singleComplex R a ⊗ chainComplex s) ◁ f) ≫
        (α_ (singleComplex R a) (chainComplex s) L).hom) := by
      rw [associator_naturality_right]
      infer_instance
    exact quasiIso_of_comp_right ((singleComplex R a ⊗ chainComplex s) ◁ f)
      (α_ (singleComplex R a) (chainComplex s) L).hom

/-- The induced isomorphism is on homology of the actual chain tensor products. -/
noncomputable def tensorHomologyIso (s : List R) [QuasiIso f] (n : ℕ) :
    (HomologicalComplex.tensorObj (chainComplex s) K).homology n ≅
      (HomologicalComplex.tensorObj (chainComplex s) L).homology n := by
  have : QuasiIso (chainComplex s ◁ f) := tensor_quasiIso f s
  exact isoOfQuasiIsoAt (chainComplex s ◁ f) n

/-- Any projective resolution may be augmented under the actual finite Koszul tensor. -/
theorem tensor_resolution_quasiIso (s : List R) {M : ModuleCat.{u} R}
    (P : ProjectiveResolution M) : QuasiIso (chainComplex s ◁ P.π) :=
  tensor_quasiIso P.π s

/-- Resolving the arbitrary coefficient module does not change Koszul tensor homology. -/
noncomputable def tensorResolutionHomologyIso (s : List R) {M : ModuleCat.{u} R}
    (P : ProjectiveResolution M) (n : ℕ) :
    (HomologicalComplex.tensorObj (chainComplex s) P.complex).homology n ≅
      (HomologicalComplex.tensorObj (chainComplex s)
        ((ChainComplex.single₀ (ModuleCat R)).obj M)).homology n :=
  tensorHomologyIso P.π s n

end ChainComplex.Koszul
