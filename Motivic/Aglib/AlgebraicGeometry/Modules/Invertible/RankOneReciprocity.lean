/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Dual
public import Aglib.AlgebraicGeometry.Modules.Invertible.Trivialization

/-! # Reciprocity of sections of an actual line bundle

A linear functional on a locally free rank-one sheaf satisfies the scalar-exchange
identity on arbitrary open sections. The proof uses actual local unit charts and
sheaf separatedness, without imposing a global trivialization.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules.Invertible

private theorem smul_exchange_of_linearEquiv
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    (c : M ≃ₗ[R] R) (f : M → R)
    (hf : ∀ (r : R) (m : M), f (r • m) = r * f m) (x y : M) :
    f x • y = f y • x := by
  let v : M := c.symm 1
  have hgen (m : M) : m = c m • v := by
    apply c.injective
    simp [v]
  conv_lhs => rw [hgen x, hgen y]
  conv_rhs => rw [hgen y, hgen x]
  rw [hf, hf, smul_smul, smul_smul]
  congr 1
  simp only [mul_comm, mul_left_comm]

/-- The scalar-exchange identity for a section of the actual dual line bundle. -/
theorem dual_section_smul_exchange (X : Scheme.{u}) (L : LineBundle X)
    (U : X.Opensᵒᵖ) (d : (dualLineBundle X L).val.val.obj U)
    (x y : L.val.val.obj U) :
    (show Γ(X, U.unop) from d.val.app (op (Over.mk (𝟙 U.unop))) x) • y =
      (show Γ(X, U.unop) from d.val.app (op (Over.mk (𝟙 U.unop))) y) • x := by
  let a : Γ(X, U.unop) := d.val.app (op (Over.mk (𝟙 U.unop))) x
  let b : Γ(X, U.unop) := d.val.app (op (Over.mk (𝟙 U.unop))) y
  change a • y = b • x
  have hc : Presheaf.equalizerSieve (F := L.val.val.presheaf) (a • y) (b • x) ∈
      (Opens.grothendieckTopology X) U.unop := by
    intro z hzU
    obtain ⟨W, hzW, ⟨e⟩⟩ :=
      (isLocallyRankOne_iff_local_unit X L.val).mp L.property z
    let V : X.Opens := W ⊓ U.unop
    let j : V ⟶ U.unop := homOfLE inf_le_right
    refine ⟨V, j, ?_, ⟨hzW, hzU⟩⟩
    change L.val.val.map j.op (a • y) = L.val.val.map j.op (b • x)
    rw [L.val.val.map_smul, L.val.val.map_smul]
    let f : L.val.val.obj (op V) → Γ(X, V) :=
      fun m => d.val.app (op (Over.mk j)) m
    have hnat (m : L.val.val.obj U) :
        f (L.val.val.map j.op m) =
          X.presheaf.map j.op (d.val.app (op (Over.mk (𝟙 U.unop))) m) := by
      exact NatTrans.naturality_apply d.val
        (Over.homMk j : Over.mk j ⟶ Over.mk (𝟙 U.unop)).op m
    change X.presheaf.map j.op a • L.val.val.map j.op y =
      X.presheaf.map j.op b • L.val.val.map j.op x
    rw [show X.presheaf.map j.op a = f (L.val.val.map j.op x) from (hnat x).symm,
      show X.presheaf.map j.op b = f (L.val.val.map j.op y) from (hnat y).symm]
    apply smul_exchange_of_linearEquiv
      (chartSectionEquiv X L.val W e V inf_le_left) f
    intro r m
    exact d.property (op (Over.mk j)) r m
  apply L.val.isSheaf.isSeparated U.unop _ hc
  intro V j hj
  exact hj

/-- Evaluations of two dual sections against two line-bundle sections satisfy reciprocity. -/
theorem dual_section_mul_exchange (X : Scheme.{u}) (L : LineBundle X)
    (U : X.Opensᵒᵖ) (d e : (dualLineBundle X L).val.val.obj U)
    (x y : L.val.val.obj U) :
    (show Γ(X, U.unop) from d.val.app (op (Over.mk (𝟙 U.unop))) x) *
        (show Γ(X, U.unop) from e.val.app (op (Over.mk (𝟙 U.unop))) y) =
      (show Γ(X, U.unop) from d.val.app (op (Over.mk (𝟙 U.unop))) y) *
        (show Γ(X, U.unop) from e.val.app (op (Over.mk (𝟙 U.unop))) x) := by
  have h := congrArg (fun m : L.val.val.obj U =>
    e.val.app (op (Over.mk (𝟙 U.unop))) m)
      (dual_section_smul_exchange X L U d x y)
  exact (e.property (op (Over.mk (𝟙 U.unop)))
    (show Γ(X, U.unop) from d.val.app (op (Over.mk (𝟙 U.unop))) x) y).symm.trans
      (h.trans (e.property (op (Over.mk (𝟙 U.unop)))
        (show Γ(X, U.unop) from d.val.app (op (Over.mk (𝟙 U.unop))) y) x))

end AlgebraicGeometry.Scheme.Modules.Invertible
