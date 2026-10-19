/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.Sheaf.UnderlyingExactness
public import Lean.Util.CollectAxioms

/-!
# Consumers of actual transfer-sheaf exactness

These consumers require only a field. All sheafification infrastructure is
provided by the existing actual abelian-group construction. Cokernels are
compared in the ordinary sheaf category, not objectwise on sections.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Motivic

universe u

namespace MotivicTest.Transfers.SheafExactness

variable (k : Type u) [Field k]

example : Abelian (PresheafWithTransfers.{u + 1} k) := inferInstance
example : Abelian (SheafWithTransfers.{u + 1} k) := inferInstance
example : PreservesFiniteLimits (PresheafWithTransfers.nisnevichSheafify k) := inferInstance
example : PreservesFiniteColimits (PresheafWithTransfers.nisnevichSheafify k) := inferInstance
example : PreservesFiniteLimits (SheafWithTransfers.toSheaf.{u + 1} k) := inferInstance
example : PreservesFiniteColimits (SheafWithTransfers.toSheaf.{u + 1} k) := inferInstance

/-- Exactness is both preserved and reflected without an additional transfer provider. -/
theorem ordinary_exact_iff (S : ShortComplex (SheafWithTransfers.{u + 1} k)) :
    (S.map (SheafWithTransfers.toSheaf k)).Exact ↔ S.Exact :=
  SheafWithTransfers.exact_toSheaf_iff k S

/-- The underlying comparison respects the actual ordinary-sheaf kernel inclusion. -/
theorem actual_kernel_map {F G : SheafWithTransfers.{u + 1} k} (f : F ⟶ G) :
    (SheafWithTransfers.underlyingKernelIso k f).hom ≫
        kernel.ι ((SheafWithTransfers.toSheaf k).map f) =
      (SheafWithTransfers.toSheaf k).map (kernel.ι f) :=
  SheafWithTransfers.underlyingKernelIso_hom_ι k f

/-- The underlying comparison respects the actual ordinary-sheaf cokernel map. -/
theorem actual_cokernel_map {F G : SheafWithTransfers.{u + 1} k} (f : F ⟶ G) :
    (SheafWithTransfers.toSheaf k).map (cokernel.π f) ≫
        (SheafWithTransfers.underlyingCokernelIso k f).hom =
      cokernel.π ((SheafWithTransfers.toSheaf k).map f) :=
  SheafWithTransfers.underlyingCokernelIso_π_hom k f

/-- Actual short exact transfer-sheaf sequences remain short exact after forgetting transfers. -/
theorem ordinary_shortExact {S : ShortComplex (SheafWithTransfers.{u + 1} k)}
    (hS : S.ShortExact) : (S.map (SheafWithTransfers.toSheaf k)).ShortExact :=
  SheafWithTransfers.shortExact_toSheaf k hS

open Lean in
run_cmd do
  for name in #[``CategoryTheory.AdditiveFunctor.abelian,
      ``Motivic.PresheafWithTransfers.nisnevichSheafify_preservesFiniteLimits,
      ``Motivic.SheafWithTransfers.abelian,
      ``Motivic.SheafWithTransfers.toSheaf_preservesColimitsOfShape,
      ``ordinary_exact_iff, ``actual_kernel_map, ``actual_cokernel_map, ``ordinary_shortExact] do
    let dependencies ← collectAxioms name
    for dependency in dependencies do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Transfer-sheaf abelianness and exactness use only standard Lean logical foundations."

end MotivicTest.Transfers.SheafExactness
