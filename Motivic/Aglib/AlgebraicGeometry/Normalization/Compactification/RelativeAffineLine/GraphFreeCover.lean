/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Graph.Frames.FreeProductCharts
public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.FiniteFlat

/-!
# Actual free affine covers for the compactification graph product

The original two-standard-chart producer supplies one nonzero coefficient
localization. Its literal chart pullbacks are transported by native pullback
pasting, and the original graph-product map then has canonical free affine
neighborhoods at every point. No free-cover family is supplied as a hypothesis.


Intended upstream module:
`Aglib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.GraphFreeCover`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.Cycles.Pushforward.Finite.RelativeAffineLineGraphNormCycle`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.FiniteSchemeNormBaseChange
open AlgebraicGeometry.Scheme.Hom

universe u
namespace AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification

/-- One actual base localization gives the original compactification graph map
its genuine canonical local coordinate-free cover, for any unchanged parameter
map into that localized compactification. -/
theorem exists_graphProductMap_free_affine_cover
    (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [IsNoetherianRing R] {Y : Scheme.{u}}
    (p : Y ⟶ Spec (.of (Polynomial R))) [Etale p] [QuasiCompact p] :
    ∃ r : R, r ≠ 0 ∧
      let A := Localization.Away r
      let m := ProjectiveSpace.map (algebraMap R A) (ULift.{u} (Fin 2))
      let f := pullback.snd (toProjectiveLine R p) m
      ∀ {S T : Scheme.{u}} (q : ProjectiveSpace A (ULift.{u} (Fin 2)) ⟶ S)
        (j : T ⟶ Limits.pullback (toProjectiveLine R p) m)
        (x : (Limits.pullback (j ≫ f ≫ q) q : Scheme.{u})),
        ∃ (U : (Limits.pullback (j ≫ f ≫ q) q).Opens) (hU : IsAffineOpen U), x ∈ U ∧
          (let : Algebra Γ(Limits.pullback (j ≫ f ≫ q) q, U)
              Γ(Limits.pullback (graphProductMap q f j) hU.fromSpec, ⊤) :=
            (scalarMap (pullback.snd (graphProductMap q f j) hU.fromSpec)).toAlgebra
           Module.Free Γ(Limits.pullback (j ≫ f ≫ q) q, U)
             Γ(Limits.pullback (graphProductMap q f j) hU.fromSpec, ⊤)) := by
  obtain ⟨r, hr, hf⟩ := exists_free_chart_sections_baseChange R p
  refine ⟨r, hr, ?_⟩
  dsimp only
  intro S T q j x
  let A := Localization.Away r
  let m := ProjectiveSpace.map (algebraMap R A) (ULift.{u} (Fin 2))
  let f := pullback.snd (toProjectiveLine R p) m
  have hfree (i : ULift.{u} (Fin 2)) :
      let : Algebra (Polynomial A) Γ(Limits.pullback f (RelativeProjectiveLine.chart A i), ⊤) :=
        (scalarMap (pullback.snd f (RelativeProjectiveLine.chart A i))).toAlgebra
      Module.Free (Polynomial A) Γ(Limits.pullback f (RelativeProjectiveLine.chart A i), ⊤) := by
    let g := RelativeProjectiveLine.chart A i ≫ m
    let : Algebra (Polynomial A) Γ(Limits.pullback (toProjectiveLine R p) g, ⊤) :=
      (scalarMap (pullback.snd (toProjectiveLine R p) g)).toAlgebra
    let : Module.Free (Polynomial A) Γ(Limits.pullback (toProjectiveLine R p) g, ⊤) := hf i
    let E := pullbackLeftPullbackSndIso (toProjectiveLine R p) m
      (RelativeProjectiveLine.chart A i)
    exact sections_free_of_iso (pullback.snd (toProjectiveLine R p) g)
      (pullback.snd f (RelativeProjectiveLine.chart A i)) E.symm (by simp [E, f, g])
  apply graphProductMap_exists_free_affine_neighborhood q f j
    (fun _ : ULift.{u} (Fin 2) => CommRingCat.of (Polynomial A))
    (RelativeProjectiveLine.chart A) ?_ hfree x
  intro z
  have hz : z ∈ (⨆ i, (RelativeProjectiveLine.chart A i).opensRange) := by
    rw [RelativeProjectiveLine.iSup_chart_opensRange]
    trivial
  exact TopologicalSpace.Opens.mem_iSup.mp hz

end AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification
