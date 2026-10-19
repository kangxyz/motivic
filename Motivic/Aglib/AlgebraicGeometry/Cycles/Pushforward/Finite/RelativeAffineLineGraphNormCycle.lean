/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Cycles.Pushforward.Finite.GenericRatioNormCycle
public import Motivic.Aglib.AlgebraicGeometry.Scheme.NormalStalks
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Source.AffineParameterNormal
public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.GraphFreeCover

/-!
# The original compactification graph norm-cycle identity

The actual two-chart producer and canonical projective base-change geometry
discharge the free-cover and normal-target inputs. Both original section maps
and their canonical generic ratio remain unchanged. A full-boundary unit
representative is a separate geometric construction, not supplied here.


Intended upstream module:
`Aglib.AlgebraicGeometry.Cycles.Pushforward.Finite.RelativeAffineLineGraphNormCycle`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification

universe u
namespace AlgebraicGeometry.Scheme

local instance {X : Scheme.{u}} [IsNoetherian X]
    {M : X.Modules} (φ : M ⟶ (show X.Modules from SheafOfModules.unit X.ringCatSheaf)) :
    IsNoetherian (Scheme.Modules.Hom.zeroScheme φ) :=
  _root_.AlgebraicGeometry.Scheme.isNoetherian_of_finiteType (Scheme.Modules.Hom.zeroInclusion φ)

/-- After one original coefficient localization, the graph-product norm identity
holds for every actual normal integral affine parameter and every pair of monic
maps from the same original line bundle. No free-cover or normality family is
assumed, and the source compactification may be disconnected or nonreduced. -/
theorem exists_relativeAffineLine_graph_norm_cycle
    (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [IsNoetherianRing R] {Y : Scheme.{u}}
    (p : Y ⟶ Spec (.of (Polynomial R))) [Etale p] [QuasiCompact p] :
    ∃ r : R, r ≠ 0 ∧
      let A := Localization.Away r
      let m := ProjectiveSpace.map (algebraMap R A) (ULift.{u} (Fin 2))
      let f := pullback.snd (toProjectiveLine R p) m
      let q := ProjectiveSpace.toSpec A (ULift.{u} (Fin 2))
      ∀ {T : Scheme.{u}} [IsAffine T] [IsDomain Γ(T, ⊤)]
        [IsIntegrallyClosed Γ(T, ⊤)] [IsNoetherianRing Γ(T, ⊤)]
        (j : T ⟶ Limits.pullback (toProjectiveLine R p) m),
        let b := j ≫ f ≫ q
        let P := Limits.pullback b q
        let C := Limits.pullback b (f ≫ q)
        let F := graphProductMap q f j
        let hn := RelativeProjectiveLine.affineParameterPullback_normal A b
        let : IsIntegral P := hn.1
        let : IsNoetherian P := hn.2.1
        let : IsNoetherian C := _root_.AlgebraicGeometry.Scheme.isNoetherian_of_finiteType F
        ∀ (L : LineBundle C)
          (φ ψ : L.val ⟶ SheafOfModules.unit C.ringCatSheaf) [Mono φ] [Mono ψ]
          (x : P),
          (_root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward F
            (_root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward
                (Scheme.Modules.Hom.zeroInclusion φ)
                (_root_.AlgebraicGeometry.Scheme.fundamentalPointCycle
                    (Scheme.Modules.Hom.zeroScheme φ)) -
              _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward
                  (Scheme.Modules.Hom.zeroInclusion ψ)
                (_root_.AlgebraicGeometry.Scheme.fundamentalPointCycle
                    (Scheme.Modules.Hom.zeroScheme ψ)))) x =
            P.ord (Scheme.genericFiberLineRatioNorm F L φ ψ) x := by
  obtain ⟨r, hr, hcover⟩ := exists_graphProductMap_free_affine_cover R p
  refine ⟨r, hr, ?_⟩
  dsimp only
  intro T hT hdomain hclosed hnoeth j
  let A := Localization.Away r
  let m := ProjectiveSpace.map (algebraMap R A) (ULift.{u} (Fin 2))
  let f := pullback.snd (toProjectiveLine R p) m
  let q := ProjectiveSpace.toSpec A (ULift.{u} (Fin 2))
  let b := j ≫ f ≫ q
  let P := Limits.pullback b q
  let F := graphProductMap q f j
  have hn := RelativeProjectiveLine.affineParameterPullback_normal A b
  let : IsIntegral P := hn.1
  let : IsNoetherian P := hn.2.1
  intro L φ ψ hφ hψ x
  apply _root_.AlgebraicGeometry.Scheme.residuePushforward_zeroCycle_sub_eq_ord_genericRatioNorm F
      ?_ (hcover q j) L φ ψ x
  intro U hU hne
  let : Nonempty U := hne
  exact _root_.AlgebraicGeometry.Scheme.isIntegrallyClosed_sections_of_stalks hn.2.2 hU

end AlgebraicGeometry.Scheme
