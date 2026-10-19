/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Cycles.Fundamental.Invariance
public import Motivic.Aglib.AlgebraicGeometry.Scheme.FiniteTypeNoetherian

/-!
# Fundamental cycles of actual closed subschemes

The fundamental cycle of a closed subscheme is formed on that subscheme using
its original local rings, then pushed into the ambient scheme. The closed
immersion has residue degree one, so the local lengths are unchanged. An
integral closed subscheme gives its literal integral-cycle basis vector.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.Hom

variable {X : Scheme.{u}} [IsNoetherian X]

/-- The closed subscheme's local Noetherianity and quasi-compactness are inherited geometrically. -/
instance isNoetherian_closedSubscheme (I : X.IdealSheafData) : IsNoetherian I.subscheme :=
  isNoetherian_of_finiteType I.subschemeι

/-- The fundamental cycle of an actual closed subscheme, pushed into its ambient scheme. -/
noncomputable def closedFundamentalCycle (I : X.IdealSheafData) : IntegralCycle X :=
  IntegralCycle.finitePushforward I.subschemeι (fundamentalCycle I.subscheme)

/-- The ambient point representation is literal reindexing along the closed immersion. -/
theorem toPoints_closedFundamentalCycle (I : X.IdealSheafData) :
    IntegralCycle.toPoints (closedFundamentalCycle I) =
      Finsupp.mapDomain I.subschemeι (fundamentalPointCycle I.subscheme) := by
  rw [closedFundamentalCycle, ← AddMonoidHom.comp_apply,
    IntegralCycle.toPoints_finitePushforward, AddMonoidHom.comp_apply,
    toPoints_fundamentalCycle, residuePushforward_eq_mapDomain_of_surjectiveOnStalks]
  rfl

/-- The multiplicity is the length of the original closed subscheme's generic local ring. -/
theorem closedFundamentalCycle_component (I : X.IdealSheafData)
    (x : genericPoints I.subscheme) :
    closedFundamentalCycle I (IntegralClosedSubscheme.pointClosure (I.subschemeι x.val)) =
      (genericMultiplicity x : ℤ) := by
  have h := congrArg (fun c : FiniteSupportCycle X => c (I.subschemeι x.val))
    (toPoints_closedFundamentalCycle I)
  rw [Finsupp.mapDomain_apply_of_injective I.subschemeι.isEmbedding.injective,
    fundamentalPointCycle_apply] at h
  have hleft : IntegralCycle.toPoints (closedFundamentalCycle I) (I.subschemeι x.val) =
      closedFundamentalCycle I
        (IntegralClosedSubscheme.pointClosure (I.subschemeι x.val)) := by
    change Finsupp.mapDomain IntegralClosedSubscheme.point (closedFundamentalCycle I)
      (I.subschemeι x.val) = _
    simpa only [IntegralClosedSubscheme.point_pointClosure] using
      Finsupp.mapDomain_apply_of_injective IntegralClosedSubscheme.point_injective
        (closedFundamentalCycle I)
        (IntegralClosedSubscheme.pointClosure (I.subschemeι x.val))
  rw [hleft] at h
  simpa [x.property] using h

/-- An integral closed subscheme gives its actual ideal-sheaf generator with coefficient one. -/
theorem closedFundamentalCycle_of_isIntegral (I : X.IdealSheafData) [IsIntegral I.subscheme] :
    closedFundamentalCycle I = Finsupp.single ⟨I, inferInstance⟩ 1 := by
  rw [closedFundamentalCycle, fundamentalCycle_of_isIntegral,
    IntegralCycle.finitePushforward_single, residueDegree_of_surjectiveOnStalks]
  simp only [Nat.cast_one, mul_one]
  congr 1
  apply IntegralClosedSubscheme.point_injective
  rw [IntegralClosedSubscheme.point_finiteImage, IntegralClosedSubscheme.point_pointClosure]
  rfl

end AlgebraicGeometry.Scheme
