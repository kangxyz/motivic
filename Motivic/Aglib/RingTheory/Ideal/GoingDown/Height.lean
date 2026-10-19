/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# Heights under integral maps satisfying going down

Contraction preserves prime heights for integral maps satisfying going down.
In particular this applies to finite flat algebras without a domain, reducedness,
connectedness or nontriviality assumption on either ring. The actual contraction
map is retained. This is the height input for whole regular-principal zero cycles.


Intended upstream module: `Aglib.RingTheory.Ideal.GoingDown.Height`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.Cycles.Pushforward.Finite.AffineRegularNormCycle`.
-/

@[expose] public section

universe u v

namespace PrimeSpectrum

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
  [IsNoetherianRing R] [IsNoetherianRing S]

/-- Integral contraction preserves heights when the original algebra satisfies
going down, including for nonintegral and disconnected rings. -/
theorem height_comap_eq_of_isIntegral_of_hasGoingDown
    [Algebra.IsIntegral R S] [Algebra.HasGoingDown R S] (q : PrimeSpectrum S) :
    (q.comap (algebraMap R S)).asIdeal.height = q.asIdeal.height := by
  let p := q.comap (algebraMap R S)
  let : q.asIdeal.LiesOver p.asIdeal := ⟨rfl⟩
  apply le_antisymm
  · rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p.asIdeal q.asIdeal]
    exact le_self_add
  · rw [q.height_eq_orderHeight, p.height_eq_orderHeight]
    exact Order.height_le_height_apply_of_strictMono
      (fun x : PrimeSpectrum S => x.comap (algebraMap R S))
      (fun _ _ hxy => Ideal.IsIntegral.under_lt_under hxy) q

/-- Heights of all original primes are preserved by a finite flat algebra map.
No component is assumed free or integral. -/
theorem height_comap_eq_of_finite_flat
    [Module.Finite R S] [Module.Flat R S] (q : PrimeSpectrum S) :
    (q.comap (algebraMap R S)).asIdeal.height = q.asIdeal.height :=
  height_comap_eq_of_isIntegral_of_hasGoingDown R S q

end PrimeSpectrum
