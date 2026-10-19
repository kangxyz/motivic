# Finite coefficients in the current motivic model

| Exact import | Interface |
| --- | --- |
| `Motivic.Cohomology.Coefficients.Finite.Complex` | Original motivic cone and coefficient maps |
| `Motivic.Cohomology.Coefficients.Finite.Hypercohomology` | Ordinary hypercohomology of the original coefficient complex |
| `Motivic.Cohomology.Coefficients.Finite.WeightOne` | Weight-one finite-coefficient comparison |

`Motivic.Cohomology.Coefficients.Finite` exposes the current `Complex` and
`Hypercohomology` lower leaves.

`Motivic.motivicFiniteComplex k q n` is the actual cone of
`n • 𝟙 (Motivic.motivicComplex k q)` for every natural `n`. It retains the
original `integral` and `bockstein` maps. This is the coefficient construction
for the [Suslin–Voevodsky model](../../SuslinVoevodsky/README.md).

The underlying operation is
[`CochainComplex.finiteCoefficients`](../../../Aglib/Algebra/Homology/CochainComplex/FiniteCoefficients/README.md),
with actual cone convention `a = snd`, positive Bockstein `b = -fst`, and the
original reduction/insertion maps. No termwise replacement or derived-tensor
identification is implicit. Any such description requires its own comparison.

Finite-coefficient hypercohomology uses the original underlying ordinary sheaf
complex and actual coefficient maps. It retains the ordinary derived-category
hypotheses, field universe `u`, transfer coefficient universe `u+1`, integer
cohomological degree and natural weight. Weight-one coefficient comparisons
and coefficient sequences consume these maps; their stronger hypotheses remain
on their own statements.

The cone construction includes zero and unit levels. Do not add invertibility
of `n` or change the sign to make a replacement sequence agree. A future model's
coefficients need their own construction and explicit comparison with this one.
