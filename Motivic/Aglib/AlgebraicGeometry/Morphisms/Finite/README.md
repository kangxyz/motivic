# Finite morphisms and component images

`Components.lean` proves that a finite generalizing morphism sends every actual
generic-component closure onto a target irreducible component. Its finite-flat
specialization supplies the generalizing property from flatness. Neither scheme
needs to be irreducible, reduced, Noetherian, or nonempty. Finiteness alone does
not give the component assertion.

The native namespace is `AlgebraicGeometry.Scheme.Hom`. The leaf reuses the
existing generic-point generalization theorem, currently in the downstream
`Motivic.AlgebraicGeometry.Cycles.GenericDominance` module; extracting that
prerequisite is a separate ownership task. The current consumer is the full
finite-flat correspondence assembly, which retains all components and lengths.
