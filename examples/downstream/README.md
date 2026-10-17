# Independent client

This is a separate Lake package requiring `Motivic` by relative path. Its
single module imports the public Milnor K low-degree leaf and uses the original
symbol quotient and degree-zero equivalence. It does not import tests or
historical records.

Resolve the committed dependencies, then use `lake build MotivicClient` from
this directory. For distribution, replace the relative requirement with this
repository's URL and an exact reviewed commit. See the root development guide
for cache and resource constraints.
