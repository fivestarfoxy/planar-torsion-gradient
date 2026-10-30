import Torsion.CompactSpectral.WeakHilbertCompact
import Torsion.CompactSpectral.RayleighCompact
import Torsion.CompactSpectral.PositiveEigenpair
import Torsion.CompactSpectral.TwoEigenpairs

/-!
# Compact self-adjoint eigenpair selection

The weak compactness and Rayleigh attainment modules are adapted from
Adam Benenson's `compact-spectral` (commit
`72cd62dbdd4c397d26fc0c5777d60fea2211e938`) under Apache-2.0, as documented
in those sources and the accompanying `CompactSpectral/LICENSE`.
The additional positive and two-eigenpair theorems give actual unit
eigenvectors and their variational bounds for the original operator.
-/
