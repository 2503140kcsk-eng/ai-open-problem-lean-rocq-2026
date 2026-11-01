module

import OmegaOneSeparation
import StandardBorelCore
import ExpectedLossBridge

/-!
A lightweight, reproducible audit target. The build log records the
transitive axiom dependencies of the principal Lean results. In particular,
the output must be inspected for sorryAx; classical choice and quotient/
propositional extensionality are reported rather than silently described as
constructive.
-/

#print axioms PublicSetting.OmegaOne.omegaOne_finite_horizon_separation
#print axioms PublicSetting.StandardBorelCore.exists_universal_core_point
#print axioms PublicSetting.ExpectedLossBridge.integral_finset_condExp_eq_integral_finset
