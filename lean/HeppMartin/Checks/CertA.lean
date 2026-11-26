import HeppCompute

/-! Native evaluation (`native_decide`): component certificates and `omega` values for all
`2^26` edge subsets of the decompletion of `Ga` at vertex 0. -/

namespace HM

theorem cert_a : certAll (decomplete Ga 0) = true := by native_decide

theorem phi_a : phiOK (decomplete Ga 0) D = true := by native_decide

end HM
