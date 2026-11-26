import HeppCompute

/-! Native evaluation (`native_decide`): component certificates and `omega` values for all
`2^26` edge subsets of the decompletion of `Gb` at vertex 0. -/

namespace HM

theorem cert_b : certAll (decomplete Gb 0) = true := by native_decide

theorem phi_b : phiOK (decomplete Gb 0) D = true := by native_decide

end HM
