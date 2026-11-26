import HeppMartin.Main

/-! Prints the axioms the main results depend on. Besides the three standard axioms of Lean and
Mathlib (`propext`, `Classical.choice`, `Quot.sound`) the list contains one axiom per
`native_decide` check in `HeppMartin/Checks`, stating that the compiled evaluation of that Boolean
check returned `true`. -/

#print axioms HM.not_both
#print axioms HM.hepp_equal
#print axioms HM.hepp_eq_hq
#print axioms HM.heppMods_eq
#print axioms HM.omegaFast_eq_of_certAll
