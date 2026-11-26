import HeppCompute

/-! Native evaluation (`native_decide`): structure of the two completed graphs and their
Martin invariants. -/

namespace HM

theorem martin_a : martin (multiply Ga 1) = 71544 := by native_decide
theorem martin_b : martin (multiply Gb 1) = 71604 := by native_decide

theorem structure_a : (wellFormed Ga && noParallel Ga && regular Ga 4 && cutsOK Ga) = true := by
  native_decide
theorem structure_b : (wellFormed Gb && noParallel Gb && regular Gb 4 && cutsOK Gb) = true := by
  native_decide

theorem dec_a : (wellFormed (decomplete Ga 0) && maxDegLe (decomplete Ga 0) 4) = true := by
  native_decide
theorem dec_b : (wellFormed (decomplete Gb 0) && maxDegLe (decomplete Gb 0) 4) = true := by
  native_decide

theorem ne_a : (decomplete Ga 0).ne = 26 := by native_decide
theorem ne_b : (decomplete Gb 0).ne = 26 := by native_decide

end HM
