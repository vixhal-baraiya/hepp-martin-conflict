import HeppCompute

/-! Native evaluation (`native_decide`): the Hepp tables of both graphs agree modulo the
primes in `chunk 5`. -/

namespace HM

theorem hepp_chunk_5 :
    heppMods (decomplete Ga 0) D (chunk 5) = heppMods (decomplete Gb 0) D (chunk 5) := by
  native_decide

end HM
