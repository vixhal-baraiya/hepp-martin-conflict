import HeppCompute

/-! Native evaluation (`native_decide`): the Hepp tables of both graphs agree modulo the
primes in `chunk 1`. -/

namespace HM

theorem hepp_chunk_1 :
    heppMods (decomplete Ga 0) D (chunk 1) = heppMods (decomplete Gb 0) D (chunk 1) := by
  native_decide

end HM
