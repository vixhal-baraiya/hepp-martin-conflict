import HeppCompute

/-! Native evaluation (`native_decide`): the Hepp tables of both graphs agree modulo the
primes in `chunk 0`. -/

namespace HM

theorem hepp_chunk_0 :
    heppMods (decomplete Ga 0) D (chunk 0) = heppMods (decomplete Gb 0) D (chunk 0) := by
  native_decide

end HM
