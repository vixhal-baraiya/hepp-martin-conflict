import HeppCompute

/-! Native evaluation (`native_decide`): the Hepp tables of both graphs agree modulo the
primes in `chunk 9`. -/

namespace HM

theorem hepp_chunk_9 :
    heppMods (decomplete Ga 0) D (chunk 9) = heppMods (decomplete Gb 0) D (chunk 9) := by
  native_decide

end HM
