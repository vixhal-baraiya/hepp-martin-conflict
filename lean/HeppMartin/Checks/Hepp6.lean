import HeppCompute

/-! Native evaluation (`native_decide`): the Hepp tables of both graphs agree modulo the
primes in `chunk 6`. -/

namespace HM

theorem hepp_chunk_6 :
    heppMods (decomplete Ga 0) D (chunk 6) = heppMods (decomplete Gb 0) D (chunk 6) := by
  native_decide

end HM
