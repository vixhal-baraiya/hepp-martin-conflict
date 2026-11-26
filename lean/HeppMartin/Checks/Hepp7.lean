import HeppCompute

/-! Native evaluation (`native_decide`): the Hepp tables of both graphs agree modulo the
primes in `chunk 7`. -/

namespace HM

theorem hepp_chunk_7 :
    heppMods (decomplete Ga 0) D (chunk 7) = heppMods (decomplete Gb 0) D (chunk 7) := by
  native_decide

end HM
