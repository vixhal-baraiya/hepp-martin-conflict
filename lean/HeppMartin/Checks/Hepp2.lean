import HeppCompute

/-! Native evaluation (`native_decide`): the Hepp tables of both graphs agree modulo the
primes in `chunk 2`. -/

namespace HM

theorem hepp_chunk_2 :
    heppMods (decomplete Ga 0) D (chunk 2) = heppMods (decomplete Gb 0) D (chunk 2) := by
  native_decide

end HM
