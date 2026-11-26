import HeppCompute

/-! Native evaluation (`native_decide`): the Hepp tables of both graphs agree modulo the
primes in `chunk 8`. -/

namespace HM

theorem hepp_chunk_8 :
    heppMods (decomplete Ga 0) D (chunk 8) = heppMods (decomplete Gb 0) D (chunk 8) := by
  native_decide

end HM
