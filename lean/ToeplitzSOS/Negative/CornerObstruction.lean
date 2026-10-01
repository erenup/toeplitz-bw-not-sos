import ToeplitzSOS.Negative.TangentApplication
import ToeplitzSOS.Negative.Analytic.Interface

/-! # Unconditional obstruction to the full algebraic corner interface -/

namespace ToeplitzSOS.Negative

/-- The full algebraic corner Gram cannot exist at the selected finite depth.
All analytic inputs are discharged by the concrete analytic stack. -/
theorem cornerGram_impossible : ¬ Nonempty (CornerGram cornerDepth) :=
  no_cornerGram Analytic.analyticInputs

end ToeplitzSOS.Negative
