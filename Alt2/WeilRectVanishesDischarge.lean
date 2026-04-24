import Mathlib
import RequestProject.WeilContour
import RequestProject.WeilFinalAssembly

set_option maxHeartbeats 400000

/-!
# `rectangleVanishes_target` — conditional discharge at `σL = -1`, `σR = 2`
-/

noncomputable section

open Complex MeasureTheory

namespace ZD
namespace WeilPositivity
namespace FinalAssembly

-- Edge targets (`topEdgeVanishes_target`, `bottomEdgeVanishes_target`,
-- `vertEdgeDiffVanishes_target`) and the conditional glue
-- `rectangleVanishes_of_edges` now live in `WeilFinalAssembly.lean`.

/-- **Conditional discharge of `rectangleVanishes_target β`** at `σL = -1`,
`σR = 2` — alias for `rectangleVanishes_of_edges`. -/
theorem rectangleVanishes_target_holds_neg_one_two
    (β : ℝ) (hβ : β ∈ Set.Ioo (0:ℝ) 1)
    (h_top    : topEdgeVanishes_target β (-1) 2)
    (h_bottom : bottomEdgeVanishes_target β (-1) 2)
    (h_vert_cancel : vertEdgeDiffVanishes_target β (-1) 2) :
    rectangleVanishes_target β :=
  rectangleVanishes_of_edges β hβ h_top h_bottom h_vert_cancel

#print axioms rectangleVanishes_target_holds_neg_one_two

end FinalAssembly
end WeilPositivity
end ZD

end
