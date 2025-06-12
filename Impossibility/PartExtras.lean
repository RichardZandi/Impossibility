import Mathlib.Data.Part

namespace Part

/-- Same `getD` we used before. -/
noncomputable def getD {α} (p : Part α) (d : α) : α := by
  by_cases h : p.Dom
  · exact p.get h
  · exact d

@[simp] lemma eval_none_dom {α} : (Part.none : Part α).Dom = False := by
  simp

end Part
