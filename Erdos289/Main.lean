import Erdos289.Assembly
import Erdos289.Target

/-!
# The terminal theorem

`Erdos289.candidateStatement` has exactly the type `Erdos289.CandidateStatement` from the
audited file `Erdos289/Intervals.lean`. Run `scripts/Axioms.lean` to see its axiom report.
-/

namespace Erdos289

/-- **Erdős Problem 289**, nonadjacent strengthened form (the audited `CandidateStatement`),
conditional on the external inputs recorded as axioms. -/
theorem candidateStatement : CandidateStatement :=
  candidateStatement_of erdos289

end Erdos289

-- The axiom report of the terminal theorem is printed on every build.
#print axioms Erdos289.candidateStatement
