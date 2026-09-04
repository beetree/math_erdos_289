import Erdos289.AssemblyS2
import Erdos289.Target

/-!
# The terminal theorem

`Erdos289.candidateStatement` has exactly the type `Erdos289.CandidateStatement` from the
audited file `Erdos289/Intervals.lean`. Run `scripts/Axioms.lean` to see its axiom report.
-/

namespace Erdos289

/-- **Erdős Problem 289**, nonadjacent strengthened form (the audited `CandidateStatement`),
proved via the signed-fiber construction (`AssemblyS2`), with no literature axiom. -/
theorem candidateStatement : CandidateStatement :=
  candidateStatement_of erdos289S2

end Erdos289

-- The axiom report of the terminal theorem is printed on every build.
#print axioms Erdos289.candidateStatement
