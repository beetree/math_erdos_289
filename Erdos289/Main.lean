import Erdos289.AssemblyS2
import Erdos289.Target

/-!
# The terminal theorem

`Erdos289.candidateStatement` has exactly the type `Erdos289.CandidateStatement` from the
audited file `Erdos289/Intervals.lean`. Its axiom report is printed by the `#print axioms`
command at the end of this file on every build; to re-run it standalone after `lake build`,
use `lake env lean Erdos289/Main.lean`, or a check file containing
`import Erdos289.Main`, `#check (Erdos289.candidateStatement : Erdos289.CandidateStatement)`
and `#print axioms Erdos289.candidateStatement`.
-/

namespace Erdos289

/-- **Erdős Problem 289**, nonadjacent strengthened form (the audited `CandidateStatement`),
proved via the signed-fiber construction (`AssemblyS2`), with no literature axiom. -/
theorem candidateStatement : CandidateStatement :=
  candidateStatement_of erdos289S2

end Erdos289

-- The axiom report of the terminal theorem is printed on every build.
#print axioms Erdos289.candidateStatement
