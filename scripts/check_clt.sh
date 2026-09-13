#!/usr/bin/env bash
# Build Erdos289CLT, report remaining sorries per file, and print the axioms of the final theorem.
set -u
cd "$(dirname "$0")/.."
lake build Erdos289CLT 2>&1 | grep -E "^error|Build completed|sorry" | sort | uniq -c | sort -rn | head -40
echo "--- sorry occurrences per file (source grep) ---"
grep -c "sorry" Erdos289CLT/*.lean | grep -v ":0$" || echo "none"
echo "--- axioms ---"
cat > /tmp/clt_axioms.lean <<'EOL'
import Erdos289CLT
#print axioms Erdos289.CLT.main_theorem
#print axioms Erdos289.CLT.statement234
EOL
lake env lean /tmp/clt_axioms.lean
