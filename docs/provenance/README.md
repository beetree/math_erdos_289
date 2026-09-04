# Provenance records for the vendored proofs

These are the port records that were previously kept outside the repository, included here so
that the repository is self-contained. They are historical working records: they refer to the
standalone port directories (`expert_input/ported/<Dir>`), to local paths on the porting
machine, and to files (`Erdos289Bridge.lean`, `Axioms.lean`) that were merged into
`Erdos289/CFPBridge.lean`, `SolveMath/Ported/*.lean` and `Erdos289/Main.lean` on integration.
The current summaries are `SolveMath/PROVENANCE.md` and `ErdosProblems/PROVENANCE.md`.

- `PORT_README.md`: overview of the four ports and how they were minimized.
- `<Dir>/PROVENANCE.md`: per-port source commit, upstream authorship, license status, and edits.
  `ErdosTuranFinite/` records a port that is **not used** by the terminal theorem and is not
  vendored (the signed-fiber construction removed the Erdős–Turán input).
- `CFP/PORT_LOG_cfp_w1a.md`: the one proof edit for the Mathlib v4.33 → v4.34.0-rc2 drift.
- `CFP/kept_modules.txt`, `CFP/dropped_modules.txt`, `CFP/closure_modules.txt`,
  `CFP/closure_decl_ranges.txt`: the proof-term walk data cited by `ErdosProblems/PRUNING_NOTES.md`.
- `ls_kept_modules.txt`, `ls_solution_decl_ranges.txt`, `mer_kept_modules.txt`: the
  minimization data for the Liu–Sawhney and Mertens ports.
- `build.sh`: the standalone build script used for the ports before integration (historical; in
  this repository the libraries build with `lake build`).

The upstream reference snapshot itself (`plby/lean-proofs`, commit `61fce10e`) is not included;
a byte-for-byte comparison against it requires that snapshot.
