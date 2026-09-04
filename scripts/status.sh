#!/usr/bin/env bash
# Live status: open sorries per file, and subagent runs. Usage: scripts/status.sh
cd "$(dirname "$0")/.."
echo "== Open sorries (excluding scratch/bridge-variant files)"
for f in Erdos289/*.lean; do
  case "$f" in *ZZScratch*|*Scratch*) continue;; esac
  n=$(grep -cE '^\s*sorry\b|:= by sorry\b|\bsorry --' "$f")
  [ "$n" -gt 0 ] && printf "  %-38s %s\n" "$f" "$n"
done
echo "== Axioms declared"
grep -n '^axiom' Erdos289/*.lean | sed 's/^/  /'
echo "== Subagent runs (.agents/*.log)"
for f in .agents/*.log; do
  n=$(basename "$f" .log); m=$(grep -oE 'model [a-z0-9.-]+' .agents/run*.sh | head -0)
  st=$(grep -o '^EXIT=.*' "$f" || echo running)
  printf "  %-14s %s\n" "$n" "$st"
done
