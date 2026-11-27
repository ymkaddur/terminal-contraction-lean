#!/usr/bin/env bash
# Audit every Lean file of this repository:
#   * it compiles with no errors and no warnings;
#   * no declaration uses `sorry`;
#   * every theorem depends only on propext, Classical.choice and Quot.sound.
# Usage:  lake exe cache get && scripts/audit.sh          (runs `lake env lean`)
#         LEAN_CMD=/path/to/lean-wrapper scripts/audit.sh  (any command that compiles one file)
set -uo pipefail
cd "$(dirname "$0")/.."
read -r -a LEAN <<< "${LEAN_CMD:-lake env lean}"
mkdir -p .lake/audit
FAIL=0
while IFS= read -r f; do
  NS="$(grep -m1 -oE '^namespace [A-Za-z0-9_.]+' "$f" | cut -d' ' -f2)"
  T=".lake/audit/$(basename "$f" .lean)_audit.lean"
  { cat "$f"; echo; grep -oE '^theorem [^ :]+' "$f" | awk -v ns="$NS" '{print "#print axioms " ns "." $2}'; } > "$T"
  # Lean wraps long axiom lists over several lines: join them before matching.
  OUT="$("${LEAN[@]}" "$T" < /dev/null 2>&1 | sed -e ':a' -e 'N' -e '$!ba' -e 's/,\n */, /g')"
  if grep -qE '(^|: )(error|warning)' <<<"$OUT"; then
    echo "FAIL   $f"; grep -E 'error|warning' <<<"$OUT" | head -20; FAIL=1; continue
  fi
  BAD="$(grep -E 'depends on axioms' <<<"$OUT" | grep -vE 'depends on axioms: \[((propext|Classical\.choice|Quot\.sound)(, )?)*\]$')"
  N="$(grep -cE 'depends on axioms|does not depend on any axioms' <<<"$OUT")"
  if [ -n "$BAD" ] || grep -q sorryAx <<<"$OUT"; then echo "AXIOMS $f"; echo "$BAD"; FAIL=1
  else echo "OK     $f  ($N theorems: 0 sorry, 0 warnings, axioms within propext/Classical.choice/Quot.sound)"; fi
done < <(find . -name '*.lean' -not -path './.lake/*' | sort)
exit $FAIL
