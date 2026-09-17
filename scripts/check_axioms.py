"""Fail unless every advertised theorem has an allowed transitive axiom report."""

import re
import sys
from pathlib import Path

expected = {
    "PowerfulPairs.jsp_000301",
    "PowerfulPairs.bounded_multiplicative_gaps",
    "PowerfulPairs.value_geometric_upper",
    "PowerfulPairs.count_at_geometric_cutoff",
    "PowerfulPairs.explicit_gap_bound",
    "PowerfulPairs.infinitely_many_pairs",
}
allowed = {"propext", "Classical.choice", "Quot.sound"}
log = Path(sys.argv[1]).read_text()
seen = set()
for name, raw in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", log):
    axioms = {item.strip() for item in raw.split(",") if item.strip()}
    if axioms - allowed:
        raise SystemExit(f"Rejected axioms for {name}: {sorted(axioms - allowed)}")
    seen.add(name)
seen.update(re.findall(r"'([^']+)' does not depend on any axioms", log))
if missing := expected - seen:
    raise SystemExit(f"Missing reports: {sorted(missing)}")
print(f"PASS: all {len(expected)} theorem reports use only allowed axioms.")
