"""census_docs.py -- read census numbers from the MARKDOWN, never from a constant.

## The defect this fixes

Both census guards compared the tree against a hardcoded `EXPECTED` dict, and both documents said
different numbers:

    check_repair_census   EXPECTED 11/37, 18/47, 57/250   REPAIR-CENSUS.md said 9/28, 22/56, 54/239
    check_refutation_census  EXPECTED 285, Geo 6          REFUTATION-CENSUS.md said 284, Geo 5

Both exited 0. So the documents had drifted and the guards were green -- the same shape as round 57's
"a guard that checks the empty set": the guard measures one thing, the document says another, and
nothing compares them.

## Why one parser instead of one checker

A third script that re-parsed both documents would duplicate the parsing, and the duplication would
drift exactly the way the numbers did. Instead this module holds THE parser, and each guard calls it.
The markdown becomes the single source of truth; the guard's job is to prove the markdown still
matches the tree.

## A parse failure is an ERROR, never a pass

If a table is renamed or a row deleted, that must fail loudly. A guard that silently degrades to
"nothing to compare" is how this defect happened in the first place -- the same reason
`check_usage_claims` was wrong to print `(absent) ... report-only`.
"""
import io
import re


class CensusDocError(Exception):
    """The document does not contain the numbers the census is supposed to record."""


def _cells(line):
    """Split a markdown table row into stripped cells, dropping the empty ends."""
    return [c.strip() for c in line.strip().strip("|").split("|")]


def _num(cell):
    """Parse a table cell holding a number, tolerating bold and thousands separators."""
    s = cell.replace("*", "").replace(",", "").strip()
    if not s.isdigit():
        raise CensusDocError("cell %r is not a number" % cell)
    return int(s)


def _rows(text):
    return [ln for ln in text.split("\n") if ln.strip().startswith("|")]


# --------------------------------------------------------------------- repair census

#: The three classes, keyed by the letter that starts the first cell.
REPAIR_CLASSES = {"A": ("A_files", "A_decls"),
                  "B": ("B_files", "B_decls"),
                  "C": ("C_files", "C_decls")}


def repair_expected(path):
    """`{A_files, A_decls, B_files, B_decls, C_files, C_decls}` from REPAIR-CENSUS.md.

    The table's shape is

        | 类 | 判据 | 文件数 | fix 命名声明数（按文件计） |
        | **A. ...** | ... | **9** | **28** |

    so the class letter is in cell 0 and the two counts are cells 2 and 3.
    """
    text = io.open(path, encoding="utf-8").read()
    out = {}
    for ln in _rows(text):
        cells = _cells(ln)
        if len(cells) < 4:
            continue
        head = cells[0].replace("*", "").strip()
        for letter, (fk, dk) in REPAIR_CLASSES.items():
            if head.startswith(letter + ".") or head.startswith(letter + " "):
                if fk in out:
                    raise CensusDocError("class %s appears twice" % letter)
                out[fk] = _num(cells[2])
                out[dk] = _num(cells[3])
                break
    missing = [k for pair in REPAIR_CLASSES.values() for k in pair if k not in out]
    if missing:
        raise CensusDocError("REPAIR-CENSUS.md is missing %s" % ", ".join(missing))
    return out


# --------------------------------------------------------------------- refutation census

#: The layers the refutation census reports separately.
# Round 238: Runtime is a real layer now; leaving it out would make the per-layer rows
# silently fail to add up to the total, which is the drift this parser exists to catch.
REFUTATION_LAYERS = ("Lib", "Lift", "Runtime", "Domains", "Evidence", "Core", "Geo", "Compose")

#: `**284 条**否定结论` -- the total in the prose above the layer table.
TOTAL = re.compile(r"\*\*(\d+)\s*条\*\*\s*否定结论")


def refutation_expected(path):
    """`(total, {layer: count})` from REFUTATION-CENSUS.md.

    Both sources are required: the prose total AND the per-layer table. Requiring both is
    deliberate -- the two had drifted INDEPENDENTLY (total 284 vs 285, Geo 5 vs 6), so a check that
    read only one of them would have missed half the drift.
    """
    text = io.open(path, encoding="utf-8").read()
    m = TOTAL.search(text)
    if not m:
        raise CensusDocError("REFUTATION-CENSUS.md has no `**N 条**否定结论` total")
    total = int(m.group(1))
    layers = {}
    for ln in _rows(text):
        cells = _cells(ln)
        if len(cells) < 2:
            continue
        name = cells[0].replace("`", "").replace("*", "").strip()
        if name in REFUTATION_LAYERS and name not in layers:
            layers[name] = _num(cells[1])
    missing = [l for l in REFUTATION_LAYERS if l not in layers]
    if missing:
        raise CensusDocError("REFUTATION-CENSUS.md layer table is missing %s" % ", ".join(missing))
    return total, layers
