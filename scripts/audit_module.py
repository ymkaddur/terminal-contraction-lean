"""Build one module and check the exact set of named theorem axiom reports."""
import re
from pathlib import Path
import subprocess
import sys
import tempfile


def main(module):
    if not re.fullmatch(r"\w+(?:\.\w+)*",module):
        raise ValueError("Use a Lean module name")
    source=Path(*module.split(".")).with_suffix(".lean").read_text(encoding="utf-8-sig")
    ns=re.search(r"^namespace ([\w.]+)$",source,re.M)[1]
    expected={ns+"."+n for n in re.findall(r"^theorem ([\w'.]+)",source,re.M)}
    if not expected:
        raise ValueError("No named theorems")
    subprocess.run(["lake","--wfail","build","+"+module],check=True)
    with tempfile.TemporaryDirectory(dir=".lake") as temp:
        path=Path(temp)/"Audit.lean"
        path.write_text("import "+module+"\n"+"".join("#print axioms "+n+"\n" for n in sorted(expected)),encoding="utf8")
        out=subprocess.check_output(["lake","env","lean","-DwarningAsError=true",str(path)],text=True)
    reports=re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",out)
    if len(reports)!=len(expected) or {n for n,_ in reports}!=expected:
        raise ValueError("Missing or extra axiom report")
    for name,axioms in reports:
        if {s.strip() for s in axioms.split(",") if s.strip()}-{"propext","Quot.sound","Classical.choice"}:
            raise ValueError(name+" depends on additional axioms")
    print(out,end="")


if __name__=="__main__":
    main(sys.argv[1])
