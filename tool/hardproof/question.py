"""The question for the human: the witness input and the outputs."""
from __future__ import annotations

from hardproof import lean
from hardproof.checks import check_certificate
from hardproof.domain import Domain

RUNNERS = {"gap": "QuestionGap.lean", "conflict": "QuestionConflict.lean"}


def parse(out: str) -> dict:
    values = {}
    for line in out.splitlines():
        if "\t" in line:
            key, value = line.split("\t", 1)
            values[key] = value
    return values


def question(domain: Domain, kinds: list, paranoid: bool) -> dict:
    report = {"command": "question", "verdict": "reject", "results": []}
    for kind in kinds:
        res = check_certificate(domain, kind, paranoid)
        report["results"].append({k: res[k] for k in ("kind", "verdict", "stage", "problems")})
        if res["verdict"] != "accept":
            continue
        # The runner imports the model. A fresh folder that ran only a gap check has no build of it.
        rc, out, err = lean.run(["lake", "build", "HPModel"], domain.gen)
        if rc != 0:
            report["results"][-1]["problems"] = ["Types, Ref or Codec does not build"]
            report["results"][-1]["output"] = lean.clean(out + err)
            continue
        rc, out, err = lean.run(["lake", "env", "lean", "--run", RUNNERS[kind]], domain.gen)
        if rc != 0:
            report["results"][-1]["problems"] = ["the question runner failed (is a design noncomputable?)"]
            report["results"][-1]["output"] = lean.clean(out + err)
            continue
        v = parse(out)
        q = {"kind": kind, "input": {"encoded": v.get("input_encoded"), "shown": v.get("input_shown")},
             "ref": {"encoded": v.get("ref_encoded"), "shown": v.get("ref_shown")}}
        if kind == "gap":
            q["design_a"] = {"encoded": v.get("a_encoded"), "shown": v.get("a_shown")}
            q["design_b"] = {"encoded": v.get("b_encoded"), "shown": v.get("b_shown")}
            q["ask"] = ("The two designs pass each law and differ on this input. "
                        "Which output is right? The output of ref is the shipped behavior.")
        else:
            q["law"] = res.get("law")
            q["ask"] = (f"The shipped code (ref) breaks the law {res.get('law')} on this input. "
                        "Is the law wrong, or is the code wrong?")
        report.update(verdict="accept", question=q)
        return report
    return report
