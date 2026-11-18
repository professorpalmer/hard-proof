"""Write steps 12 and 13 of the lab page from the stored results, and add the repository and PDF links.

Run: python3 update_page.py --site PATH_TO_SITE_CHECKOUT
The other steps of the page are edited by hand. This script replaces only the two sections and the link row.
"""
from __future__ import annotations

import argparse
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
REPO_URL = "https://github.com/professorpalmer/hard-proof"


def step12(pc: dict, review: dict) -> str:
    n = pc["bugs"]
    arms = pc["arms"]
    label = {"shell/opus": "Review: Opus 5.5, with a shell", "shell/sonnet": "Review: Sonnet 5.5, with a shell", "plain/sonnet": "Review: Sonnet 5.5, read only"}
    rows = "".join(f"<tr><td>{label[k]}</td><td>{v['detected']} of {n}</td><td>${review[k + '/pre']:.0f}</td></tr>"
                   for k, v in sorted(arms.items(), key=lambda kv: -kv[1]["detected"]))
    best = max(arms.values(), key=lambda v: v["detected"])
    missed = n - pc["any_review_arm"]
    only = len(pc["proof_only_titles"])
    first_two = sum(v for k, v in pc["detected_at_step"].items() if int(k) <= 2)
    return f"""<section>
<span class="step">12 · Real bugs</span>
<h2>{n} real bugs from our own history. A pointed review found less than half. The proof pipeline found {only} that no review found.</h2>
<p>Agents mined the history of Puppetmaster and Marionette for logic faults in small functions. A bug is in the data set only when a runnable repro gives different results before and after its fix. A reviewer agent then got the source before the fix and the name of the function.</p>
<p>The proof pipeline got the same bugs. One agent writes a Lean mirror of the function. A second agent writes laws from the documentation, with no view of the code. A prover and an adversary then give certificates: a conflict between the code and a law, a gap in the laws, or a completeness proof.</p>
<div class="scroll"><table>
<thead><tr><th>Method</th><th>Bugs detected</th><th>Cost</th></tr></thead>
<tbody>
{rows}
<tr><td>Proof pipeline</td><td>{pc['proof_detected']} of {n}</td><td>${pc['cost_usd']:.0f}</td></tr>
<tr><td>Best review arm or the proof pipeline</td><td>{best['union_with_proof']} of {n}</td><td></td></tr>
<tr><td>Any review arm or the proof pipeline</td><td>{pc['union_all']} of {n}</td><td></td></tr>
</tbody></table></div>
<p>The proof pipeline does not replace a review. It found fewer bugs, for about {pc['cost_usd'] / review[max(arms, key=lambda k: arms[k]['detected']) + '/pre']:.0f} times the cost of the best review arm. But the two methods miss different bugs. The three review arms together missed {missed} bugs, and the pipeline found {only} of those.</p>
<p>An agent wrote a correct mirror for {pc['model']['link_agrees_before_the_fix']} of {n} functions: each agrees with the real function on 5,000 random cases. When the pipeline found the bug, it was early: {first_two} of {pc['proof_detected']} detections came in the first two steps. A mirror of the code cannot show what the code does not have. The pipeline found {pc['proof_detected_in_scope']} of the {pc['in_scope']} bugs that the mirror can express, and none of the others.</p>
<p class="note">The pipeline also showed {pc['items_not_the_bug']} conflicts and gap questions that are not the known bug. In real use the owner answers each one, so the number of questions is a cost. The paper has the outcome of each bug, the limits, and a fault of our harness in this run.</p>
</section>"""


def step13(ls: dict, proof: dict) -> str:
    o = ls["owner_step"]
    sh = o["shipped"]
    s2 = ls["second_review_by_sessions"]
    ok = sum(v["ok_to_merge"] for v in s2.values())
    rev = sum(v["reverted"] for v in s2.values())
    hp = ls["hpflow_first_live_run"]
    link = proof["raw"]["link"]
    q = proof["raw"]["question"]["question"]
    kernels = len(proof["raw"]["complete"]["results"][0]["kernels"]["accepted"])
    return f"""<section>
<span class="step">13 · From findings to fixes</span>
<h2>The review findings went up a ladder of evidence. {ls['distinct_confirmed_bugs']} real bugs came out, and {o['fixes_shipped']} fixes shipped.</h2>
<p>The reviews of step 12 also made many findings that are not a known bug. A finding is only a claim. So each one had to pass these steps, on the code of today:</p>
<div class="scroll"><table>
<thead><tr><th>Step</th><th>Evidence</th><th>Result</th></tr></thead>
<tbody>
<tr><td>1</td><td>A runnable repro gives the same result on the newest code</td><td>{ls['findings_live_on_newest_dev']} findings in {ls['functions']} functions</td></tr>
<tr><td>2</td><td>Two verifier agents on different models each say "real", and each names a caller that reaches it</td><td>{ls['both_real_reachable']} findings: {ls['distinct_confirmed_bugs']} distinct bugs in {ls['files']} files</td></tr>
<tr><td>3</td><td>A fix with a regression test, a script check and a judge agent</td><td>{ok + rev} fixes</td></tr>
<tr><td>4</td><td>A second, slower review of each fix, and the full test matrix in CI</td><td>{ok} fixes stand, {rev} reverted</td></tr>
<tr><td>5</td><td>The owner decides each rule that has no precise statement, then the merge and the release</td><td>{o['fixes_shipped']} fixes shipped</td></tr>
</tbody></table></div>
<p>The {ls['distinct_confirmed_bugs']} bugs were in two shipped products of ours, Puppetmaster and Marionette. We did not know of them before. The {rev} reverted fixes had each passed the script check and the judge. Each changed the result for inputs that the bug does not cover, in a rule with no precise statement of what it must do. They became {o['owner_questions']} questions for the owner. With the answers, {o['fixes_made_again_with_the_owner_rule']} fixes were made again and {o['accepted_with_no_code_change']} bug was accepted as it is.</p>
<p>The same steps run as one command set, <code>hpflow</code>. Its first run, on the functions that changed between two releases, found {hp['confirmed']} confirmed bugs in {hp['targets']} functions, and its {hp['fixes_after_second_review']} fixes shipped too. The fixes are in {" and ".join(f"{r[0].upper() + r[1:]} {v['release'].lstrip('v')} ({v['fixes']})" for r, v in sh.items())}.</p>
<h3>Then one rule got a proof</h3>
<p>One of the reverted fixes was in the rule that decides if a request starts a swarm of workers. After the owner's answer, that rule is one function with {proof['inputs']} boolean inputs. We wrote {len(proof['laws'])} laws from the order that the owner approved. {kernels} kernels accepted a proof that the shipped function passes each law, and a proof that the laws leave no input open. A link test compared the Lean mirror with the shipped function on {link['cases']:,} cases, with {link['differences']} differences. This took about ten minutes.</p>
<p>The docstring of that function was a second test. With the docstring as the only source, the adversary proved a gap: for the input <code>{q['input']['shown']}</code>, one design gives "{q['design_a']['shown']}" and a second design gives "{q['design_b']['shown']}". The code was correct, and its documentation did not state the rule. It does now.</p>
<p class="note">Steps 1 to 4 have no Lean proof. A test shows one input, and a law says what must hold for each input. The runs of this step also showed a real fault in Puppetmaster (a helper process that stayed alive after a timeout), which is corrected in version 1.51.1.</p>
</section>"""


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--site", type=Path, required=True)
    parser.add_argument("--no-repo-link", action="store_true")
    args = parser.parse_args()
    page_path = args.site.expanduser() / "dist" / "labs" / "hard-proof" / "index.html"
    page = page_path.read_text(encoding="utf-8")
    pc = json.loads((ROOT / "v2" / "retro_compare.json").read_text())
    ls = json.loads((ROOT / "v2" / "ladder_summary.json").read_text())
    proof = json.loads((ROOT / "v3" / "summary.json").read_text())

    def swap(marker: str, text: str) -> None:
        nonlocal page
        found = re.search(r'<section>\s*<span class="step">' + re.escape(marker) + r".*?</section>", page, flags=re.S)
        if not found:
            raise SystemExit(f"section not found: {marker}")
        page = page[:found.start()] + text + page[found.end():]

    swap("12 · Real bugs", step12(pc, pc["review_cost_usd"]))
    swap("13 · From findings to fixes", step13(ls, proof))
    if not args.no_repo_link and REPO_URL not in page:
        old = '<a class="button ghost" href="/labs/data/hard-proof.json">Data</a>'
        if old not in page:
            raise SystemExit("link row not found")
        page = page.replace(old, f'<a class="button ghost" href="/labs/hard-proof/paper.pdf">Paper (PDF)</a><a class="button ghost" href="{REPO_URL}">Code on GitHub</a>' + old)
        page = page.replace('<a href="/labs/hard-proof/paper/">read the paper</a></p>',
                            f'<a href="/labs/hard-proof/paper/">read the paper</a> · <a href="/labs/hard-proof/paper.pdf">PDF</a> · <a href="{REPO_URL}">code</a></p>')
    page_path.write_text(page, encoding="utf-8")
    print("page written", page_path)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
