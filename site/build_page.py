#!/usr/bin/env python3
"""Hard Proof: write the study page of puppetmaster.gg from the data files.

The page states the result of the study first: the audit ladder with its release gate, then the evidence, the
cost, the place of a proof, and what did not work. The paper has the record in the order of the work.

One source for each number. Each count, cost and rate comes from a data file of the study, and `sources()`
lists the file for each result on the page. The four constants below are the exception. Run `build_site.py` first: it writes the
public data file that this script reads for the first study.

Usage:
    python3 build_site.py --site ~/Projects/puppetmaster-gg-hardproof
    python3 build_page.py --site ~/Projects/puppetmaster-gg-hardproof
"""
from __future__ import annotations

import argparse
import html
import json
import re
import shutil
from datetime import date
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
# The public repository has the study folders below `study`.
STUDY = ROOT / "study" if (ROOT / "study").is_dir() else ROOT
REPO_URL = "https://github.com/professorpalmer/hard-proof"
PAGE_URL = "https://puppetmaster.gg/labs/hard-proof/"
PAPER = "/labs/hard-proof/paper/"

# Measured values that no data file of the study holds. Each one is in the text of the paper, Section 14.
START_TOKENS_USER_PROFILE = 83_000      # the start text of a worker session with the settings of the user
FIRST_REQUEST_ALL_TOOLS = 33_500        # the first request of a lean worker with all tools of Claude Code
FIRST_REQUEST_SIX_TOOLS = 8_800         # the same request with the six tools of version 0.5
CI_FAILED_WORKERS = 12                  # the workers that failed in the first CI audit job, which passed


def load(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def esc(text: object) -> str:
    return html.escape(str(text), quote=True)


def money(value: float) -> str:
    return f"${value:,.2f}"


def whole(value: float) -> str:
    return f"${value:,.0f}"


def facts(site: Path) -> dict:
    """Each number of the page, from the data files."""
    v2 = STUDY / "v2"
    study = load(site / "dist" / "labs" / "data" / "hard-proof.json")
    ls, pc, tri = load(v2 / "ladder_summary.json"), load(v2 / "retro_compare.json"), load(v2 / "conflict_triage.json")
    gate, cut, rel = load(v2 / "gate_live.json"), load(v2 / "cost_cut.json")["runs"], load(v2 / "release_050.json")
    table = load(STUDY / "v3" / "summary.json")
    live = load(v2 / "import_live.json")
    tool_version = re.search(r'^version = "([^"]+)"', (ROOT / "tool" / "pyproject.toml").read_text(encoding="utf-8"), flags=re.M)
    first, grouped, lean = cut
    now = rel["same_range"][1:]
    known = {k["arm"]: k for k in rel["known_bugs"]}
    releases = gate["release_runs"]
    stopped = [r for r in releases if r["confirmed_bugs"]]
    second = ls["second_review_by_sessions"].values()
    blind = [r for r in study["scale_test"] if r["set"] == "blind"]
    loops = [r["review_loop"] for r in study["loop_tests"]["rows"] if "review_loop" in r]
    h2h = rel["head_to_head"]
    return {
        "generated": date.fromisoformat(study["generated"]),
        "version": rel["version"], "tool_version": tool_version.group(1) if tool_version else rel["version"],
        # The findings of another reviewer as input: the run with the brief of the release.
        "imp": live["runs"][-1], "imp_blind": live["blind_judge"],
        # The ladder.
        "functions": ls["functions"], "findings": ls["findings_live_on_newest_dev"], "passed": ls["both_real_reachable"],
        "bugs": ls["distinct_confirmed_bugs"], "files": ls["files"],
        "reverted": sum(s["reverted"] for s in second), "stood": sum(s["ok_to_merge"] for s in second),
        "shipped": ls["owner_step"]["fixes_shipped"],
        # The gate before each release.
        "releases": releases, "stopped": stopped, "stopped_bugs": sum(r["confirmed_bugs"] for r in stopped),
        # One range, three tools.
        "h2h": h2h, "h2h_ratio": h2h["runs"]["hpf"]["cost_usd_api_equivalent"] / h2h["runs"]["claude"]["cost_usd_api_equivalent"],
        # The known bugs.
        "known_n": pc["bugs"], "review_opus": pc["arms"]["shell/opus"]["detected"], "review_sonnet": pc["arms"]["shell/sonnet"]["detected"],
        "review_plain": pc["arms"]["plain/sonnet"]["detected"], "proof_detected": pc["proof_detected"],
        "review_opus_cost": pc["review_cost_usd"]["shell/opus/pre"], "review_sonnet_cost": pc["review_cost_usd"]["shell/sonnet/pre"],
        "review_plain_cost": pc["review_cost_usd"]["plain/sonnet/pre"], "proof_cost": pc["cost_usd"],
        "proof_only": len(pc["proof_only_vs_all_review"]), "proof_cost_one": pc["cost_mean_usd"],
        "conflicts": tri["collect"]["candidates"], "misread": tri["verdicts"]["agreed"]["misread"], "conflicts_real": tri["any_verdict_real"],
        # The cost.
        "cost_first": first["cost_usd"], "cost_lean": lean["cost_usd"], "bugs_first": first["confirmed_bugs"],
        "cost_grouped": grouped["cost_usd"], "bugs_grouped": grouped["confirmed_bugs"],
        "cost_now": sum(r["cost_usd"] for r in now) / len(now), "wall_now": sum(r["wall_seconds"] for r in now) / len(now),
        "runs_now": len(now), "targets": now[0]["targets"],
        "old48": known["lean"]["first_48"], "new48": known["direct_final"]["first_48"],
        "haiku": known["haiku"], "low": known["effort_low"], "one_pass": known["direct_final"], "two": rel["two_passes"],
        # The tool on its own release.
        "self": rel["self_audit"],
        # The first study: proofs.
        "adv": study["summary"]["all_adversary_runs"],
        "blind_ok": sum(1 for r in blind if r["correct"]), "blind_n": len(blind), "blind_laws": max(r["laws"] for r in blind),
        "dup": study["baseline_no_proof_duty"]["duplicate_entry_gap"],
        "loops_n": len(loops), "loops_early": sum(1 for r in loops if not r["end_state_complete"]),
        "link_events": study["link_tests"]["lock"]["events"], "link_differ": study["link_tests"]["lock"]["differ"],
        "table_laws": len(table["laws"]), "table_inputs": table["inputs"], "table_cases": table["input_cases"],
    }


def bar(value: float, top: float, kind: str = "") -> str:
    width = 0 if not top else max(0.0, min(100.0, 100 * value / top))
    cls = f' class="{kind}"' if kind else ""
    return f'<div class="hp-bar"><i{cls} style="width:{width:.1f}%"></i></div>'


def row(label: str, value: float, top: float, shown: str, sub: str = "", ours: bool = False) -> str:
    small = f"<small>{esc(sub)}</small>" if sub else ""
    return (f'<div class="hp-row{" is-ours" if ours else ""}"><span>{esc(label)}</span>{bar(value, top, "gold" if ours else "")}'
            f"<b>{esc(shown)}{small}</b></div>")


def hero(f: dict) -> str:
    arms = f["h2h"]["arms"]
    cut = 100 * (f["findings"] - f["passed"]) / f["findings"]
    when = f"{f['generated'].day} {f['generated']:%B %Y}"
    return f"""<p class="eyebrow"><a href="/labs/">LABS</a> · STUDY · HARD PROOF</p>
<p class="draft">Draft for review</p>
<h1>No repro, no bug. <em>No fix, no release.</em></h1>
<p class="lead">Hard Proof is a way to accept code that AI agents write, on evidence. A review finding counts only with a repro that a script runs. A release waits until each confirmed bug is closed.</p>
<p class="lead">We tested this on our own two products. This page has the result first. The paper has the record in the order of the work.</p>
<p class="byline">Puppetmaster Labs · {when} · hpflow {esc(f['tool_version'])} · <a href="{PAPER}">read the paper</a> · <a href="/labs/hard-proof/paper.pdf">PDF</a> · <a href="{REPO_URL}">code</a></p>
<div class="hp-stats">
<div class="hp-stat"><span>Confirmed bugs on one release range</span><strong class="accent">{arms['hpf']['confirmed_distinct_bugs']}</strong><em>Two AI review tools found {arms['claude']['confirmed_distinct_bugs']} each.</em></div>
<div class="hp-stat"><span>Review findings cut before you read them</span><strong>{cut:.0f}%</strong><em>{f['findings'] - f['passed']} of {f['findings']} findings did not pass two verifiers.</em></div>
<div class="hp-stat"><span>Releases stopped at the gate</span><strong>{len(f['stopped'])} of {len(f['releases'])}</strong><em>{f['stopped_bugs']} bugs in new code that an agent wrote.</em></div>
<div class="hp-stat"><span>Cost for one changed function</span><strong>{money(f['cost_now'] / f['targets'])}</strong><em>Review and two verifiers, API-equivalent.</em></div>
</div>"""


def use(f: dict) -> str:
    # The words "the same" are true only when the two sets of bugs are equal.
    hit = sum(1 for v in f["imp"]["bugs_of_the_blind_judge_found"].values() if v)
    blind = f["imp_blind"]["confirmed_distinct_bugs"]
    imp_tail = (f": the same {blind} that a blind judge confirmed." if hit == blind == f["imp"]["confirmed_distinct_bugs"]
                else f". A blind judge confirmed {blind} bugs among the same findings, and {hit} of them are in this result.")
    return f"""<section id="use">
<span class="step">1 · Use it</span>
<h2>Audit the change. Fix what is real. Gate the release.</h2>
<p><code>hpf</code> is a command line tool for Python code. It looks only at the functions that changed in a git range, so the cost follows the size of the change.</p>
<pre class="hp-code">pip install hpflow

hpf audit --repo . --ref HEAD --changed v1.2.3..HEAD --out ~/audits/next
hpf fix   --out ~/audits/next      <b># only when the report has confirmed bugs</b>
hpf gate  --out ~/audits/next --ref HEAD</pre>
<div class="hp-cmds">
<div class="hp-card"><span class="who">hpf audit</span><p>One reviewer agent reads each changed function. A finding counts only when its repro runs. Then two verifier agents on different models must each name a caller that reaches the fault.</p></div>
<div class="hp-card"><span class="who">hpf fix</span><p>An agent writes a fix and a test in a separate worktree. A script check and a judge agent must accept the fix. The tool does not commit: you review each fix.</p></div>
<div class="hp-card"><span class="who">hpf gate</span><p>This step makes no model call. Each confirmed bug must give a new result on the commit that you release, or have a waiver with a reason. If not, the gate fails.</p></div>
</div>
<p><strong>You have a review tool now?</strong> Keep it. <code>hpf audit --findings FILE</code> takes the findings of another review tool, or of a person. A worker must show each claim with a repro, and then the same verifiers and the same gate apply. In our test, the {f['imp_blind']['findings']} findings of two review tools became {f['imp']['claims']} claims. {f['imp']['shown_by_a_repro']} got a repro, and the verifiers confirmed {f['imp']['confirmed_distinct_bugs']} distinct bugs{imp_tail}</p>
<p class="note">The audit and the fix step need one agent tool with a login: Claude Code, Codex, or another tool through a command template. They need no other package. The gate needs git and Python only.</p>
<div class="hp-links"><a class="button" href="https://pypi.org/project/hpflow/">hpflow on PyPI</a><a class="button ghost" href="{REPO_URL}/blob/main/docs/USE.md">Guide in the repository</a><a class="button ghost" href="{PAPER}#use">The recommendation in the paper</a></div>
</section>"""


def ladder(f: dict) -> str:
    top = f["findings"]
    cut = 100 * (f["findings"] - f["passed"]) / f["findings"]
    rungs = [
        ("A finding with a repro", "The reviewer writes a small file that calls the function and returns the result. A script runs the file. A finding with no repro that runs is not a finding.",
         "Decided by a script", f["findings"], "findings with a repro that runs", f["findings"]),
        ("Two verifiers", "Two agents on different models read the code and its callers. Each one must say that the fault is real, and must name a caller that reaches it.",
         "Decided by two agents that must agree", f["passed"], f"findings passed ({cut:.0f} percent cut). They are {f['bugs']} distinct bugs", f["passed"]),
        ("A fix with a test", "An agent writes the fix and a new test. A script runs each repro again, the new test, and the tests that import the changed module. A judge agent reads the change.",
         "Decided by a script and one agent", f["bugs"], "fixes that the check and the judge accepted", f["bugs"]),
        ("A second review", "A second agent session reviews each fix, and runs the new test against the old code. The owner of the code decides each rule that has no exact statement.",
         "Decided by an agent, CI and the owner", f["stood"], f"fixes stood. {f['reverted']} were wrong and went to the owner for a rule", f["stood"]),
        ("The gate", "Each repro of each confirmed bug runs on the commit that you release. The same result as before means that the bug is open, and the release waits.",
         "Decided by a script, with no model call", len(f["stopped"]), f"of {len(f['releases'])} releases stopped", None),
    ]
    items = []
    for n, (name, rule, by, count, label, width) in enumerate(rungs, 1):
        items.append(f"""<li class="hp-rung"><span class="n">{n}</span><div><h3>{esc(name)}</h3><p>{esc(rule)}</p><p class="by">{esc(by)}</p></div>
<div class="count"><b>{count}</b>{esc(label)}{bar(width, top, "gold") if width is not None else ""}</div></li>""")
    return f"""<section id="ladder">
<span class="step">2 · The ladder</span>
<h2>Each step up needs harder evidence.</h2>
<p>An agent that reviews code gives many findings, and most of them are not bugs that a user can reach. The ladder is the filter. These counts are from the audit of {f['functions']} functions of our two products, Puppetmaster and Marionette.</p>
<ol class="hp-ladder">
{chr(10).join(items)}
</ol>
<p class="note">No step of this ladder is a proof. Each grade is the agreement of agents, a script, or CI. The owner of the code decides what is a bug. {f['shipped']} fixes from this ladder shipped in two releases.</p>
</section>"""


def evidence(f: dict) -> str:
    h, arms = f["h2h"], f["h2h"]["arms"]
    union = h["union_distinct_bugs"]
    names = (("hpf", "hpf audit"), ("claude", "Claude Code review"), ("codex", "Codex review"))
    tools = "".join(row(label, arms[a]["confirmed_distinct_bugs"], union, str(arms[a]["confirmed_distinct_bugs"]), ours=a == "hpf") for a, label in names)
    known = "".join([
        row("Review, Opus 5.5", f["review_opus"], f["known_n"], str(f["review_opus"]), whole(f["review_opus_cost"]), ours=True),
        row("Review, Sonnet 5.5", f["review_sonnet"], f["known_n"], str(f["review_sonnet"]), whole(f["review_sonnet_cost"]), ours=True),
        row("Review, no shell", f["review_plain"], f["known_n"], str(f["review_plain"]), whole(f["review_plain_cost"]), ours=True),
        row("Full proof pipeline", f["proof_detected"], f["known_n"], str(f["proof_detected"]), whole(f["proof_cost"])),
    ])
    blocks = "".join(f'<div class="hp-block{" is-stop" if r["confirmed_bugs"] else ""}"><i></i>{esc(r["release"].lstrip("v"))}</div>' for r in f["releases"])
    rounds = f["self"]["rounds"]
    top = max(r["confirmed_bugs"] for r in rounds)
    cols = "".join(f'<div class="hp-colbar"><b>{r["confirmed_bugs"]}</b><i style="height:{100 * r["confirmed_bugs"] / top:.0f}%"></i><span>round {r["round"]}</span></div>' for r in rounds)
    return f"""<section id="evidence">
<span class="step">3 · The evidence</span>
<h2>What the ladder found in code that we ship.</h2>
<div class="hp-tiles">
<div class="hp-tile">
<div class="big">{arms['hpf']['confirmed_distinct_bugs']}<small> against {arms['claude']['confirmed_distinct_bugs']} and {arms['codex']['confirmed_distinct_bugs']}</small></div>
<h3>One release range, three tools</h3>
<p>We gave one release range of Puppetmaster to three tools. The findings of the three went into one list with no tool name, and two verifier agents judged each one.</p>
<div class="hp-rows">{tools}</div>
<p class="note">{arms['hpf']['only_this_arm']} of the {union} confirmed bugs came from hpf only. Each other tool found one bug that hpf missed. Limits: one range and one run for each tool, and the models are not the same. hpf cost about {f['h2h_ratio']:.0f} times the Claude Code review.</p>
</div>
<div class="hp-tile">
<div class="big">{f['review_opus']}<small> of {f['known_n']}</small></div>
<h3>Known bugs from our own history</h3>
<p>We took {f['known_n']} real bugs from the history of the two products. A finding counts when its repro gives a different result before and after the real fix, so no agent is the judge.</p>
<div class="hp-rows">{known}</div>
<p class="note">The second number is the cost of the run on all {f['known_n']} bugs. One review pass leaves more than half of the known bugs. So a pass of the gate is not a proof that the code has no bug.</p>
</div>
<div class="hp-tile">
<div class="big">{len(f['stopped'])}<small> of {len(f['releases'])}</small></div>
<h3>Releases that the gate stopped</h3>
<p>The gate now runs before each release of the two products. It stopped two of them. The {f['stopped_bugs']} bugs were in new code that an agent wrote, and some were in our own fixes for earlier findings.</p>
<div class="hp-blocks">{blocks}</div>
<p class="note">Versions 1.5x are Puppetmaster, and versions 0.9.x are Marionette. Each release went out after the bugs were corrected and the gate passed.</p>
</div>
<div class="hp-tile">
<div class="big">{f['self']['confirmed_bugs']}</div>
<h3>Bugs that the tool found in its own release</h3>
<p>Before version {esc(f['version'])} we ran hpf on its own release range, and then on each set of fixes. The count went down slowly: a reviewer reads the whole function each time one of its lines changes.</p>
<div class="hp-cols">{cols}</div>
<p class="note">{len(rounds)} rounds for {money(f['self']['cost_usd'])}. The last round confirmed nothing. At the release, {f['self']['closed_by_repro']} bugs are closed by their repro and {f['self']['waived']} have a waiver.</p>
</div>
</div>
</section>"""


def cost(f: dict) -> str:
    each = f["cost_now"] / f["targets"]
    rows = "".join([
        row("First form of the tool", f["cost_first"], f["cost_first"], money(f["cost_first"])),
        row("Version 0.4: a lean worker", f["cost_lean"], f["cost_first"], money(f["cost_lean"])),
        row("Version 0.5: six tools", f["cost_now"], f["cost_first"], money(f["cost_now"]), ours=True),
    ])
    return f"""<section id="cost">
<span class="step">4 · The cost</span>
<h2>{money(each)} for each changed function.</h2>
<p>The audit of one release range of {f['targets']} functions costs {money(f['cost_now'])} and takes about {f['wall_now'] / 60:.0f} minutes. That is the mean of {f['runs_now']} runs, at the API-equivalent price.</p>
<div class="hp-rows">{rows}</div>
<p>Most of the first cost was not work. Each worker session started with about {START_TOKENS_USER_PROFILE:,} tokens of settings, rules and tool lists of the user of the machine, before it read one line of code. A lean worker does not load that text. Then a fixed list of six tools cut the first request of a worker from {FIRST_REQUEST_ALL_TOOLS:,} to {FIRST_REQUEST_SIX_TOOLS:,} tokens.</p>
<p>A lower price is no gain if the worker finds less. On {f['new48']['runs']} known bugs, the worker of version 0.5 detected {f['new48']['detected']} for {money(f['new48']['cost_usd'])}. The worker of version 0.4 detected {f['old48']['detected']} for {money(f['old48']['cost_usd'])}.</p>
<p class="note">For comparison: the full proof pipeline of this study cost {money(f['proof_cost_one'])} for one function.</p>
</section>"""


def proof(f: dict) -> str:
    adv, dup = f["adv"], f["dup"]
    return f"""<section id="hp-duel">
<span class="step">5 · Where a proof belongs</span>
<h2>A proof is the second tool, for a small rule that the owner states.</h2>
<p>The study started with a different plan: accept code from an agent only with a machine-checked proof. A proof gate shows that the code obeys its laws. It does not show that the laws say enough.</p>
<p>We proved three laws about a lock, and six proof kernels accepted the proofs. Then an adversary agent proved that the same three laws allow a lock that never unlocks.</p>
<div class="hp-duel">
<div class="hp-side"><span class="who">Design A</span><h3>The lock we proved</h3><p class="sub">release frees the lock</p><canvas id="hp-lock-a" width="200" height="210" aria-hidden="true"></canvas><p class="state" id="hp-state-a">Lock: free</p><p class="checks"><span>Law 1 ✓</span><span>Law 2 ✓</span><span>Law 3 ✓</span></p></div>
<div class="hp-side"><span class="who">Design B</span><h3>The lock the adversary wrote</h3><p class="sub">release does nothing</p><canvas id="hp-lock-b" width="200" height="210" aria-hidden="true"></canvas><p class="state" id="hp-state-b">Lock: free</p><p class="checks"><span>Law 1 ✓</span><span>Law 2 ✓</span><span>Law 3 ✓</span></p></div>
</div>
<div class="hp-trace" id="hp-trace" aria-label="The trace"><span>spawn 1</span><span>acquire 1</span><span>release 1</span></div>
<div class="hp-controls"><button class="hp-btn" id="hp-step" type="button">Next event</button><button class="hp-btn" id="hp-reset" type="button">Reset</button></div>
<p class="hp-verdict" id="hp-verdict">After the release, design B still holds the lock. Design B passes the same three laws. Lean checked the two designs and the trace.</p>
<p>We call this result a gap certificate: two designs, a proof that each one passes each law, and a proof that they differ. The owner answers one question for each gap, and the answer becomes a law. The loop stops when an agent proves that no gap is left.</p>
<ul class="hp-list">
<li>{adv['runs']} adversary runs gave {adv['gap_certificates_accepted']} gap certificates and {adv['completeness_proofs_accepted']} completeness proofs. {adv['no_accepted_result']} runs gave no accepted result.</li>
<li>In a blind test with generated rules, the adversaries gave the correct result in {f['blind_ok']} of {f['blind_n']} runs, up to {f['blind_laws']} laws.</li>
<li>A review with no proof duty missed one gap in {dup['said_complete']} of {dup['reviews']} reviews. The proof adversary found that gap {dup['proof_adversary_certificates']} of {dup['decision_points']} times.</li>
<li>A test links the model to the real code. For the lock it ran {f['link_events'] / 1e6:.1f} million events against the real lock class, with {f['link_differ']} differences.</li>
<li>On a product function, a decision table with {f['table_inputs']} inputs got {f['table_laws']} laws. Lean accepted a proof that the code passes them, and a proof that the laws leave none of the {f['table_cases']} cases open. The work took about ten minutes with no worker agent.</li>
</ul>
<p>So we use a proof for a small rule where a missed case costs much: a decision table, a permission rule, a price rule, a lock. The command <code>hp</code> of the same package is the proof gate for one Python function.</p>
</section>"""


def failures(f: dict) -> str:
    items = [
        (whole(f["proof_cost"]), f"for {f['proof_detected']} of {f['known_n']} bugs",
         f"<strong>The full proof pipeline as a bug finder.</strong> An agent wrote a model and laws from the documentation of each function, and an adversary looked for a conflict with the code. "
         f"The pipeline detected {f['proof_detected']} of the {f['known_n']} known bugs. A review detected {f['review_opus']} for {whole(f['review_opus_cost'])}. The pipeline did find {f['proof_only']} bugs that no review found."),
        (f"{100 * f['misread'] / f['conflicts']:.0f}%", "of conflicts were misreads",
         f"<strong>Laws that an agent writes from documentation.</strong> We checked the {f['conflicts']} conflicts of the pipeline that still held on the newest releases. In {f['misread']} of them the law was wrong and the code was right. "
         f"{'None' if not f['conflicts_real'] else f['conflicts_real']} was a bug that a caller reaches. A proof makes a law exact. It does not make a law correct."),
        (f"{f['loops_early']} of {f['loops_n']}", "loops stopped too early",
         "<strong>A review loop that runs until it is dry.</strong> The loop stops when two reviews in sequence say that the laws are complete. "
         f"It stopped too early in {f['loops_early']} of {f['loops_n']} law sets, each time on the same fault of a definition. A proof of completeness does not have this fault."),
        (f"{f['reverted']} of {f['bugs']}", "fixes were wrong",
         f"<strong>A fix by an agent, with no second review.</strong> {f['reverted']} fixes passed the script check and the judge, and were wrong: each one changed the result for inputs that the bug does not cover. "
         "The second review found them. A human must review each fix before the merge."),
        (f"{f['bugs_grouped']}", f"bugs, against {f['bugs_first']}",
         f"<strong>One reviewer session for a whole file.</strong> It cost {money(f['cost_grouped'])} against {money(f['cost_first'])}, and it confirmed {f['bugs_grouped']} bugs against {f['bugs_first']}. "
         "More functions in one session get less attention each. It is an option of the tool, and it is not the default."),
        (f"{f['haiku']['detected']} of {f['haiku']['bugs']}", "with a small model",
         f"<strong>A cheaper reviewer.</strong> Haiku 5.5 as the reviewer detected {f['haiku']['detected']} of {f['haiku']['bugs']} known bugs. Low effort detected {f['low']['detected']}. "
         f"The default worker detected {f['new48']['detected']} of the same {f['new48']['runs']}."),
        (f"{f['one_pass']['detected']} of {f['one_pass']['bugs']}", "in one pass",
         f"<strong>One pass as the full answer.</strong> One review pass detects about a third of the known bugs. Two passes with one set of arguments detected {f['two']['each'][0]} and {f['two']['each'][1]}, and {f['two']['together']} together. "
         "Each pass finds other bugs, and a second pass costs as much as the first."),
        (str(CI_FAILED_WORKERS), "failed workers, one green job",
         f"<strong>Our own harness.</strong> The first CI job of the audit passed with {CI_FAILED_WORKERS} failed workers, because the gate passed with no review report. Our first blind test was not blind: the folder path showed the answer. "
         f'The <a href="{PAPER}#limits">paper</a> has each fault with its correction.'),
    ]
    rows = "".join(f'<div class="hp-fail"><div class="fig">{esc(fig)}<small>{esc(sub)}</small></div><p>{text}</p></div>' for fig, sub, text in items)
    return f"""<section id="failures">
<span class="step">6 · What did not work</span>
<h2>The results that changed our plan.</h2>
<p>We started with a proof for each change. The data moved us to a review with receipts for all code, and a proof for the few rules that need one.</p>
<div class="hp-fails">{rows}</div>
</section>"""


def limits() -> str:
    points = [
        "A pass of the gate says that each bug that two verifier agents confirmed is closed or waived. It does not say that the code has no bug.",
        "The tools work on Python functions only.",
        "We tested the tools on our own products. Most runs used Claude models through Claude Code.",
        "The comparison with two review tools is one release range and one run for each tool.",
        "We made no agent run on Windows. The fix step has a live run on Claude Code only.",
        "The proof results are on small domains that we selected. A stand-in gave the answers of the human in the proof loop.",
        "The parts of the proof gate are known work: the checker is the comparator of Lean, and hardware verification has the completeness criterion. We do not claim that no earlier system has this loop.",
        "Each cost is the API-equivalent price that the provider tool reported.",
    ]
    return f"""<section id="limits">
<span class="step">7 · Limits</span>
<h2>What this page does not show.</h2>
<ul class="hp-list">
{chr(10).join(f"<li>{esc(p)}</li>" for p in points)}
</ul>
</section>"""


def sources(f: dict) -> list:
    """Each number of the page: the number, what it is, the section of the paper, and the data file in the repository."""
    arms = f["h2h"]["arms"]
    s = f["self"]
    return [
        (f"{arms['hpf']['confirmed_distinct_bugs']}, {arms['claude']['confirmed_distinct_bugs']} and {arms['codex']['confirmed_distinct_bugs']}",
         "Confirmed bugs of three tools on one release range", "use", "14", "study/v2/h2h/result.json"),
        (f"{f['findings']}, {f['passed']} and {f['bugs']}", "Findings with a repro, findings that passed two verifiers, distinct bugs", "ladder", "13", "study/v2/ladder_summary.json"),
        (f"{f['stood']} of {f['bugs']}", "Fixes that stood after the second review", "ladder", "13", "study/v2/ladder_summary.json"),
        (f"{len(f['stopped'])} of {len(f['releases'])}", "Releases that the gate stopped", "use", "14", "study/v2/gate_live.json"),
        (f"{f['review_opus']}, {f['review_sonnet']}, {f['review_plain']} and {f['proof_detected']} of {f['known_n']}", "Known bugs that each method detected", "bugs", "12", "study/v2/retro_compare.json"),
        (f"{f['misread']} of {f['conflicts']}", "Conflicts of the proof pipeline that were a misread of the law", "bugs", "12", "study/v2/conflict_triage.json"),
        (f"{money(f['cost_first'])}, {money(f['cost_lean'])} and {money(f['cost_now'])}", "Cost of the audit of one range, in three versions of the tool", "use", "14", "study/v2/cost_cut.json, study/v2/release_050.json"),
        (f"{f['new48']['detected']} and {f['old48']['detected']} of {f['new48']['runs']}", "Known bugs that the worker of version 0.5 and of version 0.4 detected", "use", "14", "study/v2/release_050.json"),
        (f"{s['confirmed_bugs']} in {len(s['rounds'])} rounds", "Bugs that the tool found in its own release", "use", "14", "study/v2/release_050.json, study/v2/self_audit"),
        (f"{f['imp']['shown_by_a_repro']} of {f['imp']['claims']}, and {f['imp']['confirmed_distinct_bugs']}", "Outside claims that got a repro, and the distinct bugs that the verifiers confirmed", "use", "14", "study/v2/import_live.json"),
        (f"{f['adv']['runs']}, {f['adv']['gap_certificates_accepted']} and {f['adv']['completeness_proofs_accepted']}", "Adversary runs, gap certificates, completeness proofs", "results", "9", "labs/data/hard-proof.json (on this site)"),
        (f"{f['blind_ok']} of {f['blind_n']}", "Correct results in the blind test with generated rules", "scale", "8", "labs/data/hard-proof.json (on this site)"),
        (f"{f['dup']['said_complete']} of {f['dup']['reviews']}", "Reviews with no proof duty that missed one gap", "baseline", "10", "labs/data/hard-proof.json (on this site)"),
        (f"{f['loops_early']} of {f['loops_n']}", "Review loops that stopped too early", "loops", "11", "labs/data/hard-proof.json (on this site)"),
    ]


def data(f: dict) -> str:
    rows = "".join(f'<tr><td class="num">{esc(n)}</td><td>{esc(what)}</td><td class="nw"><a href="{PAPER}#{anchor}">Section {sec}</a></td><td><code>{esc(path)}</code></td></tr>'
                   for n, what, anchor, sec, path in sources(f))
    return f"""<section id="data">
<span class="step">8 · Data</span>
<h2>Each number on this page, and its source.</h2>
<p>A script writes this page from the data files of the study, so each result has one source. The repository has each file, and the command that makes it.</p>
<div class="scroll"><table>
<thead><tr><th>Number</th><th>What it is</th><th>Paper</th><th>Data file</th></tr></thead>
<tbody>{rows}</tbody></table></div>
<div class="hp-links"><a class="button" href="{PAPER}">Read the paper</a><a class="button ghost" href="/labs/hard-proof/paper.pdf">Paper (PDF)</a><a class="button ghost" href="{REPO_URL}">Code on GitHub</a><a class="button ghost" href="{REPO_URL}/blob/main/docs/CLAIMS.md">Claims and commands</a><a class="button ghost" href="/labs/data/hard-proof.json">Data</a><a class="button ghost" href="/labs/data/hard-proof-artifacts.zip">Lean sources and gates</a></div>
</section>"""


def head(f: dict) -> str:
    arms = f["h2h"]["arms"]
    title = "Hard Proof: no repro, no bug"
    desc = (f"A review finding counts only with a repro that a script runs, and a release waits until each confirmed bug is closed. "
            f"On one release range hpf confirmed {arms['hpf']['confirmed_distinct_bugs']} bugs and two AI review tools confirmed {arms['claude']['confirmed_distinct_bugs']} each. "
            "A proof is the second tool, for a small rule that the owner states.")
    short = "A release gate for code that AI agents write: no repro, no bug. No fix, no release."
    image = PAGE_URL + "og-hpf.png"
    return f"""<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8"><meta name="viewport" content="width=device-width, initial-scale=1">
<meta name="description" content="{esc(desc)}">
<meta name="theme-color" content="#0a0a09"><title>{esc(title)} — Puppetmaster</title>
<link rel="canonical" href="{PAGE_URL}">
<meta property="og:type" content="article"><meta property="og:title" content="{esc(title)}"><meta property="og:description" content="{esc(short)}"><meta property="og:url" content="{PAGE_URL}"><meta property="og:image" content="{image}"><meta property="og:image:width" content="1280"><meta property="og:image:height" content="640">
<meta name="twitter:card" content="summary_large_image">
<meta name="twitter:image" content="{image}">
<link rel="icon" type="image/png" href="/logo-128.png">
<link rel="preconnect" href="https://fonts.googleapis.com"><link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
<link rel="stylesheet" href="https://fonts.googleapis.com/css2?family=Barlow+Condensed:wght@600;700&family=IBM+Plex+Mono:wght@400;500;600&family=Manrope:wght@400;500;600;700&display=swap">
<link rel="stylesheet" href="/style.css">
<link rel="stylesheet" href="/labs/hard-proof/hp.css">
<script>document.documentElement.classList.add('js')</script><script src="/site.js" defer></script>
<script src="/labs/hard-proof/vendor/zdog.dist.min.js" defer></script>
<script src="/labs/hard-proof/hp.js" defer></script>
</head>"""


def chrome(page: str) -> tuple:
    """The navigation and the footer of the site, from the page that is there now. The site owns them."""
    nav = re.search(r'<header class="nav">.*?</header>', page, flags=re.S)
    foot = re.search(r'<footer class="wrap foot">.*?</footer>', page, flags=re.S)
    if not nav or not foot:
        raise SystemExit("the current page has no site navigation or no footer: build_page.py takes them from it")
    return nav.group(0), foot.group(0)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--site", type=Path, required=True)
    args = parser.parse_args()
    site = args.site.expanduser()
    folder = site / "dist" / "labs" / "hard-proof"
    nav, foot = chrome((folder / "index.html").read_text(encoding="utf-8"))
    f = facts(site)
    body = "\n\n".join([hero(f), use(f), ladder(f), evidence(f), cost(f), proof(f), failures(f), limits(), data(f)])
    page = (f"{head(f)}\n<body class=\"doc-page\">\n<a class=\"skip\" href=\"#article\">Skip to article</a>\n{nav}\n\n"
            f"<article class=\"hp\" id=\"article\">\n{body}\n</article>\n{foot}\n</body>\n</html>\n")
    (folder / "index.html").write_text(page, encoding="utf-8")
    for name in ("hp.css", "hp.js"):
        shutil.copyfile(HERE / "page" / name, folder / name)
    shutil.copyfile(ROOT / "docs" / "social-card.png", folder / "og-hpf.png")
    words = len(re.sub(r"<[^>]+>", " ", body).split())
    print(json.dumps({"page": str(folder / "index.html"), "words": words, "numbers_with_a_source": len(sources(f))}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
