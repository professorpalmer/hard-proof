"""The briefs of the workers. The texts come from the study scripts in `hard-proof/v2`."""
from __future__ import annotations

REVIEW = """The folder `project/` has the Python source of a tool. Please review one function: `{function}` in `project/{file}`, with the helper functions that it calls.

Look for inputs for which this function gives a wrong result: a result that conflicts with its docstring, its comments, the documentation in `project/docs` or `project/README.md`, the name of the function, or what its callers in the project need. Only report a problem that you are sure about. If you find no problem, report none. Do not report style, speed, or missing features.

Write your report into the current folder:
- `findings.json`: a JSON list, the most certain finding first, at most 5 entries. Each entry: {{"n": 1, "claim": "what is wrong, in one or two sentences", "expected": "the result that a correct function gives for the input of the repro", "confidence": "high | medium"}}. An empty list when you find no problem.
- For each finding `n`, a file `finding_<n>.py` that defines `run()` with no arguments. `run()` imports the function from the project (the folder `project/` is the first entry of `sys.path`, so `import {top}` works), calls it on the input of your finding, and returns a short string that shows the result (use `repr`). If the function needs small state, build it inside `run()` with the standard library only. `run()` must be deterministic: no real time, no random values, no network, no paths outside a `tempfile.TemporaryDirectory()`. If the result is an exception, catch it and return its class name.

{arm_text}Do not change `project/`. End with VERDICT: PASS when the report is written."""

REVIEW_FILE = """The folder `project/` has the Python source of a tool. Please review these functions in `project/{file}`, each with the helper functions that it calls:

{functions}

Look for inputs for which one of these functions gives a wrong result: a result that conflicts with its docstring, its comments, the documentation in `project/docs` or `project/README.md`, the name of the function, or what its callers in the project need. Give each function in the list the same care. Only report a problem that you are sure about. If you find no problem in a function, report none for it. Do not report style, speed, or missing features.

Write your report into the current folder:
- `findings.json`: a JSON list, the most certain finding first, at most {per_function} entries for each function. Each entry: {{"n": 1, "function": "the name of the function, exactly as in the list above", "claim": "what is wrong, in one or two sentences", "expected": "the result that a correct function gives for the input of the repro", "confidence": "high | medium"}}. `n` counts from 1 over all entries. An empty list when you find no problem.
- For each finding `n`, a file `finding_<n>.py` that defines `run()` with no arguments. `run()` imports the function from the project (the folder `project/` is the first entry of `sys.path`, so `import {top}` works), calls it on the input of your finding, and returns a short string that shows the result (use `repr`). If the function needs small state, build it inside `run()` with the standard library only. `run()` must be deterministic: no real time, no random values, no network, no paths outside a `tempfile.TemporaryDirectory()`. If the result is an exception, catch it and return its class name.

{arm_text}Do not change `project/`. End with VERDICT: PASS when the report is written."""

REVIEW_FILE_CHECK = "python3 -c \"import json;d=json.load(open('findings.json'));names=json.load(open('functions.json'));assert isinstance(d,list) and all(x.get('function') in names for x in d)\""
PER_FUNCTION = 4

REVIEW_ARM = {"plain": "You have no shell in this task. Read the code.\n\n",
              "shell": "You have a shell. You can run Python on the project to check a finding, for example `cd project && python3 -c \"...\"`.\n\n"}
REVIEW_CHECK = "python3 -c \"import json;d=json.load(open('findings.json'));assert isinstance(d,list) and len(d)<=5\""

VERIFY = """The folder `project/` has the current source of the product `{repo}` (Python package, tests and documentation). {head}

`claims.json` lists the claims. For claim `k`, the file `claim_<k>.py` defines `run()`, which calls the function on the input of the claim, and `claims.json` has the result that `run()` gives on the current source (`result_now`). You can run a claim again: `cd project && python3 -c "import sys; sys.path.insert(0, '.'); exec(open('../claim_1.py').read()); print(run())"`.

Your work: decide for each claim what it is. Read the function, its docstring and comments, the documentation, the tests in `project/tests` that cover it, and each caller of the function in the product (use grep). Then give one verdict:

- `real`: the result is wrong, and the product can hit it. You must name a caller (file and line) that can pass such an input in normal use, and say in one sentence what goes wrong for the user or for the product.
- `real_unreachable`: the result conflicts with the docstring, the documentation or the clear contract of the function, but no caller in the product can pass such an input today.
- `intended`: the behavior is by design. You must quote the comment, the documentation, the test, or the caller that depends on it.
- `unclear`: the evidence does not decide it. Say what decision the owner must make.

Be strict. A claim is `real` only when you can show the path from normal use of the product to the wrong result. A test in `project/tests` that asserts the current behavior is strong evidence for `intended`, unless the test itself conflicts with the documentation.

Write one file, `verdicts.json`, in the current folder: a JSON list with one entry for each claim:
{{"k": 1, "verdict": "real | real_unreachable | intended | unclear", "duplicate_of": null or the k of an earlier claim that states the same fault, "what_goes_wrong": "one sentence, or null", "caller": "path:line of the caller that reaches it, or null", "evidence": [{{"file": "path", "line": 12, "quote": "exact text"}}], "severity": "high | medium | low", "fix_idea": "one or two sentences, or null"}}

Do not change `project/`. Do not write other files, except scratch files in `.lake/`. End with `VERDICT: PASS` when `verdicts.json` has one entry for each claim."""

VERIFY_FILE_HEAD = "A code review made {n} claims about functions in `project/{file}`. Each claim in `claims.json` names its function. Some claims can be wrong, and some can be the same claim two times."
VERIFY_ONE_HEAD = "A code review made {n} claims about one function: `{function}` in `project/{file}`. Some claims can be wrong, and some can be the same claim two times."

VERIFY_CHECK = "python3 -c \"import json;d=json.load(open('verdicts.json'));c=json.load(open('claims.json'));assert {x['k'] for x in d}=={x['k'] for x in c};assert all(x['verdict'] in ('real','real_unreachable','intended','unclear') for x in d)\""
VERDICTS = ("real", "real_unreachable", "intended", "unclear")

DEFAULT_RULES = ("Keep the style of the repository. Do not add a dependency. "
                 "Tests have no network.")

BUILD = """This folder is a git worktree of the product `{repo}`, at the commit `{base}`. A code review found {n} bugs in `{file}`. Two independent reviewers confirmed each one on this source: the result is wrong, and a caller in the product can reach it.

The bugs:

{bugs}

For bug `<id>` and claim `<k>`, the file `{info}/<id>_claim_<k>.py` defines `run()`, which shows the wrong result on this source (the listed "result now"). Read these files with `cat`.

Your work:
1. Read the function, its callers and its tests. Make sure that you understand each bug. If you find that one is not a bug (the behavior is by design), do not change the code for it: say so in your report with the evidence.
2. Fix each bug with the smallest change that corrects it. Do not change behavior that the bugs do not need. Do not refactor. Keep each existing test green: if an existing test asserts the wrong behavior, name it in your report and correct that one assertion.
3. Write regression tests in the new file `{test_file}`: for each bug at least one test that fails on the old code and passes on the fixed code, and one test for a near input that must keep its old result.
4. Run `{test_run}` and the existing test files that cover this module.

Rules of this repository: {rules} No emojis. Comments and docstrings in short plain sentences; a comment says why, not what. Edit `{file}` and `{test_file}`. Edit a second source file only when the same fault is in a sibling code path that must change together with it (for example a second caller that builds the same value in the same wrong way), and name each such file in your report. Edit an existing test file only when it asserts the wrong behavior. Do not commit.

The check after your work: `{check}` (each repro must give a new result, the new tests and the related tests must pass). Run it yourself.

Report: for each bug, the cause in one sentence and the change in one sentence. End with `VERDICT: PASS` when each bug is fixed or shown to be by design, else `VERDICT: PARTIAL - <what is open>`."""

JUDGE = """Review the uncommitted change in this git worktree of `{repo}` (`git diff` and the new file `{test_file}`). The change must fix these confirmed bugs in `{file}`:

{bugs}

Rubric. Give FAIL when one item fails, and list each problem as `path:line - what`:
1. Each bug is fixed at its cause, or the report shows with evidence that it is by design. A fix that only hides the repro input is a failure.
2. The change is minimal: no refactor, no unrelated edit, no new dependency.
3. No behavior changes for inputs that the bugs do not cover. Check the callers of the function.
4. Each new test asserts the correct behavior and fails on the old code (read the test and the old code, or run it against `git stash`-free means: `git show HEAD:{file}`).
5. The code follows the rules of the repository: {rules} No emojis.
6. No existing test was weakened, except an assertion that tested the wrong behavior of one of these bugs.

You can run `{test_run}`. Do not edit files."""
