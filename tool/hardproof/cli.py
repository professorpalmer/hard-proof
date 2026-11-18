"""The command line: `python3 -m hardproof <command>` or `./hp <command>`."""
from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path

from hardproof.domain import AUTHOR_FILES, GEN_DIR, LOCK_FILE, SOLUTION_FILES, Domain, DomainError

CHECK_KINDS = ["model", "laws", "ref", "conflict", "gap", "complete"]


class UsageError(Exception):
    pass


class Parser(argparse.ArgumentParser):
    def error(self, message):
        raise UsageError(message)


def emit(report: dict) -> None:
    print(json.dumps(report, indent=2, sort_keys=False))


def parser() -> Parser:
    top = Parser(add_help=False)
    top.add_argument("--dir", type=Path, default=None, help="the domain folder (default: the current folder)")
    top.add_argument("--actor", default="unknown", help="who runs the command (for the run log)")
    # The options can also come after the command. There they do not reset a value given before it.
    common = Parser(add_help=False)
    common.add_argument("--dir", type=Path, default=argparse.SUPPRESS, help="the domain folder")
    common.add_argument("--actor", default=argparse.SUPPRESS, help="who runs the command")
    p = Parser(prog="hardproof", description="One proof gate for one Python function.", parents=[top])
    sub = p.add_subparsers(dest="command", parser_class=Parser)

    n = sub.add_parser("new", parents=[common], help="make a domain folder with author stubs")
    n.add_argument("target", type=Path)
    n.add_argument("--name", required=True)
    n.add_argument("--module", required=True)
    n.add_argument("--function", required=True)

    sub.add_parser("generate", parents=[common], help="write the tool-owned files again")

    c = sub.add_parser("check", parents=[common], help="run one or more checks")
    c.add_argument("kinds", nargs="+", choices=CHECK_KINDS)
    c.add_argument("--paranoid", action="store_true", help="run the five extra kernels of the comparator")

    l = sub.add_parser("link", parents=[common], help="the link test against the real Python function")
    l.add_argument("--repo", type=Path, required=True)
    l.add_argument("--cases", type=int, default=20000)
    l.add_argument("--seed", type=int, default=1)
    l.add_argument("--mutants", type=int, default=20)
    l.add_argument("--function-file", type=Path, default=None)

    q = sub.add_parser("question", parents=[common], help="the question of an accepted gap or conflict")
    q.add_argument("kinds", nargs="*", choices=["gap", "conflict"])
    q.add_argument("--paranoid", action="store_true")

    sub.add_parser("pin", parents=[common], help="write hardproof.lock.json")
    v = sub.add_parser("verify-pins", parents=[common], help="reject when a pinned file differs")
    v.add_argument("--expect", nargs="+", default=[], metavar="FILE=SHA")
    sub.add_parser("status", parents=[common], help="a summary of the domain")
    return p


def cmd_new(args) -> tuple:
    from hardproof.generate import generate
    from hardproof.stubs import stubs
    target = args.target if args.target.is_absolute() else (args.dir or Path.cwd()) / args.target
    if target.exists() and any(target.iterdir()):
        return {"command": "new", "verdict": "reject", "problems": [f"{target} exists and is not empty"]}, 1
    target.mkdir(parents=True, exist_ok=True)
    for name, text in stubs(args.name, args.module, args.function).items():
        (target / name).write_text(text, encoding="utf-8")
    gen = generate(Domain(target))
    return {"command": "new", "verdict": "accept", "dir": str(target), "author_files": AUTHOR_FILES,
            "generated": gen["files"]}, 0


def cmd_check(args, domain: Domain) -> tuple:
    from hardproof.checks import check
    started = time.time()
    kinds = list(dict.fromkeys(args.kinds))
    results = []
    for kind in kinds:
        t0 = time.time()
        res = check(domain, kind, args.paranoid)
        res["seconds"] = round(time.time() - t0, 2)
        results.append(res)
    accepted = [r for r in results if r["verdict"] == "accept"]
    verdict = "accept" if accepted else "reject"
    seconds = round(time.time() - started, 2)
    report = {"command": "check", "kinds": kinds, "verdict": verdict,
              "accepted_kind": accepted[0]["kind"] if accepted else None,
              "results": results, "seconds": seconds}
    domain.log_run(args.actor, "check " + " ".join(kinds), verdict, seconds,
                   {"kinds": {r["kind"]: r["verdict"] for r in results}})
    return report, 0 if accepted else 1


def cmd_link(args, domain: Domain) -> tuple:
    from hardproof.link import link
    repo = args.repo.expanduser()
    if args.function_file is None and not repo.exists():
        return {"command": "link", "verdict": "disagree", "problems": [f"{repo} does not exist"]}, 1
    ff = args.function_file.expanduser().resolve() if args.function_file else None
    report = link(domain, repo.resolve(), args.cases, args.seed, args.mutants, ff)
    domain.log_run(args.actor, "link", report["verdict"], report.get("seconds", 0),
                   {"kinds": {"link": report["verdict"]}, "cases": report.get("cases"),
                    "differences": report.get("differences")})
    return report, 0 if report["verdict"] == "agree" else 1


def cmd_status(domain: Domain) -> tuple:
    cfg = domain.config()
    exists = {name: domain.path(name).exists() for name in AUTHOR_FILES}
    solutions = {kind: domain.path(f"{mod}.lean").exists() for kind, mod in SOLUTION_FILES.items()}
    last: dict = {}
    for run in domain.runs():
        for kind, verdict in (run.get("kinds") or {}).items():
            last[kind] = {"verdict": verdict, "time": run.get("time"), "actor": run.get("actor")}
    report = {"command": "status", "verdict": "accept", "name": cfg.get("name"),
              "function": f"{cfg['python']['module']}.{cfg['python']['function']}",
              "author_files": exists, "solution_files": solutions,
              "generated": (domain.gen / "lakefile.toml").exists(),
              "pinned": domain.path(LOCK_FILE).exists(), "last_check": last,
              "runs": len(domain.runs())}
    return report, 0


def main(argv: list = None) -> int:
    argv = sys.argv[1:] if argv is None else argv
    try:
        args = parser().parse_args(argv)
        if not args.command:
            raise UsageError("name a command: new, generate, check, link, question, pin, verify-pins, status")
    except UsageError as exc:
        emit({"verdict": "usage_error", "problems": [str(exc)]})
        return 2
    try:
        if args.command == "new":
            report, code = cmd_new(args)
        else:
            domain = Domain(args.dir or Path.cwd())
            domain.config()
            if args.command == "generate":
                from hardproof.generate import generate
                report, code = dict(command="generate", verdict="accept", **generate(domain)), 0
            elif args.command == "check":
                report, code = cmd_check(args, domain)
            elif args.command == "link":
                report, code = cmd_link(args, domain)
            elif args.command == "question":
                from hardproof.question import question
                report = question(domain, args.kinds or ["gap", "conflict"], args.paranoid)
                code = 0 if report["verdict"] == "accept" else 1
            elif args.command == "pin":
                from hardproof.pins import pin
                report, code = pin(domain), 0
            elif args.command == "verify-pins":
                from hardproof.pins import verify
                report = verify(domain, args.expect)
                code = 0 if report["verdict"] == "accept" else 1
            else:
                report, code = cmd_status(domain)
    except DomainError as exc:
        emit({"command": args.command, "verdict": "usage_error", "problems": [str(exc)]})
        return 2
    emit(report)
    return code
