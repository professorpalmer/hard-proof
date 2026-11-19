"""The command line of hpflow. Each command prints one JSON report."""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any, Callable, Dict, List, Optional

from . import commands as c
from .common import DEFAULT_CONCURRENCY, StepError, UsageError
from .runner import PuppetmasterRunner, Runner


class Parser(argparse.ArgumentParser):
    def error(self, message: str) -> None:  # type: ignore[override]
        raise UsageError(message)


def add_common(p: argparse.ArgumentParser) -> None:
    p.add_argument("--out", required=True, help="the audit folder")
    p.add_argument("--redo", action="store_true", help="run the workers again, also when a result is stored")
    p.add_argument("--concurrency", type=int, default=DEFAULT_CONCURRENCY,
                   help=f"the most worker flows that run at one time (default {DEFAULT_CONCURRENCY})")


def add_init(p: argparse.ArgumentParser) -> None:
    p.add_argument("--repo", required=True)
    p.add_argument("--ref", required=True)
    p.add_argument("--paths", nargs="+")
    p.add_argument("--python")
    p.add_argument("--test-cmd", help="template with {python} and {tests}")


def add_targets(p: argparse.ArgumentParser, required: bool = True) -> None:
    g = p.add_mutually_exclusive_group(required=required)
    g.add_argument("--changed", metavar="A..B")
    g.add_argument("--function", nargs="+", metavar="FILE:NAME", dest="functions")
    g.add_argument("--file", nargs="+", metavar="FILE", dest="files")
    p.add_argument("--max-lines", type=int, default=150)
    p.add_argument("--max", type=int, dest="max_n")


def add_review(p: argparse.ArgumentParser) -> None:
    p.add_argument("--model", default="sonnet")
    p.add_argument("--shell", dest="shell", action="store_true", default=True)
    p.add_argument("--no-shell", dest="shell", action="store_false")
    p.add_argument("--passes", type=int, default=1)
    p.add_argument("--repro-timeout", type=float, default=60)


def add_verify(p: argparse.ArgumentParser) -> None:
    p.add_argument("--models", nargs="+", default=["opus", "sonnet"])


def add_fix(p: argparse.ArgumentParser) -> None:
    p.add_argument("--base")
    p.add_argument("--only", nargs="+")
    p.add_argument("--model", default="opus", dest="fix_model")
    p.add_argument("--judge-model", default="sonnet")
    p.add_argument("--rules", help="the rules of the repository for the fix worker and the judge")


def add_waive(p: argparse.ArgumentParser) -> None:
    p.add_argument("--bug", required=True, help="the id of a confirmed bug")
    p.add_argument("--reason", required=True, help="why the behavior stays as it is")
    p.add_argument("--by", help="who decided")


def add_gate(p: argparse.ArgumentParser) -> None:
    p.add_argument("--ref", help="the commit to check, for example the release candidate")
    p.add_argument("--repro-timeout", type=float, default=60)


def build_parser() -> Parser:
    parser = Parser(prog="hpflow", description="Take Python functions up the evidence ladder with agent workers.")
    sub = parser.add_subparsers(dest="command", parser_class=Parser)
    for name, adders in (("init", [add_init]), ("targets", [add_targets]), ("review", [add_review]),
                         ("verify", [add_verify]), ("fix", [add_fix]), ("status", []),
                         ("waive", [add_waive]), ("gate", [add_gate]),
                         ("audit", [add_init, add_targets, add_review, add_verify])):
        p = sub.add_parser(name)
        add_common(p)
        for add in adders:
            add(p)
    return parser


def run_command(args: argparse.Namespace, ctx: c.Context) -> Dict[str, Any]:
    cmd = args.command
    if cmd == "init":
        return c.cmd_init(ctx, args.repo, args.ref, args.paths, args.python, args.test_cmd)
    if cmd == "targets":
        return c.cmd_targets(ctx, args.changed, args.functions, args.files, args.max_lines, args.max_n)
    if cmd == "review":
        if args.passes < 1:
            raise UsageError("--passes must be 1 or more")
        return c.cmd_review(ctx, args.model, args.shell, args.passes, args.repro_timeout)
    if cmd == "verify":
        return c.cmd_verify(ctx, args.models)
    if cmd == "fix":
        return c.cmd_fix(ctx, args.base, args.only, args.fix_model, args.judge_model, args.rules)
    if cmd == "status":
        return c.cmd_status(ctx)
    if cmd == "waive":
        return c.cmd_waive(ctx, args.bug, args.reason, args.by)
    if cmd == "gate":
        return c.cmd_gate(ctx, args.ref, args.repro_timeout)
    if cmd == "audit":
        steps: List[Dict[str, Any]] = []
        calls: List[Callable[[], Dict[str, Any]]] = [
            lambda: c.cmd_init(ctx, args.repo, args.ref, args.paths, args.python, args.test_cmd),
            lambda: c.cmd_targets(ctx, args.changed, args.functions, args.files, args.max_lines, args.max_n),
            lambda: c.cmd_review(ctx, args.model, args.shell, args.passes, args.repro_timeout),
            lambda: c.cmd_verify(ctx, args.models)]
        for call in calls:
            r = call()
            steps.append(r)
            if not r.get("ok"):
                break
        return {"command": "audit", "ok": all(s.get("ok") for s in steps) and len(steps) == len(calls), "steps": steps}
    raise UsageError("give a command: init, targets, review, verify, fix, audit, status, waive or gate")


def main(argv: Optional[List[str]] = None, runner: Optional[Runner] = None) -> int:
    try:
        args = build_parser().parse_args(argv)
        if not args.command:
            raise UsageError("give a command: init, targets, review, verify, fix, audit, status, waive or gate")
        if args.command == "audit" and not (args.changed or args.functions or args.files):
            raise UsageError("audit needs --changed, --function or --file")
        if args.concurrency < 1:
            raise UsageError("--concurrency must be 1 or more")
        out = Path(args.out).expanduser().resolve()
        runner = runner or PuppetmasterRunner(out / "graphs", concurrency=args.concurrency)
        ctx = c.Context(out, runner, redo=args.redo, concurrency=args.concurrency)
        report = run_command(args, ctx)
        code = 0 if report.get("ok") else 1
    except UsageError as e:
        report, code = {"ok": False, "usage_error": str(e)}, 2
    except StepError as e:
        report, code = {"ok": False, "error": str(e)}, 1
    print(json.dumps(report, indent=1))
    return code


if __name__ == "__main__":
    sys.exit(main())
