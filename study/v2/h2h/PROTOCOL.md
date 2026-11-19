# Head-to-head: one release range, three review tools

Written 2026-11-19 before the runs of the two other products. Public since 2026-11-19 on the decision of the owner.
Not in paper Revision 10.

## Question

On the same change, how many real bugs that a caller can reach does each tool find?

## Challenge

- Product: Puppetmaster. Range: `v1.50.0..v1.51.1`, paths `puppetmaster bench tests docs README.md pyproject.toml`
  (17 files, 1,025 lines added, 32 removed, 20 changed functions).
- Each of the two other products gets a git repository with two commits and no tags: `main` is the tree of
  `v1.50.0`, and `feature` is that tree plus the change. No later history is in the repository.

## Tools

| Arm | Command | Settings |
| --- | --- | --- |
| `hpf` | `hpf audit --changed v1.50.0..v1.51.1` (hpflow 0.4.0 defaults, lean workers) | Stored run `audit-pm-1510-lean`, 2026-11-18. It ran before this protocol. |
| Claude Code | `claude -p "/code-review high main..feature"` | Claude Code 2.1.316, no user settings (`--setting-sources ""`), no MCP servers, clean environment, default model. |
| Codex | `codex review --base main` | codex-cli 0.160.0, the config of the owner (`gpt-6.1-sol`, `xhigh`). |

One run for each arm. No prompt text of ours goes to the two other products.

## Score

1. Each finding of each arm goes into one list. The list has the claim text, the file and the function.
   It does not have the name of the arm, and it does not have a repro command. The order is random (seed 1).
2. Two verifier agents (Opus 5.5 and Sonnet 5.5) each give one verdict for each claim against the tree of
   `v1.51.1`: `real` (with a caller, file and line), `real_unreachable`, `intended`, `unclear`.
3. A claim is confirmed when the two verdicts are `real`.
4. Confirmed claims with one root cause are one bug. The merge is in `merge.json`, with the reason.
5. Result for each arm: confirmed distinct bugs, bugs that only this arm found, findings in total, time, cost.

## Rules for the use of the result

- All results go into `result.json`, also when `hpf` finds fewer bugs.
- A claim on the card needs: `hpf` has more confirmed distinct bugs than the product, and the claim names
  the range and the count.
- Limits to state with each use: one range, one run for each arm, one owner, the models are not the same,
  the stored `hpf` findings are judged again by this verify step (not by their stored verdicts).
