# Hard Proof

[![PyPI](https://img.shields.io/pypi/v/hpflow.svg)](https://pypi.org/project/hpflow/)
[![License: MIT](https://img.shields.io/badge/License-MIT-blue.svg)](https://github.com/professorpalmer/hard-proof/blob/main/LICENSE)
[![Python](https://img.shields.io/badge/python-3.9%2B-blue.svg)](https://github.com/professorpalmer/hard-proof/blob/main/tool/pyproject.toml)

![hpf: no repro, no bug. No fix, no release.](https://professorpalmer.github.io/hard-proof/social-card.png)

Hard Proof is a way to accept agent-written code on evidence. A review finding counts only with a repro that a
script runs. A small rule that the owner states gets a machine-checked proof, and an adversary proves what the
rule leaves open.

This repository has the tools, the data and the paper of the study "Proved is not finished".

## Quick setup

```bash
pip install hpflow
```

Audit the Python functions that changed since a tag, then gate the release:

```bash
hpf audit --repo . --ref HEAD --changed v1.2.3..HEAD --out ~/audits/next
hpf fix   --out ~/audits/next      # only when REPORT.md has confirmed bugs
hpf gate  --out ~/audits/next --ref HEAD
```

`hpf audit` and `hpf fix` start agent workers through the Puppetmaster command line and Claude Code. `hpf gate`
makes no model call. For all steps, the costs and the limits, see [Use the tools](https://github.com/professorpalmer/hard-proof/blob/main/docs/USE.md).

## Index

### Use it

| Doc | What it covers |
|---|---|
| [Use the tools](https://github.com/professorpalmer/hard-proof/blob/main/docs/USE.md) | Install, audit a git range, gate a release, try the proof gate, costs, limits |
| [Tool reference](https://github.com/professorpalmer/hard-proof/blob/main/tool/README.md) | Each command of `hp` and `hpf`, and the domain contract of the proof gate |
| [hpflow on PyPI](https://pypi.org/project/hpflow/) | The package |

### The study

| Doc | What it covers |
|---|---|
| [Study page](https://puppetmaster.gg/labs/hard-proof/) | The study in steps, with the results. This page is the current version |
| [Paper](https://puppetmaster.gg/labs/hard-proof/paper/) | Method, results, recommendation, limits ([PDF](https://github.com/professorpalmer/hard-proof/blob/main/docs/paper.pdf)) |
| [Results](https://github.com/professorpalmer/hard-proof/blob/main/docs/RESULTS.md) | The idea in five sentences, and each result with its evidence |

### Reproduce

| Doc | What it covers |
|---|---|
| [Claims and commands](https://github.com/professorpalmer/hard-proof/blob/main/docs/CLAIMS.md) | The folder and the command for each claim of the paper |
| [Repository layout](https://github.com/professorpalmer/hard-proof/blob/main/docs/LAYOUT.md) | What each folder holds, the requirements, and the run records |
| [Study folders](https://github.com/professorpalmer/hard-proof/tree/main/study) | Each experiment, the run records and the data |

The full docs list is in the [docs index](https://github.com/professorpalmer/hard-proof/blob/main/docs/README.md).

## License

MIT
