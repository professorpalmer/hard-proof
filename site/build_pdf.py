#!/usr/bin/env python3
"""Hard Proof: build the paper as a print page and a PDF.

The source is the built paper page of the site. This script takes its article,
puts a plain print style on it, and prints it to PDF with headless Chrome.

Usage:
    python3 build_pdf.py --paper <site>/dist/labs/hard-proof/paper/index.html --out <repo>/docs

It also replaces `<site>/dist/labs/hard-proof/paper.pdf`, the copy that the site serves.
"""
from __future__ import annotations

import argparse
import re
import shutil
import subprocess
from pathlib import Path

CHROME = "/Applications/Google Chrome.app/Contents/MacOS/Google Chrome"
BASE = "https://puppetmaster.gg"

STYLE = """
@page { size: A4; margin: 22mm 20mm 22mm 20mm; }
* { box-sizing: border-box; }
html { font-size: 10.5pt; }
body { margin: 0 auto; max-width: 170mm; font-family: "Charter", "Iowan Old Style", "Palatino Linotype", Georgia, serif; line-height: 1.5; color: #111; background: #fff; }
h1 { font-size: 21pt; line-height: 1.2; margin: 0 0 6pt; font-weight: 700; }
h2 { font-size: 13.5pt; margin: 20pt 0 6pt; border-bottom: 0.6pt solid #999; padding-bottom: 2pt; break-after: avoid; }
h3 { font-size: 11.5pt; margin: 14pt 0 4pt; break-after: avoid; }
p, li { orphans: 3; widows: 3; }
p { margin: 0 0 7pt; text-align: left; }
ul, ol { margin: 0 0 8pt; padding-left: 16pt; }
li { margin-bottom: 3pt; }
a { color: #0b3d91; text-decoration: none; }
code, pre { font-family: "SF Mono", Menlo, Consolas, monospace; font-size: 8.6pt; }
code { overflow-wrap: anywhere; }
pre { margin: 0 0 9pt; padding: 6pt 8pt; border: 0.6pt solid #bbb; background: #f6f6f6; white-space: pre-wrap; overflow-wrap: anywhere; break-inside: avoid; }
table { width: 100%; border-collapse: collapse; margin: 4pt 0 10pt; font-size: 8.6pt; line-height: 1.35; font-family: -apple-system, "Helvetica Neue", Arial, sans-serif; }
th, td { border: 0.5pt solid #999; padding: 3pt 4pt; text-align: left; vertical-align: top; overflow-wrap: anywhere; }
th { background: #eee; font-weight: 600; }
tr { break-inside: avoid; }
td.ok { color: #1a6b1a; } td.bad { color: #a11; }
.abstract { margin: 10pt 0 14pt; padding: 9pt 11pt; border: 0.6pt solid #999; background: #fafafa; }
.abstract p { font-size: 9.8pt; }
.k { font: 600 8pt -apple-system, "Helvetica Neue", Arial, sans-serif; letter-spacing: .1em; text-transform: uppercase; color: #555; margin: 0 0 5pt; }
.claim { margin: 8pt 0 12pt; padding: 7pt 10pt; border-left: 2.5pt solid #333; background: #f3f3f3; font-weight: 600; }
.draft { display: inline-block; margin: 0 0 8pt; padding: 2pt 6pt; border: 0.6pt solid #666; font: 600 7.5pt -apple-system, "Helvetica Neue", Arial, sans-serif; letter-spacing: .08em; text-transform: uppercase; }
.small, .doc-cite p { font-size: 8.6pt; color: #333; }
.toc { columns: 2; column-gap: 18pt; font-size: 9.5pt; margin: 0 0 14pt; }
.doc-stats { display: grid; grid-template-columns: repeat(4, 1fr); gap: 6pt; margin: 0 0 12pt; }
.doc-stat { border: 0.6pt solid #999; padding: 5pt 7pt; }
.doc-stat span { display: block; font: 7.5pt -apple-system, "Helvetica Neue", Arial, sans-serif; color: #555; text-transform: uppercase; letter-spacing: .05em; }
.doc-stat strong { font-size: 14pt; }
.doc-scroll { overflow: visible; }
.meta { font: 9pt -apple-system, "Helvetica Neue", Arial, sans-serif; color: #333; margin: 0 0 10pt; }
"""


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--paper", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    html = args.paper.expanduser().read_text(encoding="utf-8")
    title = re.search(r"<title>(.*?)</title>", html, flags=re.S).group(1).split(" — ")[0].strip()
    article = html[html.index("<article"): html.index("</article>") + len("</article>")]
    article = re.sub(r'(href|src)="/(?!/)', rf'\1="{BASE}/', article)
    article = re.sub(r'\sdata-[a-z-]+="[^"]*"', "", article)
    page = (f'<!doctype html>\n<html lang="en">\n<head>\n<meta charset="utf-8">\n<title>{title}</title>\n'
            f'<meta name="viewport" content="width=device-width, initial-scale=1">\n'
            f'<link rel="canonical" href="{BASE}/labs/hard-proof/paper/">\n<style>{STYLE}</style>\n</head>\n<body>\n'
            f'<p class="meta">Puppetmaster Labs. The current version of this paper is at '
            f'<a href="{BASE}/labs/hard-proof/paper/">{BASE.split("//")[1]}/labs/hard-proof/paper</a>. '
            f'Code and data: <a href="https://github.com/professorpalmer/hard-proof">github.com/professorpalmer/hard-proof</a>.</p>\n'
            f'{article}\n</body>\n</html>\n')
    out = args.out.expanduser()
    out.mkdir(parents=True, exist_ok=True)
    (out / "paper.html").write_text(page, encoding="utf-8")
    pdf = out / "paper.pdf"
    subprocess.run([CHROME, "--headless=new", "--disable-gpu", "--no-pdf-header-footer", f"--print-to-pdf={pdf}",
                    (out / "paper.html").resolve().as_uri()], capture_output=True, text=True, timeout=180)
    if not pdf.exists():
        print("no pdf")
        return 1
    print(f"{pdf} {pdf.stat().st_size // 1024} KB")
    # The site serves its own copy, beside the folder of the paper page. One build writes the two copies,
    # so the copy on the site cannot stay at an older revision.
    site_copy = args.paper.expanduser().resolve().parent.parent / "paper.pdf"
    if site_copy.exists() and site_copy.resolve() != pdf.resolve():
        shutil.copyfile(pdf, site_copy)
        print(f"{site_copy} (site copy)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
