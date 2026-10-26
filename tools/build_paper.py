#!/usr/bin/env python3
"""Build the paper in temporary storage, preserving the recorded audit."""
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def main():
    paper = ROOT / "paper"
    with tempfile.TemporaryDirectory(prefix="superpermutation-paper-") as temporary:
        work = Path(temporary)
        for source in paper.iterdir():
            if source.suffix in {".tex", ".bib"}:
                shutil.copy2(source, work / source.name)
        commands = [
            ["pdflatex", "-interaction=nonstopmode", "-halt-on-error", "main.tex"],
            ["bibtex", "main"],
            ["pdflatex", "-interaction=nonstopmode", "-halt-on-error", "main.tex"],
            ["pdflatex", "-interaction=nonstopmode", "-halt-on-error", "main.tex"],
        ]
        for command in commands:
            result = subprocess.run(command, cwd=work, stdout=subprocess.PIPE,
                                    stderr=subprocess.STDOUT, text=True)
            if result.returncode:
                raise SystemExit(result.stdout)
        log = (work / "main.log").read_text(errors="replace")
        diagnostics = [line for line in log.splitlines()
                       if any(term in line for term in ("Warning", "Overfull", "Underfull", "undefined"))]
        if diagnostics:
            raise SystemExit("Inspect LaTeX diagnostics before replacing the PDF:\n" + "\n".join(diagnostics))
        shutil.copy2(work / "main.pdf", paper / "manuscript.pdf")
        print("Built paper/manuscript.pdf with no LaTeX warnings or box diagnostics.")
        print("The historical manuscript verification record is unchanged.")


if __name__ == "__main__":
    main()
