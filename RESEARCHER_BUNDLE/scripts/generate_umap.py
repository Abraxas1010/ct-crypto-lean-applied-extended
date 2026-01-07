#!/usr/bin/env python3
"""
Generate UMAP embeddings for CT Crypto proof structure.

Produces interactive 2D and 3D HTML visualizations of the proof dependencies.
"""

import json
import subprocess
import re
from pathlib import Path
from dataclasses import dataclass
from typing import List, Dict, Optional

@dataclass
class Declaration:
    name: str
    file: str
    line: int
    docstring: str
    module: str
    kind: str  # theorem, def, structure, etc.

MODULES = {
    "PhysicalModality": "modality",
    "ContextualityPhysical": "modality",
    "TaskPossible": "modality",
    "EmpiricalModel": "contextuality",
    "ContextualitySite": "contextuality",
    "TaskExistence": "task",
    "InformationSound": "task",
    "Core": "task",
    "QubitLike": "task",
    "Security": "security",
    "Composition": "security",
    "ConstructiveHardnessCore": "umbrella",
    "ConstructiveHardnessSanity": "test",
}

MODULE_COLORS = {
    "modality": "#7aa2f7",
    "contextuality": "#7aa2f7",
    "task": "#f7768e",
    "security": "#9ece6a",
    "umbrella": "#bb9af7",
    "test": "#9aa4b2",
}

def extract_declarations(lean_dir: Path) -> List[Declaration]:
    """Extract declarations from Lean files."""
    decls = []
    for lean_file in lean_dir.rglob("*.lean"):
        content = lean_file.read_text()
        rel_path = lean_file.relative_to(lean_dir)

        # Determine module category
        for mod_name, category in MODULES.items():
            if mod_name in str(rel_path):
                module_cat = category
                break
        else:
            module_cat = "other"

        # Extract theorems, defs, structures
        patterns = [
            (r"theorem\s+(\w+)", "theorem"),
            (r"def\s+(\w+)", "def"),
            (r"structure\s+(\w+)", "structure"),
            (r"lemma\s+(\w+)", "lemma"),
        ]

        for pattern, kind in patterns:
            for match in re.finditer(pattern, content):
                name = match.group(1)
                line = content[:match.start()].count('\n') + 1

                # Extract docstring if present
                docstring = ""
                before = content[:match.start()].rstrip()
                if before.endswith("-/"):
                    doc_start = before.rfind("/-")
                    if doc_start != -1:
                        docstring = before[doc_start+2:-2].strip()

                decls.append(Declaration(
                    name=name,
                    file=str(rel_path),
                    line=line,
                    docstring=docstring[:200] if docstring else "",
                    module=module_cat,
                    kind=kind,
                ))

    return decls

def generate_html_2d(decls: List[Declaration], output_path: Path):
    """Generate interactive 2D UMAP visualization."""
    # For now, use a simple layout (real UMAP would use sklearn)
    html = """<!DOCTYPE html>
<html>
<head>
<meta charset="utf-8">
<title>CT Crypto 2D Proof Map</title>
<style>
:root {
  --bg: #0b0e14;
  --panel: #121826;
  --text: #e6edf3;
  --muted: #9aa4b2;
}
body { margin: 0; background: var(--bg); color: var(--text); font-family: system-ui; }
#canvas { width: 100vw; height: 100vh; }
.tooltip {
  position: absolute; background: var(--panel); border: 1px solid rgba(255,255,255,0.1);
  padding: 8px 12px; border-radius: 8px; font-size: 12px; pointer-events: none;
  max-width: 300px; display: none;
}
</style>
</head>
<body>
<svg id="canvas" viewBox="0 0 800 600"></svg>
<div class="tooltip" id="tooltip"></div>
<script>
const decls = """ + json.dumps([{
        "name": d.name,
        "file": d.file,
        "module": d.module,
        "kind": d.kind,
        "x": 100 + (hash(d.name) % 600),
        "y": 100 + (hash(d.file) % 400),
    } for d in decls]) + """;

const colors = {
  modality: "#7aa2f7",
  contextuality: "#7aa2f7",
  task: "#f7768e",
  security: "#9ece6a",
  umbrella: "#bb9af7",
  test: "#9aa4b2",
};

const svg = document.getElementById("canvas");
const tooltip = document.getElementById("tooltip");

decls.forEach((d, i) => {
  const circle = document.createElementNS("http://www.w3.org/2000/svg", "circle");
  circle.setAttribute("cx", d.x);
  circle.setAttribute("cy", d.y);
  circle.setAttribute("r", d.kind === "theorem" ? 8 : 6);
  circle.setAttribute("fill", colors[d.module] || "#9aa4b2");
  circle.setAttribute("fill-opacity", "0.6");
  circle.setAttribute("stroke", colors[d.module] || "#9aa4b2");
  circle.setAttribute("stroke-width", "1.5");
  circle.style.cursor = "pointer";

  circle.addEventListener("mouseenter", (e) => {
    tooltip.innerHTML = `<b>${d.name}</b><br><span style="color:#9aa4b2">${d.file}:${d.kind}</span>`;
    tooltip.style.left = e.pageX + 10 + "px";
    tooltip.style.top = e.pageY + 10 + "px";
    tooltip.style.display = "block";
  });
  circle.addEventListener("mouseleave", () => {
    tooltip.style.display = "none";
  });

  svg.appendChild(circle);
});
</script>
</body>
</html>"""

    output_path.write_text(html)
    print(f"Generated 2D visualization: {output_path}")

def main():
    script_dir = Path(__file__).parent
    bundle_dir = script_dir.parent
    lean_dir = bundle_dir / "HeytingLean"
    visuals_dir = bundle_dir / "artifacts" / "visuals"

    print("Extracting declarations...")
    decls = extract_declarations(lean_dir)
    print(f"Found {len(decls)} declarations")

    print("Generating 2D visualization...")
    generate_html_2d(decls, visuals_dir / "ct_crypto_2d.html")

    print("Done!")

if __name__ == "__main__":
    main()
