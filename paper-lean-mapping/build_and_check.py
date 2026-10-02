"""Validate the result map and its generated files; use --write to regenerate them."""

from pathlib import Path
import argparse
import re
import tempfile
import copy
import html
import json
import subprocess
import shutil
import textwrap
import xml.etree.ElementTree as ET


def require(condition, message):
    if not condition:
        raise ValueError("FAIL: " + message)


def lean_code(text):
    """Remove nested comments and strings, preserving newlines for declaration scanning."""
    result = []
    i = 0
    depth = 0
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth += 1
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                i += 2
            else:
                result.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif text.startswith("/-", i):
            depth = 1
            result.append(" ")
            i += 2
        elif text.startswith("--", i):
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
        elif text[i] == '"':
            i += 1
            while i < len(text):
                if text[i] == "\\":
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    result.append("\n" if text[i] == "\n" else " ")
                    i += 1
            result.append(" ")
        else:
            result.append(text[i])
            i += 1
    require(depth == 0, "unterminated Lean comment")
    return "".join(result)


def declarations(text):
    """Names of source declarations under their explicit namespace/section stack."""
    names = set()
    stack = []
    namespace = []
    for line in lean_code(text).splitlines():
        line = line.strip()
        match = re.match(r"namespace\s+([\w.\']+)\s*$", line)
        if match:
            stack.append(list(namespace))
            namespace += match[1].split(".")
            continue
        if re.match(r"(?:noncomputable\s+)?section(?:\s+\S+)?\s*$", line):
            stack.append(list(namespace))
            continue
        if re.match(r"end(?:\s+\S+)?\s*$", line):
            require(bool(stack), "unbalanced Lean namespace")
            namespace = stack.pop()
            continue
        match = re.match(
            r"(?:(?:noncomputable|private|protected|unsafe)\s+)*(?:def|abbrev|theorem|lemma|inductive|structure|opaque)\s+([\w.\']+)",
            line,
        )
        if match:
            name = match[1]
            names.add(
                name.removeprefix("_root_.")
                if name.startswith("_root_.")
                else ".".join(namespace + [name])
            )
    return names


STATUSES = {
    "Lean-proved": "#d1fae5",
    "Exact-verified": "#dbeafe",
    "Proved in the paper only": "#fef3c7",
    "Unproved remark": "#ede9fe",
}


def validate(root, data):
    rows = data["results"]
    by_label = {row["label"]: row for row in rows}
    require(
        bool(rows) and len(by_label) == len(rows), "empty or repeated result labels"
    )
    assigned = []
    for row in rows:
        require(row["status"] in STATUSES, "unknown evidence status")
        for field in (
            "label",
            "title",
            "statement",
            "section",
            "explanation",
            "scope",
        ):
            require(
                isinstance(row[field], str) and bool(row[field]),
                "missing result field: " + field,
            )
        assigned += [row["label"]] + row.get("additional_labels", [])
        require(
            len(set(row["paper_dependencies"])) == len(row["paper_dependencies"]),
            "repeated dependency",
        )
        for dep in row["paper_dependencies"]:
            require(dep in by_label, "dangling dependency: " + dep)
        routes = row["formal_routes"]
        require(isinstance(routes, dict) and set(routes) <= set(row["paper_dependencies"]),
                "formal-route note must name a paper dependency")
        for dep in row["paper_dependencies"]:
            if row["status"] == "Lean-proved" and by_label[dep]["status"] != "Lean-proved":
                require(bool(row["lean"]) and bool(routes.get(dep)),
                        "Lean-proved result must explain its separate formal route: " + dep)
        require(all(isinstance(note, str) and note.strip() for note in routes.values()),
                "empty formal-route explanation")
        for ref in row["lean"]:
            path = root / ref["file"]
            require(
                ref["file"].startswith("lean/")
                and ".." not in Path(ref["file"]).parts
                and path.is_file(),
                "missing Lean file",
            )
            require(
                ref["name"] in declarations(path.read_text()),
                "missing Lean declaration: " + ref["name"],
            )
            require(bool(ref["role"]), "Lean reference must state its role")
        for check in row["checks"]:
            path = root / check["script"]
            require(
                check["script"].startswith("verification/")
                and ".." not in Path(check["script"]).parts
                and path.is_file(),
                "missing verification script",
            )
            require(
                check["script"] in check["command"]
                and check["expected"]
                and check["scope"],
                "incomplete exact-check command",
            )
    require(len(assigned) == len(set(assigned)), "paper label assigned more than once")
    visited, active = set(), set()

    def visit(label):
        require(label not in active, "cyclic dependency: " + label)
        if label in visited:
            return
        active.add(label)
        for dep in by_label[label]["paper_dependencies"]:
            visit(dep)
        active.remove(label)
        visited.add(label)

    for label in by_label:
        visit(label)
    paper_labels = set()
    tex_files = sorted((root / "paper").rglob("*.tex"))
    for path in tex_files:
        text = re.sub(r"(?<!\\)%[^\n]*", "", path.read_text())
        found = re.findall(r"\\label\s*\{([^}]+)\}", text)
        require(
            not (paper_labels & set(found)) and len(found) == len(set(found)),
            "duplicate TeX label",
        )
        paper_labels.update(found)
        for match in re.finditer(
            r"\\begin\{(theorem|proposition|lemma|corollary|remark)\}(.*?)\\end\{\1\}",
            text,
            re.S,
        ):
            result_labels = re.findall(r"\\label\s*\{([^}]+)\}", match[2])
            require(
                bool(set(result_labels) & set(by_label)),
                "numbered result needs its own entry",
            )
    require(
        paper_labels <= set(assigned),
        "paper labels without entries: "
        + ", ".join(sorted(paper_labels - set(assigned))),
    )
    if not tex_files:
        require(
            data["paper_status"] == "pending" and bool(data["todos"]),
            "absent manuscript must be explicit",
        )
    else:
        require(data["paper_status"] == "present", "included manuscript must be marked present")
        require(
            all(label in paper_labels for label in by_label),
            "mapping result absent from paper",
        )
    return bool(tex_files)


def render_tables(data):
    lines = [
        "# Results by paper section", "",
        "Generated from `mapping.json`; edit that file and run `python3 paper-lean-mapping/build_and_check.py --write`.", "",
        "Evidence colours refer to the stated formal scope. All dependencies below are steps in the paper argument; the separate Lean routes are stated explicitly.", "",
    ]
    for section in dict.fromkeys(row["section"] for row in data["results"]):
        lines += ["## " + section, "",
                  "| Result | Statement and scope | Lean declarations | Exact computation |",
                  "|---|---|---|---|"]
        for row in data["results"]:
            if row["section"] != section:
                continue
            title = (f"[{row['number']}](../{row['paper_file']}) — "
                     if row.get("number") and row.get("paper_file") else "")
            grouped = {}
            for ref in row["lean"]:
                grouped.setdefault(ref["role"], []).append(
                    f"[{ref['name']}](../{ref['file']})")
            refs = "<br>".join(", ".join(names) + ": " + role for role, names in grouped.items()) or "No declaration cited."
            checks = "<br>".join(
                f"[{Path(check['script']).name}](#" + Path(check['script']).stem + ")"
                for check in row["checks"]) or (
                    "Unproved remark; no exact check."
                    if row["status"] == "Unproved remark" else "Written proof.")
            scope = row["scope"]
            if row["formal_routes"]:
                scope += "<br>" + "<br>".join(
                    f"**Paper edge from `{dep}`:** {note}"
                    for dep, note in row["formal_routes"].items())
            lines.append(f"| {title}{row['title']}<br>`{row['label']}` | {row['statement']}<br>**{row['status']}.** {scope} | {refs} | {checks} |")
        lines.append("")
    lines += ["## Exact computation commands", "",
              "Each program is listed once here; the result rows link to these entries. Run from the repository root. See [verification](../verification/README.md) for costs and coordinates.", ""]
    checks = {}
    for row in data["results"]:
        for check in row["checks"]:
            previous = checks.setdefault(check["script"], check)
            require(previous == check, "inconsistent descriptions of the same exact checker")
    for script, check in checks.items():
        lines += ["### " + Path(script).stem, "", check["scope"], "",
                  "Command: `" + check["command"] + "`.", "",
                  "Last line: `" + check["expected"] + "`.", ""]
    lines += ["## Remaining questions", ""] + ["- " + item for item in data["todos"]] + [""]
    return "\n".join(lines)


def render_graphs(data, svg=True):
    rows = data["results"]
    ids = {row["label"]: f"n{i}" for i, row in enumerate(rows)}
    status_ids = {status: f"s{i}" for i, status in enumerate(STATUSES)}
    mermaid = [
        "# Dependency graph",
        "",
        "Arrows record the paper argument, not Lean proof dependencies. Dashed edges into green nodes use a separate formal route, explained in the section table. Dashed edges into unproved remarks indicate motivation. Green status applies to the formal scope stated in the table. The uniform theorem covers every k >= 16; Lean closes the needed scale k = 4980737 directly. The positive range is a separate branch.",
        "",
        "```mermaid",
        '%%{init: {"flowchart": {"nodeSpacing": 16, "rankSpacing": 22, "padding": 8}, "themeVariables": {"fontSize": "14px"}}}%%',
        "flowchart LR",
        "  subgraph Results[Numbered results]",
        "    direction TB",
    ]
    dot = [
        "digraph Results {",
        'graph [rankdir=TB, bgcolor="white", pad="0.2", nodesep="0.2", ranksep="0.18", fontname="DejaVu Sans"];',
        'node [shape=box, style="rounded,filled", fontname="DejaVu Sans", fontsize=11, margin="0.10,0.06", color="#475569"];',
        'edge [color="#64748b", arrowsize=0.7];',
    ]
    for row in rows:
        identifier = ids[row["label"]]
        title = row.get("graph_title", row["title"])
        label = "\n".join(textwrap.wrap(title, 30)) + "\n" + row["label"]
        dot.append(
            f'{identifier} [label={json.dumps(label)}, fillcolor="{STATUSES[row["status"]]}"];'
        )
        mermaid.append(
            f'  {identifier}["{title}<br/>{row["label"]}"]:::{status_ids[row["status"]]}'
        )
        for dep in row["paper_dependencies"]:
            dashed = row["status"] == "Unproved remark" or dep in row["formal_routes"]
            dot.append(f"{ids[dep]} -> {identifier}" + (" [style=dashed];" if dashed else ";"))
            mermaid.append(f"  {ids[dep]} " + ("-.->" if dashed else "-->") + f" {identifier}")
    mermaid += ["  end", "  subgraph Legend", "    direction TB"]
    dot += [
        'subgraph cluster_legend { label="Evidence status"; color="#cbd5e1"; style=rounded;'
    ]
    for i, (status, color) in enumerate(STATUSES.items()):
        dot.append(
            f'legend{i} [label={json.dumps(status)}, fillcolor="{color}", fontsize=10];'
        )
        mermaid.append(f'    legend{i}["{status}"]:::{status_ids[status]}')
    legend_notes = [
        "Arrows: paper argument; not Lean proof dependencies",
        "Dashed to green: separate Lean route (see table)",
        "Green: Lean proves the formal scope in the table",
        "All k >= 16: paper; k = 4980737: Lean application",
        "Dashed to unproved remark: motivating evidence",
    ]
    for i, note in enumerate(legend_notes):
        dot.append(f'key{i} [label={json.dumps(note)}, fillcolor="white", fontsize=10];')
        mermaid.append(f'    key{i}["{note}"]')
    legend_nodes = [f"legend{i}" for i in range(len(STATUSES))] + [f"key{i}" for i in range(len(legend_notes))]
    dot += [" -> ".join(legend_nodes) + " [style=invis];", "}", "}"]
    mermaid += [
        "    legend0 ~~~ legend1 ~~~ legend2 ~~~ legend3",
        "  end",
        "  Results ~~~ Legend",
        "  style Results fill:#ffffff,stroke:#cbd5e1",
        "  style Legend fill:#ffffff,stroke:#cbd5e1",
    ]
    for status, color in STATUSES.items():
        mermaid.append(
            f"  classDef {status_ids[status]} fill:{color},stroke:#475569,color:#0f172a"
        )
    mermaid += [
        "```",
        "",
        (
            "“Proved in the paper only” records an analytic proof, whose manuscript is pending in this snapshot. A cited Lean proposition definition does not change that status."
            if data["paper_status"] == "pending"
            else "“Proved in the paper only” records an analytic proof. A cited Lean proposition definition does not change that status."
        ),
        "",
    ]
    if not svg:
        return {"graph.md": "\n".join(mermaid)}
    result = subprocess.run(
        ["dot", "-Tsvg"],
        input="\n".join(dot),
        text=True,
        capture_output=True,
        check=True,
    )
    tree = ET.fromstring(result.stdout)
    require(tree.tag.endswith("svg"), "Graphviz did not return SVG")
    # Graphviz provenance comments are immaterial to the mathematical diagram.
    svg = re.sub(r"<!--.*?-->\s*", "", result.stdout, flags=re.S)
    return {"graph.md": "\n".join(mermaid), "graph.svg": svg}


def svg_signature(svg):
    """Read graph content independently of coordinates, fonts, and SVG object ids.

    Graphviz stores stable DOT identifiers in group titles. Its generated XML
    ids (such as node1) depend on rendering order and are not graph identifiers.
    """
    try:
        root = ET.fromstring(svg)
    except ET.ParseError as error:
        raise ValueError("FAIL: malformed graph SVG") from error
    require(root.tag == "{http://www.w3.org/2000/svg}svg", "missing SVG root")

    def tag(element):
        return element.tag.rsplit("}", 1)[-1]

    def colour(value):
        value = value.strip().lower()
        if re.fullmatch(r"#[0-9a-f]{3}", value):
            value = "#" + "".join(character * 2 for character in value[1:])
        return {"white": "#ffffff", "black": "#000000",
                "transparent": "none"}.get(value, value)

    def paint(element, property_name, default):
        style = dict(item.split(":", 1) for item in element.get("style", "").split(";") if ":" in item)
        style = {key.strip(): value.strip() for key, value in style.items()}
        return style.get(property_name, element.get(property_name, default))

    signature = {}
    for group in root.iter():
        if tag(group) != "g":
            continue
        classes = tuple(sorted(group.get("class", "").split()))
        kinds = set(classes) & {"node", "edge", "cluster"}
        if not kinds:
            continue
        require(len(kinds) == 1, "ambiguous SVG graph group")
        titles = [child for child in group if tag(child) == "title"]
        require(len(titles) == 1, "missing or ambiguous SVG graph identifier")
        identifier = "".join(titles[0].itertext()).strip()
        require(bool(identifier), "empty SVG graph identifier")
        key = (next(iter(kinds)), identifier)
        require(key not in signature, "duplicate SVG graph identifier")
        labels, shapes = [], set()
        for child in group.iter():
            kind = tag(child)
            if kind == "text":
                labels.append((" ".join("".join(child.itertext()).split()),
                               colour(paint(child, "fill", "black"))))
            elif kind in {"path", "polygon", "polyline", "ellipse", "rect", "circle", "line"}:
                dash = paint(child, "stroke-dasharray", "none").strip().lower()
                shapes.add((colour(paint(child, "fill", "black")),
                            colour(paint(child, "stroke", "none")),
                            dash not in {"", "none", "0", "0,0", "0 0"}))
        require(bool(shapes), "SVG graph element has no shape")
        signature[key] = (classes, tuple(labels), tuple(sorted(shapes)))
    require(bool(signature), "SVG contains no graph elements")
    return signature


def generated_files(directory, expected, write=False):
    """Check every output before permitting any write."""
    if write:
        for name, contents in expected.items():
            path = directory / name
            if not path.exists() or path.read_text() != contents:
                path.write_text(contents)
        return
    for name, contents in expected.items():
        path = directory / name
        require(path.is_file(), f"missing generated file: {name}")
        actual = path.read_text()
        matches = (svg_signature(actual) == svg_signature(contents)
                   if name == "graph.svg" else actual == contents)
        require(matches,
                f"generated file differs: {name}; use --write to regenerate "
                "and inspect the change")


def generated_controls():
    svg = '''<svg xmlns="http://www.w3.org/2000/svg" width="200pt">
      <g class="node" id="node1"><title>a</title>
        <path fill="#d1fae5" stroke="#475569" d="M0,0 L1,1"/>
        <text x="0" y="0" font-family="serif">First result</text></g>
      <g class="node" id="node2"><title>b</title>
        <polygon fill="#fef3c7" stroke="#475569" points="0,0 1,1 0,1"/>
        <text>Second result</text></g>
      <g class="edge" id="edge1"><title>a-&gt;b</title>
        <path fill="none" stroke="#64748b" stroke-dasharray="5,2" d="M0,0 L1,1"/>
        <polygon fill="#64748b" stroke="#64748b" points="0,0 1,1 0,1"/></g>
      <g class="cluster"><title>cluster_legend</title>
        <path fill="white" stroke="#cbd5e1" d="M0,0 L1,1"/>
        <text>Evidence status</text></g></svg>'''
    with tempfile.TemporaryDirectory() as temporary:
        directory = Path(temporary)
        expected = {"graph.md": "diagram\n", "graph.svg": svg, "by-section.md": "table\n"}
        generated_files(directory, expected, write=True)
        generated_files(directory, expected)
        for name in expected:
            path = directory / name
            path.write_text("corrupt\n")
            try:
                generated_files(directory, expected)
            except ValueError:
                pass
            else:
                raise ValueError("FAIL: stale generated output accepted")
            require(path.read_text() == "corrupt\n", "check mode modified an output")
            generated_files(directory, expected, write=True)
        (directory / "graph.md").unlink()
        try:
            generated_files(directory, expected)
        except ValueError:
            pass
        else:
            raise ValueError("FAIL: missing generated output accepted")
        require(not (directory / "graph.md").exists(), "check mode created an output")
        generated_files(directory, expected, write=True)
        alternate = ET.fromstring(svg)
        alternate.set("width", "900pt")
        alternate[:] = reversed(list(alternate))
        for group in alternate:
            group.set("id", "different-" + group.get("id", "legend"))
        for element in alternate.iter():
            layout = {"x": "42", "y": "17", "d": "M10,10 L20,20",
                      "points": "10,10 20,20 10,20", "font-family": "sans-serif"}
            for attribute, value in layout.items():
                if attribute in element.attrib:
                    element.set(attribute, value)
            if element.get("fill") == "white":
                element.set("fill", "#fff")
        alternate_text = ET.tostring(alternate, encoding="unicode")
        (directory / "graph.svg").write_text(alternate_text)
        generated_files(directory, expected)
        require((directory / "graph.svg").read_text() == alternate_text,
                "check mode rewrote equivalent SVG")
        corruptions = [
            svg.replace("<title>a</title>", "<title>missing</title>"),
            svg.replace("a-&gt;b", "b-&gt;a"),
            svg.replace("First result", "Wrong result"),
            svg.replace("#d1fae5", "#fef3c7"),
            svg.replace('class="node"', 'class="node wrong-status"', 1),
            svg.replace('stroke-dasharray="5,2"', ''),
            svg.replace("Evidence status", "Wrong legend"),
            svg.replace("cluster_legend", "missing_legend"),
            svg.replace('<path fill="white"', '<path fill="red"'),
        ]
        missing = ET.fromstring(svg)
        missing.remove(list(missing)[0])
        corruptions.append(ET.tostring(missing, encoding="unicode"))
        duplicate = ET.fromstring(svg)
        duplicate.append(copy.deepcopy(list(duplicate)[0]))
        corruptions.append(ET.tostring(duplicate, encoding="unicode"))
        for corrupted in corruptions:
            (directory / "graph.svg").write_text(corrupted)
            try:
                generated_files(directory, expected)
            except ValueError:
                pass
            else:
                raise ValueError("FAIL: changed SVG graph content accepted")
            require((directory / "graph.svg").read_text() == corrupted,
                    "check mode repaired corrupted SVG")


def controls():
    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory)
        for name in ("lean", "paper", "verification"):
            (root / name).mkdir()
        (root / "lean/Test.lean").write_text(
            "namespace Example\n/-- def ghost := 0 -/\ndef present := 0\nend Example\n"
        )
        (root / "verification/test.py").write_text("")
        row = dict(
            label="thm:test",
            title="Test",
            statement="Test",
            section="Test",
            explanation="Test",
            scope="Test",
            status="Exact-verified",
            paper_dependencies=[],
            formal_routes={},
            lean=[
                dict(name="Example.present", file="lean/Test.lean", role="definition")
            ],
            checks=[
                dict(
                    script="verification/test.py",
                    command="python3 verification/test.py",
                    expected="PASS",
                    scope="Test",
                )
            ],
        )
        base = dict(paper_status="pending", todos=["Test"], results=[row])
        require(not validate(root, base), "placeholder positive control")
        route = copy.deepcopy(base)
        target = copy.deepcopy(row)
        target.update(label="thm:formal", status="Lean-proved",
                      paper_dependencies=["thm:test"])
        route["results"].append(target)
        try:
            validate(root, route)
        except ValueError:
            pass
        else:
            raise ValueError("FAIL: unexplained paper-only premise into Lean result accepted")
        target["formal_routes"] = {"thm:test": "A separate formal theorem supplies the required instance."}
        require(not validate(root, route), "explained separate formal route control")
        target["formal_routes"] = {"absent": "Not a paper edge."}
        try:
            validate(root, route)
        except ValueError:
            pass
        else:
            raise ValueError("FAIL: dangling formal-route note accepted")
        corruptions = []
        for field, value in [
            ("paper_dependencies", ["missing"]),
            ("paper_dependencies", ["thm:test"]),
            (
                "lean",
                [dict(name="Example.ghost", file="lean/Test.lean", role="definition")],
            ),
            (
                "checks",
                [
                    dict(
                        script="verification/missing.py",
                        command="python3 verification/missing.py",
                        expected="PASS",
                        scope="Test",
                    )
                ],
            ),
        ]:
            bad = copy.deepcopy(base)
            bad["results"][0][field] = value
            corruptions.append(bad)
        for bad in corruptions:
            try:
                validate(root, bad)
            except ValueError:
                pass
            else:
                raise ValueError("FAIL: corrupted mapping accepted")
        (root / "paper/main.tex").write_text(
            r"\begin{theorem}\label{thm:missing}X\end{theorem}"
        )
        try:
            validate(root, base)
        except ValueError:
            pass
        else:
            raise ValueError("FAIL: missing paper label accepted")
        (root / "paper/main.tex").write_text(
            r"\begin{theorem}\label{thm:test}X\end{theorem}"
        )
        try:
            validate(root, base)
        except ValueError:
            pass
        else:
            raise ValueError("FAIL: stale manuscript status accepted")
        base["paper_status"] = "present"
        require(validate(root, base), "paper coverage positive control")


def graphviz_preflight():
    executable = shutil.which("dot")
    require(executable is not None,
            "Graphviz 'dot' was not found. Install Graphviz, or use --no-graph "
            "to validate the map, tables, and Mermaid without checking SVG.")
    try:
        result = subprocess.run([executable, "-V"], capture_output=True, text=True)
    except OSError as error:
        raise ValueError("FAIL: Graphviz 'dot' could not run; repair the installation or use --no-graph") from error
    require(result.returncode == 0, "Graphviz 'dot -V' failed; repair the installation or use --no-graph")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="update generated tables and diagrams")
    parser.add_argument("--no-graph", action="store_true",
                        help="check or write tables and Mermaid without Graphviz; skip SVG")
    args = parser.parse_args()
    if not args.no_graph:
        graphviz_preflight()
    directory = Path(__file__).resolve().parent
    data = json.loads((directory / "mapping.json").read_text())
    controls()
    generated_controls()
    has_paper = validate(directory.parent, data)
    outputs = {"by-section.md": render_tables(data), **render_graphs(data, svg=not args.no_graph)}
    generated_files(directory, outputs, write=args.write)
    print(
        "PASS: mapping, DAG, declarations, scripts, and rejection controls ("
        + ("paper labels covered" if has_paper else "paper pending")
        + ("; SVG skipped" if args.no_graph else "")
        + ")"
    )


if __name__ == "__main__":
    try:
        main()
    except (ValueError, OSError, subprocess.CalledProcessError) as error:
        raise SystemExit(str(error)) from None
