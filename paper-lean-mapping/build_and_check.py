"""Validate the result map and its generated files; use --write to regenerate them."""

from pathlib import Path
import argparse
import hashlib
import os
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


def pdf_tokens(text):
    return re.findall(r"[a-z0-9]+", text.lower())


def phrase_found(page, phrase):
    wanted = pdf_tokens(phrase)
    if not wanted:
        return True
    got = pdf_tokens(page)
    return any(got[i:i + len(wanted)] == wanted for i in range(len(got) - len(wanted) + 1))


def validate(root, data, pdf_pages):
    """Validate the result map against page-scoped text extracted from paper/main.pdf."""
    rows = data["results"]
    by_label = {row["label"]: row for row in rows}
    require(bool(rows) and len(by_label) == len(rows), "empty or repeated result labels")
    require(data.get("paper_status") == "pdf-only", "paper status must document PDF-only export")
    require(len(pdf_pages) == 29, "published PDF text must have 29 pages")
    require(hashlib.sha256((root / "paper/main.pdf").read_bytes()).hexdigest() == data["pdf_sha256"],
            "published PDF hash")
    numbers = []
    for row in rows:
        require(row["status"] in STATUSES, "unknown evidence status")
        for field in ("label", "number", "title", "statement", "section", "explanation", "scope"):
            require(isinstance(row.get(field), str) and row[field], "missing result field: " + field)
        require(isinstance(row.get("paper_page"), int) and 1 <= row["paper_page"] <= len(pdf_pages),
                "invalid recorded PDF page: " + row["label"])
        page = pdf_pages[row["paper_page"] - 1]
        require(row["number"] in page, "mapped result number absent from recorded PDF page: " + row["label"])
        require(row.get("pdf_title", "") == "" or phrase_found(page, row["pdf_title"]),
                "mapped result title absent from recorded PDF page: " + row["label"])
        require(row.get("paper_file", "").startswith("paper/"), "missing e-print source anchor")
        require(isinstance(row.get("source_index"), int) and row["source_index"] > 0, "missing source index")
        require(not row.get("additional_labels", []), "non-result labels belong in other_labels")
        numbers.append(row["number"])
        require(len(set(row["paper_dependencies"])) == len(row["paper_dependencies"]), "repeated dependency")
        for dep in row["paper_dependencies"]:
            require(dep in by_label, "dangling dependency: " + dep)
        routes = row["formal_routes"]
        require(isinstance(routes, dict) and set(routes) <= set(row["paper_dependencies"]),
                "formal-route note must name a paper dependency")
        for dep in row["paper_dependencies"]:
            if row["status"] == "Lean-proved" and by_label[dep]["status"] != "Lean-proved":
                require(bool(row["lean"]) and bool(routes.get(dep)),
                        "Lean-proved result must explain its separate formal route: " + dep)
        require(all(isinstance(note, str) and note.strip() for note in routes.values()), "empty formal-route explanation")
        for ref in row["lean"]:
            path = root / ref["file"]
            require(ref["file"].startswith("lean/") and ".." not in Path(ref["file"]).parts and path.is_file(), "missing Lean file")
            require(ref["name"] in declarations(path.read_text()), "missing Lean declaration: " + ref["name"])
            require(bool(ref["role"]), "Lean reference must state its role")
        for check in row["checks"]:
            path = root / check["script"]
            require(check["script"].startswith("verification/") and ".." not in Path(check["script"]).parts and path.is_file(), "missing verification script")
            require(check["script"] in check["command"] and check["expected"] and check["scope"], "incomplete exact-check command")
            for data_file in check.get("data_files", []):
                require(isinstance(data_file, str) and data_file.startswith("verification/") and ".." not in Path(data_file).parts and (root/data_file).is_file(), "missing exact-check data file")
    require(len(numbers) == len(set(numbers)), "duplicate mapped PDF numbers")
    require(len(data["other_labels"]) == len({row["label"] for row in data["other_labels"]}), "repeated other label")
    visited, active = set(), set()
    def visit(label):
        require(label not in active, "cyclic dependency: " + label)
        if label in visited: return
        active.add(label)
        for dep in by_label[label]["paper_dependencies"]: visit(dep)
        active.remove(label); visited.add(label)
    for label in by_label: visit(label)
    return True

KINDS = "theorem|proposition|lemma|corollary|remark|example"
RESULT_RE = re.compile(r"\\begin\{(" + KINDS + r")\}(?:\[[^\]]*\])?(.*?)\\end\{\1\}", re.S)


def source_files(root):
    main = root / "paper/main.tex"
    require(main.is_file(), "missing paper main source")
    files = ["paper/main.tex"]
    def visit(filename):
        text = re.sub(r"(?<!\\)%[^\n]*", "", (root / filename).read_text())
        for name in re.findall(r"\\input\{([^}]+)\}", text):
            child = "paper/" + name + ("" if name.endswith(".tex") else ".tex")
            require(".." not in Path(child).parts and (root/child).is_file(), "invalid paper input")
            require(child not in files, "repeated or cyclic paper input")
            files.append(child)
            visit(child)
    visit("paper/main.tex")
    return files


def source_inventory(root):
    results, locations = {}, {}
    for filename in source_files(root):
        text = re.sub(r"(?<!\\)%[^\n]*", "", (root/filename).read_text())
        for label in re.findall(r"\\label\s*\{([^}]+)\}", text):
            require(label not in locations, "duplicate TeX label: " + label)
            locations[label] = filename
        counts = {}
        for match in RESULT_RE.finditer(text):
            kind, body = match.groups()
            counts[kind] = counts.get(kind, 0) + 1
            labels = re.findall(r"\\label\s*\{([^}]+)\}", body)
            label = labels[0] if labels else f"unlabelled:{filename.removeprefix('paper/')}:{kind}:{counts[kind]}"
            require(label not in results, "duplicate numbered result")
            results[label] = dict(paper_file=filename,kind=kind,source_index=counts[kind],
                                  aux_label=label if labels else "mapping:"+label)
    require(bool(results), "no numbered results")
    return results, locations


def aux_group(text, start):
    require(start < len(text) and text[start] == "{", "expected aux group")
    depth, end = 1, start + 1
    while end < len(text) and depth:
        escaped = text[end-1] == "\\"
        if not escaped and text[end] == "{": depth += 1
        if not escaped and text[end] == "}": depth -= 1
        end += 1
    require(depth == 0, "incomplete aux group")
    return text[start+1:end-1], end


def aux_labels(text):
    labels = {}
    for match in re.finditer(r"\\newlabel\{", text):
        label, end = aux_group(text, match.end()-1)
        contents, end = aux_group(text, end)
        number, end = aux_group(contents, 0)
        require(label not in labels, "duplicate compiled label")
        labels[label] = number
    return labels


def immutable_inputs(root, data):
    revision = data["frozen_revision"]
    require(revision == "7126c0841b008dc89a21edfd008bbf1b748d280f", "wrong frozen revision")
    def git(*parts):
        return subprocess.check_output(["git", "-C", str(root), *parts])
    require(data["lean_tree"] == "69d02281c91fea6ff54fe3556aaddc43eae66e65", "wrong frozen Lean tree")
    require(git("rev-parse", revision+":lean").decode().strip() == data["lean_tree"], "frozen Lean tree differs")
    require(git("rev-parse", "HEAD:lean").decode().strip() == data["lean_tree"], "HEAD Lean tree differs")
    require(subprocess.run(["git", "-C", str(root), "diff", "--quiet", revision, "--", "lean"]).returncode == 0,
            "working Lean tree differs")
    require(not git("ls-files", "--others", "--exclude-standard", "lean").strip(), "additional Lean source")
    for row in data["results"]:
        for ref in row["lean"]:
            payload = git("show", revision+":"+ref["file"])
            require(payload == (root/ref["file"]).read_bytes(), "cited declaration file differs from frozen tree")
            require(ref["name"] in declarations(payload.decode()), "declaration absent at frozen revision")
    require(hashlib.sha256((root/"paper/main.pdf").read_bytes()).hexdigest() == data["pdf_sha256"],
            "published PDF hash differs")
    require({str(p.relative_to(root/"paper")) for p in (root/"paper").iterdir()} == {"main.pdf"},
            "paper directory must contain only main.pdf")


def compile_numbering(root):
    """Compile a temporary copy, labelling only unlabelled results in that copy."""
    inventory, locations = source_inventory(root)
    with tempfile.TemporaryDirectory(prefix="paper-numbering-") as temporary:
        paper = Path(temporary)/"paper"
        shutil.copytree(root/"paper", paper, ignore=shutil.ignore_patterns(".build"))
        for filename in source_files(root):
            path = Path(temporary)/filename
            text = path.read_text()
            counts = {}
            # The published sources have no commented-out numbered environments.
            def instrument(match):
                kind, body = match.groups()
                counts[kind] = counts.get(kind, 0) + 1
                if re.search(r"\\label\s*\{", body):
                    return match.group()
                label = f"mapping:unlabelled:{filename.removeprefix('paper/')}:{kind}:{counts[kind]}"
                opening = match.group().index("}") + 1
                if match.group()[opening:opening+1] == "[":
                    opening = match.group().index("]", opening) + 1
                return match.group()[:opening] + r"\label{" + label + "}" + match.group()[opening:]
            path.write_text(RESULT_RE.sub(instrument, text))
        built = subprocess.run(["bash", str(paper/"build.sh")], stdout=subprocess.PIPE,
                               stderr=subprocess.STDOUT, text=True,
                               env={**os.environ, "OMP_NUM_THREADS":"1", "OPENBLAS_NUM_THREADS":"1",
                                    "MKL_NUM_THREADS":"1", "NUMEXPR_NUM_THREADS":"1"})
        require(built.returncode == 0, "numbering build failed:\n"+built.stdout[-4000:])
        return aux_labels((paper/".build/main.aux").read_text())


def render_tables(data):
    lines = [
        "# Results by paper section", "",
        "Generated from `mapping.json`; edit that file and run `python3 paper-lean-mapping/build_and_check.py --write`.", "",
        "Numbers refer to arXiv:2610.08980v1. Evidence colours refer to the stated formal scope. Dependencies describe the paper argument; each separate Lean route is stated explicitly.", "",
    ]
    for section in dict.fromkeys(row["section"] for row in data["results"]):
        lines += ["## " + section, "",
                  "| Result | Statement and scope | Lean declarations | Exact computation |",
                  "|---|---|---|---|"]
        for row in data["results"]:
            if row["section"] != section:
                continue
            title = (f"[{row['number']}](../paper/main.pdf) — "
                     if row.get("number") and row.get("paper_file") else "")
            grouped = {}
            for ref in row["lean"]:
                grouped.setdefault(ref["role"], []).append(
                    f"[{ref['name']}](../{ref['file']})")
            refs = "<br>".join(", ".join(names) + ": " + role for role, names in grouped.items()) or "No declaration cited."
            checks = "<br>".join(
                f"[{Path(check['script']).name}](#" + Path(check['script']).stem + ")"
                for check in row["checks"]) or (
                    "Numerical observation; no exact check."
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
        data_files = check.get("data_files", [])
        if data_files:
            links = [f"[{Path(name).name}](../{name})" for name in data_files]
            description = ("; ".join(links) if len(links) < 4 else
                           links[0] + "; " + links[1] + " through " + links[-1] + f" ({len(links)-1} certificate files)")
            lines += ["Data: " + description + ".", ""]
        else:
            lines += ["Data: integer witness coefficients and constants are reconstructed in the script; no external data file.", ""]
    lines += ["## Remaining questions", ""] + ["- " + item for item in data["todos"]] + [""]
    return "\n".join(lines)


def render_graphs(data, svg=True):
    rows = data["results"]
    ids = {row["label"]: f"n{i}" for i, row in enumerate(rows)}
    status_ids = {status: f"s{i}" for i, status in enumerate(STATUSES)}
    mermaid = [
        "# Dependency graph",
        "",
        "Arrows record the arXiv v1 paper argument, not Lean proof dependencies. Dashed edges into green nodes use a separate formal route, explained in the section table. Dashed edges into unproved remarks indicate motivation. Green status applies to the formal scope stated in the table. The uniform theorem covers every k >= 16; Lean closes the needed scale k = 4980737 directly. The positive range is a separate branch.",
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
        label = "\n".join(textwrap.wrap(title, 30)) + "\n" + row.get("number", row["label"])
        dot.append(
            f'{identifier} [label={json.dumps(label)}, fillcolor="{STATUSES[row["status"]]}"];'
        )
        mermaid.append(
            f'  {identifier}["{row.get("number", row["label"])}<br/>{title}"]:::{status_ids[row["status"]]}'
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
            else "“Proved in the paper only” includes full statements with formal ingredients of narrower scope. Purple remarks are numerical observations. A definition is not a proof."
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
    """Exercise PDF-page and mapping rejection controls without touching the release."""
    with tempfile.TemporaryDirectory() as temporary:
        root = Path(temporary); (root / "paper").mkdir(); (root / "lean").mkdir(); (root / "verification").mkdir()
        payload = b"Theorem 1.1. Test result."
        fake_pages = ["Theorem 1.1. Test result."] + [""] * 28
        (root / "paper/main.pdf").write_bytes(payload)
        (root / "lean/Test.lean").write_text("namespace Example\ndef present := 0\nend Example\n")
        (root / "verification/test.py").write_text("")
        row = dict(label="thm:test", number="Theorem 1.1", title="Test", statement="Test", section="Test",
                   explanation="Test", scope="Test", kind="theorem", paper_file="paper/main.tex", source_index=1,
                   paper_page=1, pdf_title="", status="Exact-verified", paper_dependencies=[], formal_routes={},
                   lean=[dict(name="Example.present",file="lean/Test.lean",role="definition")],
                   checks=[dict(script="verification/test.py",command="python3 verification/test.py",expected="PASS",scope="Test")])
        base = dict(paper_status="pdf-only", pdf_sha256=hashlib.sha256(payload).hexdigest(), other_labels=[], todos=["Test"], results=[row])
        require(validate(root, base, fake_pages), "PDF mapping positive control")
        for field, value in (("number", "Theorem 9.9"), ("paper_page", 2), ("pdf_title", "Absent title"), ("label", "")):
            bad = copy.deepcopy(base); bad["results"][0][field] = value
            try: validate(root, bad, fake_pages)
            except ValueError: pass
            else: raise ValueError("FAIL: corrupted PDF mapping accepted: " + field)

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


def pdf_text_pages(root):
    pdf = root / "paper/main.pdf"
    require(pdf.is_file(), "missing published PDF")
    text = subprocess.check_output(["pdftotext", "-raw", str(pdf), "-"], text=True,
                                   stderr=subprocess.PIPE)
    pages = text.split("\f")
    if pages and not pages[-1].strip(): pages.pop()
    return pages

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
    immutable_inputs(directory.parent, data)
    pdf_pages = pdf_text_pages(directory.parent)
    has_paper = validate(directory.parent, data, pdf_pages)
    outputs = {"by-section.md": render_tables(data), **render_graphs(data, svg=not args.no_graph)}
    generated_files(directory, outputs, write=args.write)
    print(
        "PASS: mapping, DAG, declarations, scripts, and rejection controls ("
        + ("arXiv numbering and frozen tree checked" if has_paper else "paper pending")
        + ("; SVG skipped" if args.no_graph else "")
        + ")"
    )


if __name__ == "__main__":
    try:
        main()
    except (ValueError, OSError, subprocess.CalledProcessError) as error:
        raise SystemExit(str(error)) from None
