#!/usr/bin/env python3
"""Snapshot real source workloads and measure single-worker analyzer runs."""

import argparse
import hashlib
import json
import platform
import shutil
import subprocess
from collections import Counter
from datetime import datetime, timezone
from pathlib import Path


REPO = Path(__file__).resolve().parent.parent
PROJECTS = Path.home() / "projects"
WORKLOADS = {
    "nogui": PROJECTS / "nogui",
    "skript": PROJECTS / "skript",
    "ocean": PROJECTS / "ocean",
    "zwanzig": REPO,
    "zmath": PROJECTS / "zmath",
    "mon": PROJECTS / "mon",
}
EVENTS = "task-clock:u,cycles:u,instructions:u,branches:u,branch-misses:u,page-faults:u"


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def save_json(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n")


def snapshot(destination):
    destination.mkdir(parents=True, exist_ok=False)
    workloads = {}
    for name, original in WORKLOADS.items():
        source = original / "src"
        paths = sorted(source.rglob("*.zig"))
        if not paths:
            raise ValueError(f"No Zig sources in {source}")
        for filename in ("build.zig", "build.zig.zon", ".zwanzig.json"):
            path = original / filename
            if path.is_file():
                paths.append(path)
        hashes = {}
        for path in paths:
            relative = path.relative_to(original)
            target = destination / name / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            before = digest(path)
            shutil.copyfile(path, target)
            if digest(target) != before or digest(path) != before:
                raise RuntimeError(f"Input changed during snapshot: {path}")
            hashes[str(relative)] = before
        workloads[name] = {"original": str(original), "hashes": hashes}
        print(f"{name}: {sum(p.endswith('.zig') and p.startswith('src/') for p in hashes)} source files", flush=True)
    save_json(destination / "manifest.json", {
        "created_at": datetime.now(timezone.utc).isoformat(),
        "host": platform.uname()._asdict(),
        "workloads": workloads,
    })


def verify_inputs(root, hashes):
    actual = {str(path.relative_to(root)) for path in (root / "src").rglob("*.zig")}
    actual.update(name for name in ("build.zig", "build.zig.zon", ".zwanzig.json") if (root / name).is_file())
    if set(hashes) != actual:
        raise RuntimeError(f"Snapshot membership changed in {root}")
    for relative, expected in hashes.items():
        if digest(root / relative) != expected:
            raise RuntimeError(f"Snapshot changed: {root / relative}")


def verify_config(manifest):
    config = REPO / ".zwanzig.json"
    expected = manifest["workloads"]["zwanzig"]["hashes"].get(".zwanzig.json")
    actual = digest(config) if config.is_file() else None
    if actual != expected:
        raise RuntimeError("Working-directory configuration changed since the snapshot")


def measure(inputs, binary, output, name, workload, profile):
    source = inputs / name
    verify_inputs(source, workload["hashes"])
    destination = output / name
    destination.mkdir(parents=True, exist_ok=False)
    timer = shutil.which("time")
    if timer is None:
        raise RuntimeError("GNU time is required")
    command = ["nice", "-n", "15", "perf"]
    if profile:
        command += ["record", "-F", "99", "--call-graph", "fp", "-o", str(destination / "perf.data")]
    else:
        command += ["stat", "-x", ";", "-e", EVENTS, "-o", str(destination / "perf.stat")]
    command += [
        "--", timer, "-f", '{"wall_s":%e,"user_s":%U,"sys_s":%S,"peak_rss_kib":%M}',
        "-o", str(destination / "time.txt"), str(binary),
        "--threads", "1", "--format", "json", str(source / "src"),
    ]
    print(f"Starting {name}", flush=True)
    with (destination / "diagnostics.json").open("wb") as stdout, (destination / "stderr.txt").open("wb") as stderr:
        completed = subprocess.run(command, cwd=REPO, stdout=stdout, stderr=stderr, timeout=3600)
    if completed.returncode not in (0, 1):
        raise RuntimeError(f"{name} failed with exit {completed.returncode}; see {destination}")
    verify_inputs(source, workload["hashes"])
    diagnostics = json.loads((destination / "diagnostics.json").read_text())
    if diagnostics["total"] != len(diagnostics["diagnostics"]):
        raise RuntimeError(f"Invalid diagnostic total for {name}")
    timing = json.loads((destination / "time.txt").read_text().splitlines()[-1])
    result = {"workload": name, "exit": completed.returncode, "diagnostics": diagnostics["total"], **timing}
    if not profile:
        for line in (destination / "perf.stat").read_text().splitlines():
            fields = line.split(";")
            if len(fields) >= 3 and fields[2] in EVENTS.split(","):
                result[fields[2]] = float(fields[0].replace(",", ""))
    errors = (destination / "stderr.txt").read_text()
    result["limit_warnings"] = [line for line in errors.splitlines() if "analysis limit exceeded" in line or "analysis state limit exceeded" in line]
    save_json(destination / "result.json", result)
    summary = {key: value for key, value in result.items() if key != "limit_warnings"}
    print(json.dumps({**summary, "limit_warnings": len(result["limit_warnings"])}), flush=True)
    return result


def run(args):
    inputs = args.inputs.resolve()
    binary = args.binary.resolve()
    output = args.output.resolve()
    manifest_path = inputs / "manifest.json"
    manifest = json.loads(manifest_path.read_text())
    verify_config(manifest)
    workloads = args.workloads or list(manifest["workloads"])
    binary_hash = digest(binary)
    output.mkdir(parents=True, exist_ok=False)
    version = subprocess.run([str(binary), "--version"], check=True, capture_output=True, text=True).stdout.strip()
    results = {
        "created_at": datetime.now(timezone.utc).isoformat(),
        "binary": str(binary), "binary_sha256": binary_hash, "version": version,
        "inputs": str(inputs), "manifest_sha256": digest(manifest_path),
        "profiled": args.profile, "threads": 1, "nice": 15, "results": [],
    }
    for name in workloads:
        results["results"].append(measure(inputs, binary, output, name, manifest["workloads"][name], args.profile))
        verify_config(manifest)
        if digest(binary) != binary_hash:
            raise RuntimeError("Analyzer executable changed during measurement")
        save_json(output / "results.json", results)


def compare(args):
    before = json.loads((args.before / "results.json").read_text())
    after = json.loads((args.after / "results.json").read_text())
    for key in ("inputs", "manifest_sha256", "version", "profiled", "threads", "nice"):
        if before[key] != after[key]:
            raise ValueError(f"Incomparable runs: {key} differs")
    previous = {row["workload"]: row for row in before["results"]}
    current = {row["workload"]: row for row in after["results"]}
    if previous.keys() != current.keys():
        raise ValueError("Incomparable workload sets")
    for name, old in previous.items():
        new = current[name]
        diagnostics = []
        for directory in (args.before, args.after):
            payload = json.loads((directory / name / "diagnostics.json").read_text())
            diagnostics.append(Counter(json.dumps(item, sort_keys=True) for item in payload["diagnostics"]))
        if diagnostics[0] != diagnostics[1]:
            raise ValueError(f"Diagnostic multiset changed: {name}")
        if old["exit"] != new["exit"] or Counter(old["limit_warnings"]) != Counter(new["limit_warnings"]):
            raise ValueError(f"Completion status or analysis-limit warnings changed: {name}")
        print(json.dumps({
            "workload": name, "diagnostics": new["diagnostics"],
            "cpu_before_s": old["user_s"], "cpu_after_s": new["user_s"],
            "cpu_speedup": old["user_s"] / new["user_s"] if new["user_s"] else None,
            "wall_before_s": old["wall_s"], "wall_after_s": new["wall_s"],
            "rss_before_kib": old["peak_rss_kib"], "rss_after_kib": new["peak_rss_kib"],
            "instructions_before": old.get("instructions:u"),
            "instructions_after": new.get("instructions:u"),
        }))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    capture = commands.add_parser("snapshot", help="freeze all six source workloads")
    capture.add_argument("destination", type=Path)
    execute = commands.add_parser("run", help="measure frozen workloads sequentially")
    execute.add_argument("inputs", type=Path)
    execute.add_argument("binary", type=Path)
    execute.add_argument("output", type=Path)
    execute.add_argument("--workloads", nargs="+", choices=WORKLOADS)
    execute.add_argument("--profile", action="store_true", help="sample call stacks instead of collecting counters")
    comparison = commands.add_parser("compare", help="compare timings with exact diagnostic and limit-warning checks")
    comparison.add_argument("before", type=Path)
    comparison.add_argument("after", type=Path)
    args = parser.parse_args()
    if args.command == "snapshot":
        snapshot(args.destination.resolve())
    elif args.command == "compare":
        compare(args)
    else:
        run(args)


if __name__ == "__main__":
    main()
