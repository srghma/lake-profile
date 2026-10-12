from __future__ import annotations

import argparse
import atexit
import os
import re
import shutil
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Optional

from rich.console import Console
from rich.panel import Panel
from rich.table import Table

from profile_lake.transform import parse_and_transform_lean, revert_transform_lean

console = Console()

ANSI_REGEX = re.compile(r"\x1B(?:[@-Z\\-_]|\[[0-?]*[ -/]*[@-~])")
LAKE_BUILD_TARGET_REGEX = re.compile(r"(?:Building|Compiling)\s+([A-Za-z0-9_.]+)")
TRACE_CMD_REGEX = re.compile(
    r"^(?:(?:info|warning|error):\s+)?(?:(?P<file>[^:\n\r]+):(?P<line>\d+):(?P<col>\d+):\s+)?"
    r"\[Elab\.command\]\s+\[(?P<time>[0-9.]+)\]\s+(?P<cmd>.*)$"
)
TIMEOUT_REGEX = re.compile(
    r"^(?:(?:info|warning|error):\s+)?(?P<file>[^:\n\r]+):(?P<line>\d+):(?P<col>\d+):\s+error:\s+"
    r"\(deterministic\)\s+timeout.*?(?:at\s+'(?P<target>[^']+)')?"
)


@dataclass
class SkippedRecord:
    kind: str
    target: str
    file: str
    line: Optional[int]
    reason: str


MODIFIED_FILES_BACKUP: dict[Path, str] = {}
CURRENT_PROCESS: Optional[subprocess.Popen] = None


def restore_backup_files():
    for path, content in MODIFIED_FILES_BACKUP.items():
        if path.exists():
            path.write_text(content, encoding="utf-8")


def cleanup_on_exit():
    global CURRENT_PROCESS
    if CURRENT_PROCESS and CURRENT_PROCESS.poll() is None:
        try:
            CURRENT_PROCESS.terminate()
            CURRENT_PROCESS.wait(timeout=1.0)
        except Exception:
            CURRENT_PROCESS.kill()
    restore_backup_files()


atexit.register(cleanup_on_exit)


def strip_ansi(text: str) -> str:
    return ANSI_REGEX.sub("", text)


def just_comment_out_expensive(dirs: list[Path], revert: bool = False) -> int:
    """Scans the given directories and comments out (or reverts) expensive commands/theorems."""
    total_scanned = 0
    updated_files = 0
    action_label = "Reverting" if revert else "Commenting out expensive tests in"

    for d in dirs:
        dir_path = Path(d).resolve()
        if not dir_path.exists():
            console.print(f"[bold red]Error:[/bold red] Directory '{d}' does not exist.")
            continue

        console.print(f"[bold cyan]• {action_label}:[/bold cyan] [dim]{dir_path}[/dim]")
        for lean_file in dir_path.rglob("*.lean"):
            if ".lake" in lean_file.parts:
                continue
            total_scanned += 1
            try:
                content = lean_file.read_text(encoding="utf-8")
            except (UnicodeDecodeError, OSError) as e:
                console.print(f"  [red]Failed to read {lean_file}: {e}[/red]")
                continue

            if revert:
                transformed = revert_transform_lean(content)
                changed = transformed != content
            else:
                transformed, changed = parse_and_transform_lean(content)

            if changed:
                try:
                    lean_file.write_text(transformed, encoding="utf-8")
                    updated_files += 1
                    rel = lean_file.relative_to(dir_path) if dir_path in lean_file.parents else lean_file
                    console.print(f"  [green]✓ Updated:[/green] {rel}")
                except OSError as e:
                    console.print(f"  [red]Failed to write {lean_file}: {e}[/red]")

    console.print(f"\n[bold green]Complete![/bold green] Scanned {total_scanned} files, modified {updated_files} files.")
    return 0


def apply_skip_to_project(project_root: Path):
    for lean_file in project_root.rglob("*.lean"):
        if ".lake" in lean_file.parts:
            continue
        try:
            original = lean_file.read_text(encoding="utf-8")
        except UnicodeDecodeError:
            continue

        transformed, changed = parse_and_transform_lean(original)
        if changed:
            MODIFIED_FILES_BACKUP[lean_file] = original
            lean_file.write_text(transformed, encoding="utf-8")


def stub_slow_command(file_path: Path, line_no: int) -> tuple[str, str]:
    if not file_path.exists():
        return "unknown", "file not found"

    if file_path not in MODIFIED_FILES_BACKUP:
        MODIFIED_FILES_BACKUP[file_path] = file_path.read_text(encoding="utf-8")

    lines = file_path.read_text(encoding="utf-8").splitlines(keepends=True)
    if not (1 <= line_no <= len(lines)):
        return "unknown", "invalid line"

    idx = line_no - 1
    target_line = lines[idx]
    cleaned = target_line.strip()

    if cleaned.startswith("#"):
        lines[idx] = f"-- [SKIPPED] {target_line}"
        kind, name = "command", cleaned[:30]
    else:
        lines[idx] = f"{target_line.rstrip()} := by sorry\n"
        kind, name = "declaration", cleaned[:30]

    file_path.write_text("".join(lines), encoding="utf-8")
    return kind, name


def create_lean_wrapper(temp_dir: Path, real_lean: Path, threshold_ms: int, max_heartbeats: Optional[int]) -> Path:
    hb_flag = f"-DmaxHeartbeats={max_heartbeats}" if max_heartbeats else ""
    if os.name == "nt":
        wrapper_path = temp_dir / "lean.bat"
        content = (
            f"@echo off\n"
            f'"{real_lean}" -Dtrace.profiler=true -Dtrace.profiler.threshold={threshold_ms} {hb_flag} %*\n'
        )
        wrapper_path.write_text(content, encoding="utf-8")
    else:
        wrapper_path = temp_dir / "lean"
        content = (
            f"#!/bin/sh\n"
            f'for arg in "$@"; do\n'
            f'    case "$arg" in\n'
            f"        --version|-v|-h|--help|--print-prefix|--print-libdir|--print-githash)\n"
            f'            exec "{real_lean}" "$@"\n'
            f"            ;;\n"
            f"    esac\n"
            f"done\n"
            f'exec "{real_lean}" -Dtrace.profiler=true -Dtrace.profiler.threshold={threshold_ms} {hb_flag} "$@"\n'
        )
        wrapper_path.write_text(content, encoding="utf-8")
        wrapper_path.chmod(0o755)

    return wrapper_path


def main() -> int:
    global CURRENT_PROCESS

    parser = argparse.ArgumentParser(
        description="Profile Lake builds and skip/stub long-running theorems, #eval, #reduce, and #guard."
    )

    # Subparsers for commands
    subparsers = parser.add_subparsers(dest="command")

    comment_parser = subparsers.add_parser(
        "just_comment_out_expensive",
        aliases=["just-comment-out-expensive"],
        help="Comment out expensive tests (#eval, #guard, decide +kernel, kernel_rfl, etc.) in directories",
    )
    comment_parser.add_argument("dirs", nargs="+", type=Path, help="List of directories to transform")
    comment_parser.add_argument("--revert", action="store_true", help="Revert commented-out tests back to normal")

    # Options for profiling builds
    parser.add_argument(
        "--just-comment-out-expensive",
        dest="just_comment_dirs",
        nargs="+",
        type=Path,
        metavar="DIR",
        help="Comment out expensive tests in specified directories and exit",
    )
    parser.add_argument(
        "--revert",
        action="store_true",
        help="Revert commented-out tests back to normal (with --just-comment-out-expensive)",
    )
    parser.add_argument("-t", "--threshold", type=int, default=500, help="Profiler time threshold (ms)")
    parser.add_argument("--clean", action="store_true", help="Run 'lake clean' before building")
    parser.add_argument("--skip-eval-guard", action="store_true", help="Comment out #eval, #reduce, #guard")
    parser.add_argument("--max-heartbeats", type=int, default=None, help="Hard limit on heartbeats (e.g. 200000)")
    parser.add_argument("--auto-skip", action="store_true", help="Auto-stub with 'sorry' on timeout and retry")
    parser.add_argument("--raw", action="store_true", help="Print raw lake output")

    args = parser.parse_args()

    # Handle `just_comment_out_expensive` command
    if args.command in ("just_comment_out_expensive", "just-comment-out-expensive"):
        return just_comment_out_expensive(args.dirs, revert=args.revert)

    if args.just_comment_dirs:
        return just_comment_out_expensive(args.just_comment_dirs, revert=args.revert)

    # Lake build profiler flow
    lake_bin = shutil.which("lake")
    lean_bin = shutil.which("lean")
    if not lake_bin or not lean_bin:
        console.print("[bold red]Error:[/bold red] 'lake' or 'lean' not found.")
        return 1

    if args.clean:
        console.print("[dim]Cleaning build cache ('lake clean')...[/dim]")
        subprocess.run([lake_bin, "clean"], check=False)

    if args.skip_eval_guard:
        console.print("[bold yellow]⊘ Skipping standalone #eval, #reduce, and #guard commands...[/bold yellow]")
        apply_skip_to_project(Path.cwd())

    temp_dir = Path(tempfile.mkdtemp(prefix="lake_profiler_"))
    wrapper = create_lean_wrapper(temp_dir, Path(lean_bin).resolve(), args.threshold, args.max_heartbeats)
    env = os.environ.copy()
    env["LEAN"] = str(wrapper)
    env["PATH"] = f"{temp_dir}{os.pathsep}{env.get('PATH', '')}"

    console.print(
        Panel(
            f"[bold cyan]Lean 4 Build & Skip Profiler[/bold cyan]\n"
            f"• Threshold: [yellow]{args.threshold} ms[/yellow]\n"
            f"• Max Heartbeats: [yellow]{args.max_heartbeats or 'Default'}[/yellow]\n"
            f"• Auto-Skip On Timeout: [green]{args.auto_skip}[/green]",
            expand=False,
        )
    )

    skipped_items: list[SkippedRecord] = []
    max_retries = 10 if args.auto_skip else 1

    try:
        for _ in range(max_retries):
            current_file = "unknown"
            timed_out_command: Optional[tuple[Path, int, str]] = None
            CURRENT_PROCESS = subprocess.Popen(
                [lake_bin, "build"],
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                text=True,
                bufsize=1,
                env=env,
            )

            assert CURRENT_PROCESS.stdout is not None
            for raw_line in CURRENT_PROCESS.stdout:
                if args.raw:
                    sys.stdout.write(raw_line)
                    sys.stdout.flush()

                clean = strip_ansi(raw_line).strip()

                mod_match = LAKE_BUILD_TARGET_REGEX.search(clean)
                if mod_match:
                    current_file = mod_match.group(1).replace(".", "/") + ".lean"
                    if not args.raw:
                        console.print(f"[dim]Building {current_file}...[/dim]")

                to_match = TIMEOUT_REGEX.match(clean)
                if to_match:
                    f_path = Path(to_match.group("file") or current_file)
                    line_no = int(to_match.group("line"))
                    t_name = to_match.group("target") or "unknown"
                    timed_out_command = (f_path, line_no, t_name)

                tr_match = TRACE_CMD_REGEX.match(clean)
                if tr_match:
                    duration_ms = float(tr_match.group("time")) * 1000.0
                    if duration_ms >= args.threshold:
                        cmd = tr_match.group("cmd").strip()
                        loc_file = tr_match.group("file") or current_file
                        line_str = tr_match.group("line")
                        line_no = int(line_str) if line_str else None

                        console.print(f"  ⏱  [yellow]{duration_ms/1000:.2f}s[/yellow] │ {cmd[:50]} [dim]({loc_file}:{line_no})[/dim]")

                        if args.auto_skip and line_no and Path(loc_file).exists():
                            kind, name = stub_slow_command(Path(loc_file), line_no)
                            skipped_items.append(SkippedRecord(kind, name, loc_file, line_no, f"Slow ({duration_ms:.0f}ms)"))

            CURRENT_PROCESS.wait()
            ret = CURRENT_PROCESS.returncode
            CURRENT_PROCESS = None

            if ret == 0:
                console.print("\n[bold green]✓ Build succeeded![/bold green]")
                break

            if args.auto_skip and timed_out_command:
                f_path, line_no, t_name = timed_out_command
                kind, name = stub_slow_command(f_path, line_no)
                console.print(f"[bold red]Timeout at {f_path}:{line_no}[/bold red] → Skipping...")
                skipped_items.append(SkippedRecord(kind, name or t_name, str(f_path), line_no, "Timeout"))
                continue
            else:
                console.print("\n[bold red]Build terminated with errors.[/bold red]")
                return ret

    except KeyboardInterrupt:
        console.print("\n[bold red]Interrupted by user. Cleaning up...[/bold red]")
        cleanup_on_exit()
        return 130

    if skipped_items:
        table = Table(title="Skipped Commands Summary", header_style="bold red")
        table.add_column("Kind", justify="center")
        table.add_column("Target", justify="left")
        table.add_column("Location", justify="left", style="dim")
        for s in skipped_items:
            table.add_row(s.kind, s.target, f"{s.file}:{s.line}")
        console.print()
        console.print(table)

    return 0


if __name__ == "__main__":
    sys.exit(main())
