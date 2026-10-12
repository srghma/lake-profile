from __future__ import annotations

import re
from typing import Optional

SKIP_PREFIX = "-- [SKIPPED BY PROFILE_LAKE] "

# Standalone interactive commands to skip
EVAL_COMMANDS = ("#eval!", "#eval", "#reduce", "#guard_expr", "#guard")

# Tactics that represent evaluation tests for anonymous `example`
EXAMPLE_TEST_TACTICS = ("native_decide", "kernel_rfl", "decide", "rfl")

# Heavy kernel-evaluation tactics in `theorem` / `lemma` (e.g. bounded list exhaustions)
# Note: kernel_rfl is excluded here so named definitional theorems remain available downstream.
HEAVY_THEOREM_TACTIC_PATTERNS = (
    re.compile(r"\bdecide\b[^\n]*\+kernel\b"),
    re.compile(r"\bnative_decide\b"),
)

DECL_MODIFIERS = ("public", "private", "protected", "scoped", "noncomputable", "unsafe", "partial")

DECL_KEYWORDS = (
    "theorem", "lemma", "def", "instance", "example", "inductive",
    "structure", "class", "axiom", "opaque", "abbrev", "variable",
    "open", "import", "export", "namespace", "section", "end",
    "mutual", "initialize", "builtin_initialize", "syntax", "macro",
    "elab", "notation", "infix", "infixl", "infixr", "prefix", "postfix",
    "set_option", "run_meta", "run_cmd", "#check", "#print",
)


def _strip_leading_attributes_and_modifiers(line: str) -> list[str]:
    trimmed = line.strip()
    while trimmed.startswith("@["):
        idx = trimmed.find("]")
        if idx != -1:
            trimmed = trimmed[idx + 1:].strip()
        else:
            break
    parts = trimmed.split()
    while parts and parts[0] in DECL_MODIFIERS:
        parts = parts[1:]
    return parts


def is_example_decl(line: str) -> bool:
    parts = _strip_leading_attributes_and_modifiers(line)
    if not parts:
        return False
    return parts[0] == "example" or parts[0].startswith("example:")


def is_theorem_or_lemma_decl(line: str) -> bool:
    parts = _strip_leading_attributes_and_modifiers(line)
    if not parts:
        return False
    return parts[0] in ("theorem", "lemma")


def uses_heavy_theorem_tactic(block_text: str) -> bool:
    return any(p.search(block_text) for p in HEAVY_THEOREM_TACTIC_PATTERNS)


def is_eval_or_guard_cmd(cmd_text: str) -> bool:
    cleaned = cmd_text.strip()
    return any(
        cleaned == c or cleaned.startswith(f"{c} ") or cleaned.startswith(f"{c}\t") or cleaned.startswith(f"{c}\n")
        for c in EVAL_COMMANDS
    )


def starts_new_top_level_decl(line: str) -> bool:
    trimmed = line.strip()
    if not trimmed:
        return False
    if trimmed.startswith(("/--", "/-", "--", "@[")):
        return True
    return any(
        trimmed == kw or trimmed.startswith(f"{kw} ") or trimmed.startswith(f"{kw}\t")
        for kw in (*DECL_KEYWORDS, *EVAL_COMMANDS, "#guard_msgs")
    )


def find_docstring_and_attr_start(lines: list[str], idx: int) -> int:
    """
    Safely finds the start of a `/-- ... -/` docstring and/or `@[...]` attribute
    immediately preceding `idx`. Never scans past non-doc comments (`/-!` or `/-`).
    """
    curr = idx - 1
    start = idx

    while curr >= 0:
        # Skip empty lines immediately preceding
        while curr >= 0 and not lines[curr].strip():
            curr -= 1
        if curr < 0:
            break

        stripped = lines[curr].strip()

        # Check for docstring (must end with -/)
        if stripped.endswith("-/"):
            doc_curr = curr
            found_doc = False
            # Scan backward ONLY within this comment
            while doc_curr >= 0:
                s = lines[doc_curr].strip()
                if s.startswith("/--"):
                    found_doc = True
                    break
                # If it's a module comment /-! or regular comment /-, STOP: it's not a docstring
                if s.startswith("/-"):
                    break
                doc_curr -= 1

            if found_doc:
                start = doc_curr
                curr = doc_curr - 1
                continue
            else:
                break

        # Check for attributes @[...]
        if stripped.endswith("]"):
            attr_curr = curr
            found_attr = False
            while attr_curr >= 0:
                s = lines[attr_curr].strip()
                if s.startswith("@["):
                    found_attr = True
                    break
                if not s or starts_new_top_level_decl(s):
                    break
                attr_curr -= 1

            if found_attr:
                start = attr_curr
                curr = attr_curr - 1
                continue
            else:
                break

        # If not a docstring or attribute, stop scanning
        break

    return start


def find_matching_brackets(text: str) -> int:
    depth = 0
    in_string = False
    escape = False

    for ch in text:
        if escape:
            escape = False
            continue
        if ch == '\\' and in_string:
            escape = True
            continue
        if ch == '"':
            in_string = not in_string
            continue
        if not in_string:
            if ch in "([{":
                depth += 1
            elif ch in ")]}":
                depth -= 1
    return depth


def _scan_command_end(lines: list[str], start_idx: int) -> int:
    n = len(lines)
    base_indent = len(lines[start_idx]) - len(lines[start_idx].lstrip())
    paren_depth = find_matching_brackets(lines[start_idx])
    curr = start_idx + 1

    while curr < n:
        line = lines[curr]
        stripped = line.strip()

        if not stripped:
            if paren_depth > 0:
                curr += 1
                continue
            lookahead = curr + 1
            while lookahead < n and not lines[lookahead].strip():
                lookahead += 1
            if lookahead < n:
                next_indent = len(lines[lookahead]) - len(lines[lookahead].lstrip())
                if next_indent > base_indent and not starts_new_top_level_decl(lines[lookahead]):
                    curr = lookahead
                    continue
            break

        paren_depth += find_matching_brackets(line)
        line_indent = len(line) - len(line.lstrip())

        if paren_depth <= 0:
            if starts_new_top_level_decl(line) and line_indent <= base_indent:
                break
            if line_indent <= base_indent and curr > start_idx:
                break

        curr += 1

    return curr


def parse_and_transform_lean(source: str) -> tuple[str, bool]:
    lines = source.splitlines(keepends=True)
    n = len(lines)
    blocks_to_skip: list[tuple[int, int]] = []
    i = 0

    while i < n:
        raw_line = lines[i]
        stripped = raw_line.strip()

        if not stripped or stripped.startswith("--") or stripped.startswith("/-"):
            i += 1
            continue

        # 1. Check for `#guard_msgs in #eval`
        if stripped.startswith("#guard_msgs"):
            guard_msgs_line = i
            combined_header = stripped
            header_end = i + 1

            while " in" not in combined_header and header_end < n:
                combined_header += " " + lines[header_end].strip()
                header_end += 1

            match_in = re.search(r"\bin\s+(.*)$", combined_header)
            following_cmd = match_in.group(1).strip() if match_in else ""

            cmd_start_line = header_end - 1
            if not following_cmd and header_end < n:
                following_cmd = lines[header_end].strip()
                cmd_start_line = header_end

            if is_eval_or_guard_cmd(following_cmd):
                block_start = find_docstring_and_attr_start(lines, guard_msgs_line)
                block_end = _scan_command_end(lines, cmd_start_line)
                blocks_to_skip.append((block_start, block_end))
                i = block_end
                continue
            else:
                i = header_end
                continue

        # 2. Check for standalone #eval, #reduce, #guard
        if is_eval_or_guard_cmd(stripped):
            block_start = find_docstring_and_attr_start(lines, i)
            block_end = _scan_command_end(lines, i)
            blocks_to_skip.append((block_start, block_end))
            i = block_end
            continue

        # 3. Check for example tests (native_decide, kernel_rfl, decide, rfl)
        if is_example_decl(stripped):
            block_start = find_docstring_and_attr_start(lines, i)
            block_end = _scan_command_end(lines, i)
            block_text = "".join(lines[block_start:block_end])

            if any(tac in block_text for tac in EXAMPLE_TEST_TACTICS):
                blocks_to_skip.append((block_start, block_end))
                i = block_end
                continue

        # 4. Check for theorems using heavy kernel exhaustion (decide +kernel, native_decide)
        if is_theorem_or_lemma_decl(stripped):
            block_start = find_docstring_and_attr_start(lines, i)
            block_end = _scan_command_end(lines, i)
            block_text = "".join(lines[block_start:block_end])

            if uses_heavy_theorem_tactic(block_text):
                blocks_to_skip.append((block_start, block_end))
                i = block_end
                continue

        i += 1

    if not blocks_to_skip:
        return source, False

    modified_lines = list(lines)
    for start, end in blocks_to_skip:
        for idx in range(start, end):
            if not modified_lines[idx].startswith(SKIP_PREFIX):
                modified_lines[idx] = f"{SKIP_PREFIX}{modified_lines[idx]}"

    return "".join(modified_lines), True


def revert_transform_lean(source: str) -> str:
    lines = source.splitlines(keepends=True)
    restored = [
        line[len(SKIP_PREFIX):] if line.startswith(SKIP_PREFIX) else line
        for line in lines
    ]
    return "".join(restored)
