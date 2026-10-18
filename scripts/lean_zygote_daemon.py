#!/usr/bin/env python3
"""Zygote-style Lean REPL Daemon with Direct Env Resolution, AST Slicer, Multi-Agent Session Isolation, and Instant GC.

Key architectural improvements over baseline `scripts/lean_repl_daemon.py`:
  1. Direct REPL Spawning (No 795 MiB `lake` parent):
     Resolves `lake env env -0` ONCE at daemon startup, caches the environment,
     and spawns `/tmp/lean-repl/.lake/build/bin/repl` directly.
  2. AST-Aware Declaration & Context Extractor (`extract_decl_context`):
     - Parses Lean 4 top-level declarations, comments (`/- ... -/`, `/-- ... -/`),
       attributes (`@[...]`), modifiers (`private`, `set_option ... in`), and
       scopes (`namespace`, `section`, `mutual`, `end`, `open`, `variable`).
     - Snaps arbitrary `--until-line` or target line numbers to clean declaration
       boundaries so it never cuts mid-command or mid-proof.
     - Tracks enclosing `namespace` / `section` / `open` / `variable` / `set_option`
       scopes so isolated `check-decl` calls inside sections (like `section MapChainContext`
       in `Verity/Core.lean`) automatically include their required `variable` declarations.
     - Automatically resolves unbuilt upstream imports (such as `FunctionBody/Base.lean`
       in `Stmt.lean`) by walking the unbuilt `.lean` module graph, collecting `.olean`-backed
       transitive imports, and slicing in only the referenced upstream declarations (with
       upstream theorem proofs stubbed as `:= by sorry`).
  3. Multi-Agent Session Isolation & Header Deduplication:
     - Supports `--agent-id <id>` and `--checkpoint <name>` so multiple concurrent agents
       can load headers and check theorems simultaneously on a single shared `repl` process
       without overwriting each other's `header_env`.
     - Deduplicates identical headers by SHA-256 hash so agents sharing the same file/prefix
       reuse the warm `env` ID in <1 ms.
  4. Instant GC / Checkpoint Recycling (`gc` command & `--max-private-dirty-mb`):
     - Monitors `/proc/<repl_pid>/smaps_rollup` (`Rss`, `Pss`, `Private_Dirty`,
       `Shared_Clean`, `Private_Clean`).
     - Supports on-demand `gc` / `reset-to-checkpoint` and automatic worker recycling
       when `Private_Dirty` exceeds threshold, re-warming named checkpoints automatically.
"""

from __future__ import annotations

import argparse
import fcntl
import hashlib
import json
import os
import re
import signal
import socket
import socketserver
import subprocess
import sys
import threading
import time
from pathlib import Path
from typing import Any

DEFAULT_REPO_ROOT = Path("/var/lib/sandboxed-node/9304baf4-5074-4dad-8c26-2e2896f70f25/verity")
DEFAULT_SOCKET = "/tmp/verity-lean-zygote.sock"
DEFAULT_REPL_BIN = "/tmp/lean-repl/.lake/build/bin/repl"
DEFAULT_ELAN_BIN = "/var/lib/sandboxed-node/caches/elan/bin"
DEFAULT_ELAN_HOME = "/var/lib/sandboxed-node/caches/elan"

DECL_KEYWORDS = {
    "theorem",
    "lemma",
    "def",
    "abbrev",
    "structure",
    "inductive",
    "class",
    "instance",
    "axiom",
    "opaque",
    "example",
}
MODIFIER_KEYWORDS = {
    "private",
    "protected",
    "noncomputable",
    "partial",
    "unsafe",
    "scoped",
    "local",
}
SCOPE_KEYWORDS = {
    "import",
    "namespace",
    "section",
    "mutual",
    "end",
    "open",
    "variable",
    "universe",
    "set_option",
}
IDENT_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_'\?\!]*")


def read_smaps_rollup(pid: int) -> dict[str, int]:
    """Read /proc/<pid>/smaps_rollup metrics in kB."""
    metrics: dict[str, int] = {}
    smaps_path = Path(f"/proc/{pid}/smaps_rollup")
    if not smaps_path.exists():
        return metrics
    try:
        for line in smaps_path.read_text(encoding="utf-8").splitlines():
            parts = line.split()
            if len(parts) >= 2 and parts[0].endswith(":"):
                key = parts[0][:-1]
                try:
                    metrics[key] = int(parts[1])
                except ValueError:
                    pass
    except OSError:
        pass
    return metrics


def resolve_lake_env(cwd: Path, cache_file: Path | None = None) -> dict[str, str]:
    """Resolve `lake env` ONCE and return the environment dict for direct `repl` execution."""
    if cache_file and cache_file.exists():
        try:
            cached = json.loads(cache_file.read_text(encoding="utf-8"))
            if isinstance(cached, dict) and "LEAN_PATH" in cached:
                return cached
        except Exception:
            pass

    base_env = os.environ.copy()
    if DEFAULT_ELAN_BIN not in base_env.get("PATH", ""):
        base_env["PATH"] = f"{DEFAULT_ELAN_BIN}:{base_env.get('PATH', '')}"
    base_env.setdefault("ELAN_HOME", DEFAULT_ELAN_HOME)
    base_env.setdefault("LEAN_NUM_THREADS", str(os.cpu_count() or 4))

    raw = subprocess.check_output(
        ["lake", "env", "env", "-0"],
        cwd=str(cwd),
        env=base_env,
    ).decode("utf-8", errors="replace")

    resolved: dict[str, str] = {}
    for entry in raw.split("\0"):
        if "=" in entry:
            k, v = entry.split("=", 1)
            resolved[k] = v
    resolved.setdefault("LEAN_NUM_THREADS", str(os.cpu_count() or 4))

    if cache_file:
        try:
            cache_file.write_text(json.dumps(resolved), encoding="utf-8")
        except OSError:
            pass
    return resolved


def scan_line_tokens(line: str, block_depth: int) -> tuple[int, int | None, list[str], str]:
    """Track nested `/- ... -/` comments and string literals on a single line."""
    j = 0
    in_str = False
    first_col = None
    code_chars: list[str] = []
    n = len(line)
    while j < n:
        if block_depth > 0:
            if line[j : j + 2] == "/-":
                block_depth += 1
                j += 2
            elif line[j : j + 2] == "-/":
                block_depth -= 1
                j += 2
            else:
                j += 1
        else:
            if in_str:
                code_chars.append(line[j])
                if line[j] == "\\" and j + 1 < n:
                    code_chars.append(line[j + 1])
                    j += 2
                elif line[j] == '"':
                    in_str = False
                    j += 1
                else:
                    j += 1
            else:
                if line[j : j + 2] == "--":
                    break
                elif line[j : j + 2] == "/-":
                    block_depth += 1
                    j += 2
                elif line[j] == '"':
                    if first_col is None:
                        first_col = j
                    in_str = True
                    code_chars.append(line[j])
                    j += 1
                else:
                    if not line[j].isspace() and first_col is None:
                        first_col = j
                    code_chars.append(line[j])
                    j += 1
    code_str = "".join(code_chars)
    return block_depth, first_col, code_str.split(), code_str


def parse_lean_commands(text: str) -> list[dict[str, Any]]:
    """Parse a Lean 4 file into top-level AST commands with full scope tracking."""
    lines = text.splitlines()
    commands: list[dict[str, Any]] = []
    block_depth = 0
    cur_lines: list[str] = []
    cur_start = 1
    cur_kind: str | None = None
    cur_name: str | None = None
    pending_modifier = False

    # Each entry in scope_stack has:
    # {"kind": "namespace"|"section"|"mutual", "name": str, "opens": list[str], "variables": list[str], "options": list[str]}
    root_scope: dict[str, Any] = {
        "kind": "root",
        "name": "",
        "opens": [],
        "variables": [],
        "options": [],
    }
    scope_stack: list[dict[str, Any]] = [root_scope]

    def extract_decl_kind_and_name(tokens: list[str]) -> tuple[str | None, str | None]:
        idx = 0
        while idx < len(tokens):
            t = tokens[idx]
            if t.startswith("@["):
                while idx < len(tokens) and not tokens[idx].endswith("]"):
                    idx += 1
                idx += 1
                continue
            if t in MODIFIER_KEYWORDS:
                idx += 1
                continue
            break
        if idx >= len(tokens):
            return None, None
        kw = tokens[idx]
        if kw in DECL_KEYWORDS:
            name = None
            if idx + 1 < len(tokens):
                raw_name = tokens[idx + 1]
                name = re.split(r"[\(\{\[\:]", raw_name)[0]
            return kw, name
        if kw in SCOPE_KEYWORDS:
            arg = " ".join(tokens[idx + 1 :]) if idx + 1 < len(tokens) else ""
            return kw, arg
        return None, None

    def flush(end_line: int) -> None:
        nonlocal cur_lines, cur_kind, cur_name
        if cur_lines and cur_kind is not None:
            cmd_text = "\n".join(cur_lines)
            ns_parts = [s["name"] for s in scope_stack if s["kind"] == "namespace" and s["name"]]
            qual = (
                ".".join(ns_parts + ([cur_name] if cur_name else []))
                if cur_kind in DECL_KEYWORDS
                else cur_name
            )
            active_scopes = [
                (s["kind"], s["name"])
                for s in scope_stack
                if s["kind"] in ("namespace", "section")
            ]
            active_opens = [op for s in scope_stack for op in s["opens"]]
            active_variables = [v for s in scope_stack for v in s["variables"]]
            active_options = [opt for s in scope_stack for opt in s["options"]]

            commands.append(
                {
                    "kind": cur_kind,
                    "name": cur_name,
                    "qualified_name": qual,
                    "start_line": cur_start,
                    "end_line": end_line,
                    "text": cmd_text,
                    "scopes": active_scopes,
                    "opens": active_opens,
                    "variables": active_variables,
                    "options": active_options,
                }
            )
            if cur_kind in ("namespace", "section", "mutual"):
                scope_stack.append(
                    {
                        "kind": cur_kind,
                        "name": cur_name or "",
                        "opens": [],
                        "variables": [],
                        "options": [],
                    }
                )
            elif cur_kind == "end":
                if len(scope_stack) > 1:
                    scope_stack.pop()
            elif cur_kind == "open" and cur_name:
                scope_stack[-1]["opens"].append(cmd_text.strip())
            elif cur_kind == "variable" and cur_name:
                scope_stack[-1]["variables"].append(cmd_text.strip())
            elif cur_kind == "set_option" and cur_name:
                scope_stack[-1]["options"].append(cmd_text.strip())

            cur_lines = []
            cur_kind = None
            cur_name = None

    for lineno, line in enumerate(lines, 1):
        prev_depth = block_depth
        is_doc_comment_start = prev_depth == 0 and line.startswith("/--")
        block_depth, first_col, tokens, _ = scan_line_tokens(line, block_depth)
        if is_doc_comment_start:
            if not pending_modifier and cur_lines and cur_kind is not None:
                flush(lineno - 1)
            if not cur_lines:
                cur_start = lineno
            pending_modifier = True
            cur_lines.append(line)
            continue

        if prev_depth == 0 and first_col == 0 and tokens:
            first_tok = tokens[0]
            is_attr_only = first_tok.startswith("@[") and not any(
                t in DECL_KEYWORDS for t in tokens
            )
            is_set_option_in = first_tok == "set_option" and tokens[-1] == "in"
            is_mod_only = first_tok in MODIFIER_KEYWORDS and not any(
                t in DECL_KEYWORDS for t in tokens
            )

            if not pending_modifier and cur_lines and cur_kind is not None:
                flush(lineno - 1)

            if not cur_lines:
                cur_start = lineno

            if is_attr_only or is_set_option_in or is_mod_only:
                pending_modifier = True
                cur_lines.append(line)
                continue
            else:
                pending_modifier = False
                k, nm = extract_decl_kind_and_name(tokens)
                if k is not None:
                    cur_kind = k
                    cur_name = nm
                cur_lines.append(line)
        else:
            if not cur_lines:
                cur_start = lineno
            cur_lines.append(line)

    flush(len(lines))
    return commands


def stub_theorem(text: str) -> str:
    """Replace the top-level proof `:= ...` of a theorem/lemma with `:= by sorry`."""
    depth = 0
    in_str = False
    block_depth = 0
    i = 0
    n = len(text)
    while i < n:
        if block_depth > 0:
            if text[i : i + 2] == "/-":
                block_depth += 1
                i += 2
            elif text[i : i + 2] == "-/":
                block_depth -= 1
                i += 2
            else:
                i += 1
            continue
        ch = text[i]
        if in_str:
            if ch == "\\" and i + 1 < n:
                i += 2
                continue
            elif ch == '"':
                in_str = False
        else:
            if text[i : i + 2] == "/-":
                block_depth += 1
                i += 2
                continue
            elif text[i : i + 2] == "--":
                nl = text.find("\n", i)
                if nl == -1:
                    break
                i = nl + 1
                continue
            elif ch == '"':
                in_str = True
            elif ch in "([{":
                depth += 1
            elif ch in ")]}":
                depth = max(0, depth - 1)
            elif depth == 0 and text[i : i + 2] == ":=":
                return text[:i] + ":= by sorry"
        i += 1
    return text


def has_olean_in_paths(mod_name: str, lean_paths: list[Path]) -> bool:
    rel = Path(*mod_name.split(".")).with_suffix(".olean")
    return any((lp / rel).exists() for lp in lean_paths)


def resolve_unbuilt_imports_and_decls(
    cmds: list[dict[str, Any]],
    target_snippets: list[str],
    repo_root: Path,
    lean_paths: list[Path],
) -> tuple[list[str], list[str]]:
    """Resolve `import` statements, replacing unbuilt modules with their `.olean`-backed
    transitive imports plus AST-sliced upstream definitions and stubbed theorems."""
    built_imports: list[str] = []
    unbuilt_modules: list[tuple[str, list[dict[str, Any]]]] = []
    visited: set[str] = set()

    def walk_mod(mod_name: str) -> None:
        if mod_name in visited:
            return
        visited.add(mod_name)
        if not lean_paths or has_olean_in_paths(mod_name, lean_paths):
            if mod_name not in built_imports:
                built_imports.append(mod_name)
            return
        src = repo_root / Path(*mod_name.split(".")).with_suffix(".lean")
        if not src.exists():
            if mod_name not in built_imports:
                built_imports.append(mod_name)
            return
        m_cmds = parse_lean_commands(src.read_text(encoding="utf-8"))
        for c in m_cmds:
            if c["kind"] == "import" and c["name"]:
                for sub_mod in c["name"].split():
                    walk_mod(sub_mod)
        unbuilt_modules.append((mod_name, m_cmds))

    for c in cmds:
        if c["kind"] == "import" and c["name"]:
            for mod_name in c["name"].split():
                walk_mod(mod_name)

    if not unbuilt_modules:
        return [f"import {m}" for m in built_imports], []

    decl_index: dict[str, list[tuple[int, int, dict[str, Any]]]] = {}
    for m_idx, (_mod_name, m_cmds) in enumerate(unbuilt_modules):
        for c_idx, c in enumerate(m_cmds):
            if c["kind"] in DECL_KEYWORDS and c["name"]:
                short = c["name"].split(".")[-1]
                decl_index.setdefault(short, []).append((m_idx, c_idx, c))

    needed: set[tuple[int, int]] = set()
    queue: set[str] = set()
    for snip in target_snippets:
        for tok in IDENT_RE.findall(snip):
            if tok in decl_index:
                queue.add(tok)

    seen_tokens: set[str] = set()
    while queue:
        tok = queue.pop()
        if tok in seen_tokens:
            continue
        seen_tokens.add(tok)
        for m_idx, c_idx, c in decl_index.get(tok, []):
            if (m_idx, c_idx) not in needed:
                needed.add((m_idx, c_idx))
                body_text = (
                    stub_theorem(c["text"]) if c["kind"] in ("theorem", "lemma") else c["text"]
                )
                for sub_tok in IDENT_RE.findall(body_text):
                    if sub_tok in decl_index and sub_tok not in seen_tokens:
                        queue.add(sub_tok)

    sliced_blocks: list[str] = []
    for m_idx, (_mod_name, m_cmds) in enumerate(unbuilt_modules):
        mod_indices = sorted(c_idx for (mi, c_idx) in needed if mi == m_idx)
        if not mod_indices:
            continue
        for c_idx in mod_indices:
            c = m_cmds[c_idx]
            body = stub_theorem(c["text"]) if c["kind"] in ("theorem", "lemma") else c["text"]
            ns_open = "\n".join(
                f"namespace {nm}" for k, nm in c["scopes"] if k == "namespace" and nm
            )
            opens = "\n".join(c["opens"])
            vars_text = "\n".join(c["variables"])
            ns_close = "\n".join(
                f"end {nm}" for k, nm in reversed(c["scopes"]) if k == "namespace" and nm
            )
            parts = [p for p in (ns_open, opens, vars_text, body, ns_close) if p]
            sliced_blocks.append("\n".join(parts))

    return [f"import {m}" for m in built_imports], sliced_blocks


def find_target_decl(
    cmds: list[dict[str, Any]], decl_name_or_line: str | int
) -> tuple[int, dict[str, Any]]:
    """Locate a declaration command by name (short or qualified) or 1-based line number."""
    line_num: int | None = None
    if isinstance(decl_name_or_line, int):
        line_num = decl_name_or_line
    elif isinstance(decl_name_or_line, str) and decl_name_or_line.isdigit():
        line_num = int(decl_name_or_line)

    if line_num is not None:
        # First look for a declaration containing line_num
        for idx, c in enumerate(cmds):
            if c["start_line"] <= line_num <= c["end_line"] and c["kind"] in DECL_KEYWORDS:
                return idx, c
        # Or the first declaration starting at or after line_num
        for idx, c in enumerate(cmds):
            if c["start_line"] >= line_num and c["kind"] in DECL_KEYWORDS:
                return idx, c
        # Or the last declaration before line_num
        for idx in range(len(cmds) - 1, -1, -1):
            if cmds[idx]["start_line"] <= line_num and cmds[idx]["kind"] in DECL_KEYWORDS:
                return idx, cmds[idx]
        raise ValueError(f"No declaration found near line {line_num}")

    target_str = str(decl_name_or_line).strip()
    for idx, c in enumerate(cmds):
        if c["kind"] in DECL_KEYWORDS and (
            c["name"] == target_str
            or c["qualified_name"] == target_str
            or (c["qualified_name"] and c["qualified_name"].endswith("." + target_str))
        ):
            return idx, c
    raise ValueError(f"Declaration '{target_str}' not found")


def extract_decl_context(
    file_path: Path,
    decl_name_or_line: str | int,
    repo_root: Path = DEFAULT_REPO_ROOT,
    lean_paths: list[Path] | None = None,
    stub_prefix_theorems: bool = False,
) -> dict[str, Any]:
    """AST-aware declaration & context extractor.

    Returns a dictionary containing:
      - `header_and_prefix`: Complete valid Lean code for imports + all commands strictly
        before the target declaration (never cutting mid-command).
      - `scope_wrapped_decl`: The target declaration wrapped in its active `section`/`variable`
        context (so even if `header_env` was loaded before the enclosing `section`,
        checking `scope_wrapped_decl` succeeds without losing `variable` declarations).
      - `standalone_scope_context`: Imports + only active `set_option`/`namespace`/`open`/`section`/`variable`
        headers + the target declaration + closing `end` statements.
      - `decl_text`: Exact source text of the target declaration.
      - `decl_name`, `qualified_name`, `kind`, `start_line`, `end_line`, `scopes`, `variables`.
    """
    text = file_path.read_text(encoding="utf-8")
    cmds = parse_lean_commands(text)
    target_idx, target_cmd = find_target_decl(cmds, decl_name_or_line)

    prefix_non_import: list[str] = []
    for c in cmds[:target_idx]:
        if c["kind"] == "import":
            continue
        if stub_prefix_theorems and c["kind"] in ("theorem", "lemma"):
            prefix_non_import.append(stub_theorem(c["text"]))
        else:
            prefix_non_import.append(c["text"])

    snippets_for_slicing = prefix_non_import + [target_cmd["text"]]
    imports, sliced_upstream = resolve_unbuilt_imports_and_decls(
        cmds,
        snippets_for_slicing,
        repo_root=repo_root,
        lean_paths=lean_paths or [],
    )

    header_parts: list[str] = []
    if imports:
        header_parts.append("\n".join(imports))
    if sliced_upstream:
        header_parts.append("\n\n".join(sliced_upstream))
    if prefix_non_import:
        header_parts.append("\n\n".join(prefix_non_import))
    header_and_prefix = "\n\n".join(header_parts)

    # Active section variables that apply to target_cmd
    vars_in_scope = "\n".join(target_cmd["variables"])
    if vars_in_scope:
        scope_wrapped_decl = (
            f"section\n{vars_in_scope}\n{target_cmd['text']}\nend"
        )
    else:
        scope_wrapped_decl = target_cmd["text"]

    # Standalone scope-only wrapper (imports + options + namespaces + opens + variables + decl + ends)
    opts_text = "\n".join(target_cmd["options"])
    ns_open = "\n".join(
        f"{k} {nm}".strip() for k, nm in target_cmd["scopes"]
    )
    opens_text = "\n".join(target_cmd["opens"])
    ns_close = "\n".join(
        f"end {nm}".strip() for _k, nm in reversed(target_cmd["scopes"])
    )
    standalone_parts = [
        p
        for p in (
            "\n".join(imports),
            "\n\n".join(sliced_upstream),
            opts_text,
            ns_open,
            opens_text,
            vars_in_scope,
            target_cmd["text"],
            ns_close,
        )
        if p
    ]

    return {
        "file": str(file_path),
        "decl_name": target_cmd["name"],
        "qualified_name": target_cmd["qualified_name"],
        "kind": target_cmd["kind"],
        "start_line": target_cmd["start_line"],
        "end_line": target_cmd["end_line"],
        "scopes": target_cmd["scopes"],
        "opens": target_cmd["opens"],
        "variables": target_cmd["variables"],
        "options": target_cmd["options"],
        "decl_text": target_cmd["text"],
        "scope_wrapped_decl": scope_wrapped_decl,
        "header_and_prefix": header_and_prefix,
        "standalone_scope_context": "\n\n".join(standalone_parts),
        "built_imports_count": len(imports),
        "sliced_upstream_decls_count": len(sliced_upstream),
    }


def extract_ast_header_prefix(
    file_path: Path,
    until_line: int | None,
    until_decl: str | int | None,
    repo_root: Path,
    lean_paths: list[Path],
    stub_prefix_theorems: bool = False,
) -> tuple[str, dict[str, Any]]:
    """Extract an AST-clean header or prefix up to `until_decl` or snapped `until_line`."""
    if until_decl is not None:
        ctx = extract_decl_context(
            file_path,
            until_decl,
            repo_root=repo_root,
            lean_paths=lean_paths,
            stub_prefix_theorems=stub_prefix_theorems,
        )
        return ctx["header_and_prefix"], {
            "snapped_before_decl": ctx["decl_name"],
            "snapped_before_line": ctx["start_line"],
            "built_imports_count": ctx["built_imports_count"],
            "sliced_upstream_decls_count": ctx["sliced_upstream_decls_count"],
        }

    text = file_path.read_text(encoding="utf-8")
    cmds = parse_lean_commands(text)

    if until_line is not None:
        # Snap until_line so we NEVER cut inside a declaration!
        # Keep only complete commands that end <= until_line, OR if until_line falls inside
        # a declaration, stop strictly before that declaration!
        kept_cmds: list[dict[str, Any]] = []
        snapped_decl = None
        snapped_line = until_line
        for c in cmds:
            if c["kind"] == "import":
                kept_cmds.append(c)
                continue
            if c["end_line"] <= until_line:
                kept_cmds.append(c)
            elif c["start_line"] <= until_line <= c["end_line"]:
                if c["kind"] in ("namespace", "section", "open", "variable", "set_option"):
                    kept_cmds.append(c)
                else:
                    snapped_decl = c["name"]
                    snapped_line = c["start_line"] - 1
                    break
            else:
                break
    else:
        # Default header: include imports + top-level set_option/namespace/open/variable before first decl
        kept_cmds = []
        snapped_decl = None
        snapped_line = 0
        for c in cmds:
            if c["kind"] in ("import", "set_option", "namespace", "section", "open", "variable", "universe"):
                kept_cmds.append(c)
                snapped_line = c["end_line"]
            else:
                snapped_decl = c["name"]
                break

    non_import_texts: list[str] = []
    for c in kept_cmds:
        if c["kind"] == "import":
            continue
        if stub_prefix_theorems and c["kind"] in ("theorem", "lemma"):
            non_import_texts.append(stub_theorem(c["text"]))
        else:
            non_import_texts.append(c["text"])

    # Also include all commands in the file when resolving unbuilt imports if until_line is None
    all_snippets = [c["text"] for c in cmds if c["kind"] != "import"]
    imports, sliced_upstream = resolve_unbuilt_imports_and_decls(
        cmds,
        non_import_texts if non_import_texts else all_snippets[:25],
        repo_root=repo_root,
        lean_paths=lean_paths,
    )

    parts = [p for p in ("\n".join(imports), "\n\n".join(sliced_upstream), "\n\n".join(non_import_texts)) if p]
    return "\n\n".join(parts), {
        "snapped_before_decl": snapped_decl,
        "snapped_line": snapped_line,
        "built_imports_count": len(imports),
        "sliced_upstream_decls_count": len(sliced_upstream),
    }


def read_repl_response(stdout) -> dict[str, Any]:
    lines: list[str] = []
    while True:
        line = stdout.readline()
        if not line:
            if not lines:
                raise EOFError("REPL process closed stdout unexpectedly")
            break
        if line in ("\n", "\r\n"):
            if lines:
                break
            continue
        lines.append(line)
    raw = "".join(lines).strip()
    return json.loads(raw)


def has_error_messages(resp: dict[str, Any]) -> bool:
    if "error" in resp:
        return True
    for msg in resp.get("messages", []):
        if msg.get("severity") == "error":
            return True
    if "message" in resp and "env" not in resp and "proofState" not in resp:
        return True
    return False


class ZygoteDaemonState:
    def __init__(
        self,
        repl_bin: Path,
        cwd: Path,
        resolved_env: dict[str, str],
        max_private_dirty_mb: float = 0.0,
    ) -> None:
        self.repl_bin = repl_bin
        self.cwd = cwd
        self.resolved_env = resolved_env
        self.lean_paths = [
            Path(p) for p in resolved_env.get("LEAN_PATH", "").split(":") if p
        ]
        self.max_private_dirty_kb = (
            int(max_private_dirty_mb * 1024) if max_private_dirty_mb > 0 else 0
        )
        self.lock = threading.RLock()
        self.proc: subprocess.Popen[str] = self._spawn_repl()
        self.header_env: int | None = None
        self.last_env: int | None = None
        # Named checkpoints: checkpoint_name -> {"env": int, "cmd": str, "sha256": str}
        self.checkpoints: dict[str, dict[str, Any]] = {}
        # Deduplicated header cache: sha256(cmd) -> env_id
        self.header_cache: dict[str, int] = {}
        # Multi-agent isolated sessions: agent_id -> {"header_env": int | None, "last_env": int | None, "checkpoint": str | None, "checks": int}
        self.sessions: dict[str, dict[str, Any]] = {}
        self.gc_count = 0

    def _spawn_repl(self) -> subprocess.Popen[str]:
        return subprocess.Popen(
            [str(self.repl_bin)],
            cwd=str(self.cwd),
            env=self.resolved_env,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.DEVNULL,
            text=True,
            bufsize=1,
        )

    def get_session(self, agent_id: str) -> dict[str, Any]:
        if agent_id not in self.sessions:
            self.sessions[agent_id] = {
                "header_env": self.header_env,
                "last_env": self.last_env,
                "checkpoint": None,
                "checks": 0,
            }
        return self.sessions[agent_id]

    def send_raw(self, payload: dict[str, Any]) -> tuple[dict[str, Any], float]:
        with self.lock:
            for attempt in range(2):
                if self.proc.poll() is not None:
                    self.proc = self._spawn_repl()
                t0 = time.perf_counter()
                try:
                    assert self.proc.stdin is not None and self.proc.stdout is not None
                    stanza = json.dumps(payload) + "\n\n"
                    self.proc.stdin.write(stanza)
                    self.proc.stdin.flush()
                    resp = read_repl_response(self.proc.stdout)
                    dt_ms = (time.perf_counter() - t0) * 1000.0
                    return resp, dt_ms
                except (EOFError, BrokenPipeError):
                    if self.proc.poll() is None:
                        self.proc.kill()
                        self.proc.wait()
                    if attempt == 0 and "env" not in payload and "proofState" not in payload:
                        self.proc = self._spawn_repl()
                        continue
                    raise
            raise RuntimeError("Unreachable")

    def recycle_and_rewarm(self, checkpoints_to_keep: list[str] | None = None) -> dict[str, Any]:
        """Recycle the direct REPL process to reclaim all Private_Dirty heap pages and re-warm checkpoints."""
        with self.lock:
            before_pid = self.proc.pid
            before_smaps = read_smaps_rollup(before_pid)
            saved_checkpoints = dict(self.checkpoints)
            if checkpoints_to_keep is not None:
                saved_checkpoints = {
                    k: v for k, v in saved_checkpoints.items() if k in checkpoints_to_keep
                }

            if self.proc.poll() is None:
                self.proc.terminate()
                try:
                    self.proc.wait(timeout=3)
                except subprocess.TimeoutExpired:
                    self.proc.kill()

            self.proc = self._spawn_repl()
            self.header_cache.clear()
            self.checkpoints.clear()
            self.header_env = None
            self.last_env = None
            self.gc_count += 1

            rewarmed: dict[str, int] = {}
            for cp_name, cp_info in saved_checkpoints.items():
                cmd_text = cp_info["cmd"]
                digest = cp_info["sha256"]
                if digest in self.header_cache:
                    env_id = self.header_cache[digest]
                else:
                    resp, _ = self.send_raw({"cmd": cmd_text})
                    env_id = resp.get("env", 0)
                    self.header_cache[digest] = env_id
                self.checkpoints[cp_name] = {
                    "env": env_id,
                    "cmd": cmd_text,
                    "sha256": digest,
                }
                rewarmed[cp_name] = env_id
                self.header_env = env_id
                self.last_env = env_id

            for _agent_id, sess in self.sessions.items():
                cp_name = sess.get("checkpoint")
                if cp_name and cp_name in rewarmed:
                    sess["header_env"] = rewarmed[cp_name]
                    sess["last_env"] = rewarmed[cp_name]
                else:
                    sess["header_env"] = self.header_env
                    sess["last_env"] = self.last_env

            after_smaps = read_smaps_rollup(self.proc.pid)
            return {
                "ok": True,
                "gc_count": self.gc_count,
                "old_repl_pid": before_pid,
                "new_repl_pid": self.proc.pid,
                "before_smaps_kb": before_smaps,
                "after_smaps_kb": after_smaps,
                "rewarmed_checkpoints": rewarmed,
            }

    def maybe_auto_gc(self) -> dict[str, Any] | None:
        if self.max_private_dirty_kb <= 0:
            return None
        smaps = read_smaps_rollup(self.proc.pid)
        priv_dirty = smaps.get("Private_Dirty", 0)
        if priv_dirty > self.max_private_dirty_kb:
            return self.recycle_and_rewarm()
        return None


class ThreadedUnixStreamServer(socketserver.ThreadingMixIn, socketserver.UnixStreamServer):
    daemon_threads = True
    allow_reuse_address = True


def serve_daemon(
    socket_path: Path,
    repl_bin: Path,
    cwd: Path,
    max_private_dirty_mb: float = 0.0,
) -> int:
    socket_path.parent.mkdir(parents=True, exist_ok=True)
    lock_path = Path(f"{socket_path}.lock")
    lock_fd = os.open(str(lock_path), os.O_CREAT | os.O_RDWR, 0o600)
    try:
        fcntl.flock(lock_fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except OSError:
        os.close(lock_fd)
        return 0

    if socket_path.exists():
        socket_path.unlink(missing_ok=True)

    env_cache_path = Path(f"{socket_path}.env.json")
    resolved_env = resolve_lake_env(cwd, cache_file=env_cache_path)
    state = ZygoteDaemonState(
        repl_bin=repl_bin,
        cwd=cwd,
        resolved_env=resolved_env,
        max_private_dirty_mb=max_private_dirty_mb,
    )

    class Handler(socketserver.BaseRequestHandler):
        def handle(self) -> None:
            data = b""
            while True:
                chunk = self.request.recv(65536)
                if not chunk:
                    break
                data += chunk
            if not data:
                return
            try:
                req = json.loads(data.decode("utf-8"))
            except Exception as exc:
                self.request.sendall(
                    json.dumps({"error": f"invalid JSON: {exc}"}).encode("utf-8")
                )
                return

            action = req.get("action", "send")
            agent_id = req.get("agent_id") or "default"

            if action == "status":
                with state.lock:
                    repl_smaps = read_smaps_rollup(state.proc.pid)
                    daemon_smaps = read_smaps_rollup(os.getpid())
                    sess = state.get_session(agent_id)
                    resp = {
                        "ok": state.proc.poll() is None,
                        "daemon_pid": os.getpid(),
                        "repl_pid": state.proc.pid,
                        "direct_repl_no_lake_parent": True,
                        "agent_id": agent_id,
                        "agent_header_env": sess["header_env"],
                        "agent_last_env": sess["last_env"],
                        "global_header_env": state.header_env,
                        "global_last_env": state.last_env,
                        "checkpoints": {
                            k: v["env"] for k, v in state.checkpoints.items()
                        },
                        "active_sessions": {
                            k: {
                                "header_env": v["header_env"],
                                "last_env": v["last_env"],
                                "checkpoint": v["checkpoint"],
                                "checks": v["checks"],
                            }
                            for k, v in state.sessions.items()
                        },
                        "gc_count": state.gc_count,
                        "repl_smaps_kb": repl_smaps,
                        "daemon_smaps_kb": daemon_smaps,
                    }
                self.request.sendall(json.dumps(resp).encode("utf-8"))
                return

            if action == "gc":
                keep = req.get("keep_checkpoints")
                resp = state.recycle_and_rewarm(checkpoints_to_keep=keep)
                self.request.sendall(json.dumps(resp).encode("utf-8"))
                return

            if action == "stop":
                with state.lock:
                    if state.proc.poll() is None:
                        state.proc.terminate()
                        try:
                            state.proc.wait(timeout=3)
                        except subprocess.TimeoutExpired:
                            state.proc.kill()
                self.request.sendall(
                    json.dumps({"ok": True, "stopped": True}).encode("utf-8")
                )
                threading.Thread(target=server.shutdown, daemon=True).start()
                return

            if action == "load_header":
                payload = req.get("payload", {})
                cmd_text = payload.get("cmd", "")
                checkpoint_name = req.get("checkpoint") or f"cp_{agent_id}"
                deduplicate = bool(req.get("deduplicate", True))
                digest = hashlib.sha256(cmd_text.encode("utf-8")).hexdigest()

                with state.lock:
                    sess = state.get_session(agent_id)
                    if deduplicate and digest in state.header_cache and payload.get("env") is None:
                        env_id = state.header_cache[digest]
                        sess["header_env"] = env_id
                        sess["last_env"] = env_id
                        sess["checkpoint"] = checkpoint_name
                        state.header_env = env_id
                        state.last_env = env_id
                        state.checkpoints[checkpoint_name] = {
                            "env": env_id,
                            "cmd": cmd_text,
                            "sha256": digest,
                        }
                        self.request.sendall(
                            json.dumps(
                                {
                                    "env": env_id,
                                    "deduplicated": True,
                                    "agent_id": agent_id,
                                    "checkpoint": checkpoint_name,
                                    "elapsed_ms": 0.05,
                                }
                            ).encode("utf-8")
                        )
                        return

                    repl_resp, dt_ms = state.send_raw(payload)
                    if "env" in repl_resp and not has_error_messages(repl_resp):
                        env_id = repl_resp["env"]
                        state.header_cache[digest] = env_id
                        state.header_env = env_id
                        state.last_env = env_id
                        sess["header_env"] = env_id
                        sess["last_env"] = env_id
                        sess["checkpoint"] = checkpoint_name
                        state.checkpoints[checkpoint_name] = {
                            "env": env_id,
                            "cmd": cmd_text,
                            "sha256": digest,
                        }
                    repl_resp["deduplicated"] = False
                    repl_resp["agent_id"] = agent_id
                    repl_resp["checkpoint"] = checkpoint_name
                    repl_resp["elapsed_ms"] = round(dt_ms, 2)
                self.request.sendall(json.dumps(repl_resp).encode("utf-8"))
                return

            # Default action == "send" / "check"
            payload = req.get("payload")
            if not isinstance(payload, dict):
                self.request.sendall(
                    json.dumps({"error": "missing dict payload"}).encode("utf-8")
                )
                return

            with state.lock:
                sess = state.get_session(agent_id)
                checkpoint_name = req.get("checkpoint")
                if "env" not in payload and "proofState" not in payload:
                    if checkpoint_name and checkpoint_name in state.checkpoints:
                        payload["env"] = state.checkpoints[checkpoint_name]["env"]
                    elif sess["header_env"] is not None:
                        payload["env"] = sess["header_env"]
                    elif state.header_env is not None:
                        payload["env"] = state.header_env

                try:
                    repl_resp, dt_ms = state.send_raw(payload)
                except Exception as exc:
                    self.request.sendall(
                        json.dumps({"error": f"REPL communication error: {exc}"}).encode("utf-8")
                    )
                    return

                sess["checks"] += 1
                if "env" in repl_resp and not has_error_messages(repl_resp):
                    sess["last_env"] = repl_resp["env"]
                    state.last_env = repl_resp["env"]
                    if req.get("mark_header"):
                        sess["header_env"] = repl_resp["env"]
                        state.header_env = repl_resp["env"]

                auto_gc_info = state.maybe_auto_gc()
                repl_resp["agent_id"] = agent_id
                repl_resp["used_base_env"] = payload.get("env")
                repl_resp["elapsed_ms"] = round(dt_ms, 2)
                if auto_gc_info is not None:
                    repl_resp["auto_gc"] = auto_gc_info

            self.request.sendall(json.dumps(repl_resp).encode("utf-8"))

    server = ThreadedUnixStreamServer(str(socket_path), Handler)
    os.chmod(socket_path, 0o600)

    def cleanup(*_args: Any) -> None:
        try:
            server.server_close()
        except OSError:
            pass
        if socket_path.exists():
            try:
                socket_path.unlink()
            except OSError:
                pass
        if state.proc.poll() is None:
            state.proc.terminate()
            try:
                state.proc.wait(timeout=3)
            except subprocess.TimeoutExpired:
                state.proc.kill()
        try:
            fcntl.flock(lock_fd, fcntl.LOCK_UN)
            os.close(lock_fd)
        except OSError:
            pass
        sys.exit(0)

    signal.signal(signal.SIGTERM, cleanup)
    signal.signal(signal.SIGINT, cleanup)

    try:
        server.serve_forever()
    finally:
        cleanup()


def request_daemon(
    socket_path: Path, message: dict[str, Any], timeout: float = 300.0
) -> dict[str, Any]:
    if not socket_path.exists():
        raise FileNotFoundError(
            f"Zygote REPL socket {socket_path} does not exist. Run `lean_zygote_daemon.py start` first."
        )
    client = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    client.settimeout(timeout)
    with client:
        client.connect(str(socket_path))
        client.sendall(json.dumps(message).encode("utf-8"))
        client.shutdown(socket.SHUT_WR)
        chunks: list[bytes] = []
        while True:
            chunk = client.recv(65536)
            if not chunk:
                break
            chunks.append(chunk)
    return json.loads(b"".join(chunks).decode("utf-8"))


def cmd_start(args: argparse.Namespace) -> int:
    socket_path = Path(args.socket)
    if socket_path.exists():
        try:
            status = request_daemon(socket_path, {"action": "status"}, timeout=2.0)
            if status.get("ok"):
                print(json.dumps({"status": "already_running", **status}, indent=2))
                return 0
        except OSError:
            pass

    repl_bin = Path(args.repl_bin).resolve()
    if not repl_bin.exists():
        raise FileNotFoundError(f"REPL binary not found at {repl_bin}")

    if args.foreground:
        return serve_daemon(
            socket_path=socket_path,
            repl_bin=repl_bin,
            cwd=Path(args.cwd).resolve(),
            max_private_dirty_mb=args.max_private_dirty_mb,
        )

    log_path = Path(args.log or f"{socket_path}.log")
    with open(log_path, "ab") as log_file:
        subprocess.Popen(
            [
                sys.executable,
                str(Path(__file__).resolve()),
                "start",
                "--foreground",
                "--socket",
                str(socket_path),
                "--repl-bin",
                str(repl_bin),
                "--cwd",
                str(Path(args.cwd).resolve()),
                "--max-private-dirty-mb",
                str(args.max_private_dirty_mb),
            ],
            stdout=log_file,
            stderr=log_file,
            start_new_session=True,
        )

    deadline = time.time() + 10.0
    while time.time() < deadline:
        if socket_path.exists():
            try:
                status = request_daemon(socket_path, {"action": "status"}, timeout=2.0)
                if status.get("ok"):
                    print(json.dumps({"status": "started", "socket": str(socket_path), **status}, indent=2))
                    return 0
            except OSError:
                pass
        time.sleep(0.05)

    print(f"Failed to start Zygote REPL daemon on {socket_path}; inspect {log_path}", file=sys.stderr)
    return 1


def cmd_load_header(args: argparse.Namespace) -> int:
    socket_path = Path(args.socket)
    file_path = Path(args.file).resolve()
    repo_root = Path(args.cwd).resolve()
    env_cache_path = Path(f"{socket_path}.env.json")
    resolved_env = resolve_lake_env(repo_root, cache_file=env_cache_path)
    lean_paths = [Path(p) for p in resolved_env.get("LEAN_PATH", "").split(":") if p]

    cmd_text, meta = extract_ast_header_prefix(
        file_path=file_path,
        until_line=args.until_line,
        until_decl=args.until_decl,
        repo_root=repo_root,
        lean_paths=lean_paths,
        stub_prefix_theorems=args.stub_prefix_theorems,
    )
    payload: dict[str, Any] = {"cmd": cmd_text}
    if args.env is not None:
        payload["env"] = args.env

    resp = request_daemon(
        socket_path,
        {
            "action": "load_header",
            "agent_id": args.agent_id,
            "checkpoint": args.checkpoint,
            "deduplicate": not args.no_dedup,
            "payload": payload,
        },
        timeout=args.timeout,
    )
    resp["ast_header_meta"] = meta
    print(json.dumps(resp, indent=2))
    return 1 if has_error_messages(resp) else 0


def cmd_check_decl(args: argparse.Namespace) -> int:
    socket_path = Path(args.socket)
    file_path = Path(args.file).resolve()
    repo_root = Path(args.cwd).resolve()
    env_cache_path = Path(f"{socket_path}.env.json")
    resolved_env = resolve_lake_env(repo_root, cache_file=env_cache_path)
    lean_paths = [Path(p) for p in resolved_env.get("LEAN_PATH", "").split(":") if p]

    ctx = extract_decl_context(
        file_path=file_path,
        decl_name_or_line=args.decl,
        repo_root=repo_root,
        lean_paths=lean_paths,
        stub_prefix_theorems=args.stub_prefix_theorems,
    )

    if args.auto_load_prefix:
        header_resp = request_daemon(
            socket_path,
            {
                "action": "load_header",
                "agent_id": args.agent_id,
                "checkpoint": args.checkpoint or f"prefix_{ctx['decl_name']}",
                "deduplicate": True,
                "payload": {"cmd": ctx["header_and_prefix"]},
            },
            timeout=args.timeout,
        )
        if has_error_messages(header_resp):
            print(json.dumps({"stage": "auto_load_prefix", **header_resp}, indent=2))
            return 1
        base_env = header_resp["env"]
        snippet = ctx["decl_text"]
    else:
        base_env = args.env
        snippet = ctx["scope_wrapped_decl"]

    payload: dict[str, Any] = {"cmd": snippet}
    if base_env is not None:
        payload["env"] = base_env

    resp = request_daemon(
        socket_path,
        {
            "action": "send",
            "agent_id": args.agent_id,
            "checkpoint": args.checkpoint,
            "payload": payload,
        },
        timeout=args.timeout,
    )
    resp["decl_meta"] = {
        "decl_name": ctx["decl_name"],
        "qualified_name": ctx["qualified_name"],
        "kind": ctx["kind"],
        "start_line": ctx["start_line"],
        "end_line": ctx["end_line"],
        "scopes": ctx["scopes"],
        "variables": ctx["variables"],
    }
    print(json.dumps(resp, indent=2))
    return 1 if has_error_messages(resp) else 0


def cmd_gc(args: argparse.Namespace) -> int:
    resp = request_daemon(
        Path(args.socket),
        {"action": "gc", "keep_checkpoints": args.keep_checkpoint},
        timeout=args.timeout,
    )
    print(json.dumps(resp, indent=2))
    return 0 if resp.get("ok") else 1


def cmd_status(args: argparse.Namespace) -> int:
    resp = request_daemon(
        Path(args.socket),
        {"action": "status", "agent_id": args.agent_id},
        timeout=5.0,
    )
    print(json.dumps(resp, indent=2))
    return 0 if resp.get("ok") else 1


def cmd_stop(args: argparse.Namespace) -> int:
    socket_path = Path(args.socket)
    if not socket_path.exists():
        print(json.dumps({"ok": True, "stopped": False, "reason": "not_running"}))
        return 0
    resp = request_daemon(socket_path, {"action": "stop"}, timeout=5.0)
    print(json.dumps(resp, indent=2))
    return 0


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="subcommand", required=True)

    p_start = sub.add_parser("start", help="Start the Zygote Lean REPL daemon (direct repl, no lake parent)")
    p_start.add_argument("--socket", default=DEFAULT_SOCKET)
    p_start.add_argument("--repl-bin", default=DEFAULT_REPL_BIN)
    p_start.add_argument("--cwd", default=str(DEFAULT_REPO_ROOT))
    p_start.add_argument("--log", default=None)
    p_start.add_argument("--foreground", action="store_true")
    p_start.add_argument("--max-private-dirty-mb", type=float, default=0.0)
    p_start.set_defaults(func=cmd_start)

    p_header = sub.add_parser(
        "load-header",
        help="AST-aware header/prefix loader with multi-agent session isolation and SHA-256 deduplication",
    )
    p_header.add_argument("--socket", default=DEFAULT_SOCKET)
    p_header.add_argument("--cwd", default=str(DEFAULT_REPO_ROOT))
    p_header.add_argument("--file", required=True)
    p_header.add_argument("--until-line", type=int, default=None)
    p_header.add_argument("--until-decl", default=None)
    p_header.add_argument("--stub-prefix-theorems", action="store_true")
    p_header.add_argument("--agent-id", default="default")
    p_header.add_argument("--checkpoint", default=None)
    p_header.add_argument("--no-dedup", action="store_true")
    p_header.add_argument("--env", type=int, default=None)
    p_header.add_argument("--timeout", type=float, default=300.0)
    p_header.set_defaults(func=cmd_load_header)

    p_check_decl = sub.add_parser(
        "check-decl",
        help="AST-aware declaration checker by name or line number (preserves section/variable/namespace context)",
    )
    p_check_decl.add_argument("--socket", default=DEFAULT_SOCKET)
    p_check_decl.add_argument("--cwd", default=str(DEFAULT_REPO_ROOT))
    p_check_decl.add_argument("--file", required=True)
    p_check_decl.add_argument("--decl", required=True, help="Declaration name or 1-based line number")
    p_check_decl.add_argument("--agent-id", default="default")
    p_check_decl.add_argument("--checkpoint", default=None)
    p_check_decl.add_argument("--env", type=int, default=None)
    p_check_decl.add_argument("--auto-load-prefix", action="store_true")
    p_check_decl.add_argument("--stub-prefix-theorems", action="store_true")
    p_check_decl.add_argument("--timeout", type=float, default=300.0)
    p_check_decl.set_defaults(func=cmd_check_decl)

    p_gc = sub.add_parser("gc", help="Recycle REPL worker to reclaim Private_Dirty RAM and re-warm checkpoints")
    p_gc.add_argument("--socket", default=DEFAULT_SOCKET)
    p_gc.add_argument("--keep-checkpoint", action="append", default=None)
    p_gc.add_argument("--timeout", type=float, default=300.0)
    p_gc.set_defaults(func=cmd_gc)

    p_status = sub.add_parser("status", help="Check daemon status, smaps_rollup RAM, checkpoints, and agent sessions")
    p_status.add_argument("--socket", default=DEFAULT_SOCKET)
    p_status.add_argument("--agent-id", default="default")
    p_status.set_defaults(func=cmd_status)

    p_stop = sub.add_parser("stop", help="Stop the running Zygote REPL daemon")
    p_stop.add_argument("--socket", default=DEFAULT_SOCKET)
    p_stop.set_defaults(func=cmd_stop)

    return parser


def main(argv: list[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    return args.func(args)


if __name__ == "__main__":
    sys.exit(main())
