#!/usr/bin/env python3
"""
sorry_analyzer.py - Extract and analyze sorry statements in Lean 4 code

Usage:
    ./sorry_analyzer.py <file-or-directory> [--format=text|json|markdown] [--interactive]

This script finds all 'sorry' instances in Lean files and extracts:
- Location (file, line number)
- Context (surrounding code)
- Documentation (TODO comments)
- Type information (from goal state if available)

Modes:
    --interactive: Interactive mode to pick which sorry to work on
    --format=FORMAT: Output format (text, json, markdown)

Examples:
    ./sorry_analyzer.py MyFile.lean
    ./sorry_analyzer.py src/DeFinetti/ --format=markdown
    ./sorry_analyzer.py . --format=json > sorries.json
    ./sorry_analyzer.py . --interactive
"""

import re
import sys
import json
import subprocess
from pathlib import Path
from dataclasses import dataclass, asdict
from typing import List, Optional

@dataclass
class Sorry:
    """Represents a sorry instance with context"""
    file: str
    line: int
    context_before: List[str]
    context_after: List[str]
    documentation: List[str]
    in_declaration: Optional[str] = None

def extract_declaration_name(lines: List[str], sorry_idx: int) -> Optional[str]:
    """Extract the theorem/lemma/def name containing this sorry"""
    # Search backwards for declaration
    for i in range(sorry_idx - 1, max(0, sorry_idx - 50), -1):
        match = re.match(r'^\s*(theorem|lemma|def|example)\s+(\w+)', lines[i])
        if match:
            return f"{match.group(1)} {match.group(2)}"
    return None

def extract_documentation(lines: List[str], sorry_idx: int) -> List[str]:
    """Extract TODO/NOTE comments near the sorry"""
    docs = []
    # Check lines after sorry
    for i in range(sorry_idx + 1, min(len(lines), sorry_idx + 10)):
        line = lines[i].strip()
        if line.startswith('--'):
            comment = line[2:].strip()
            if any(keyword in comment.upper() for keyword in ['TODO', 'NOTE', 'FIXME', 'STRATEGY', 'DEPENDENCIES']):
                docs.append(comment)
        elif line and not line.startswith('--'):
            break
    return docs

def find_sorries_in_file(filepath: Path) -> List[Sorry]:
    """Find all sorries in a single Lean file"""
    try:
        with open(filepath, 'r', encoding='utf-8') as f:
            lines = f.readlines()
    except Exception as e:
        print(f"Warning: Could not read {filepath}: {e}", file=sys.stderr)
        return []

    sorries = []
    for i, line in enumerate(lines):
        # Look for sorry (not in comments)
        if 'sorry' in line:
            # Simple check: not in a comment
            code_part = line.split('--')[0]
            if 'sorry' in code_part:
                context_before = [l.rstrip() for l in lines[max(0, i-3):i]]
                context_after = [l.rstrip() for l in lines[i+1:min(len(lines), i+4)]]

                sorry = Sorry(
                    file=str(filepath),
                    line=i + 1,  # 1-indexed
                    context_before=context_before,
                    context_after=context_after,
                    documentation=extract_documentation(lines, i),
                    in_declaration=extract_declaration_name(lines, i)
                )
                sorries.append(sorry)

    return sorries

def find_sorries(target: Path) -> List[Sorry]:
    """Find all sorries in target file or directory"""
    if target.is_file():
        return find_sorries_in_file(target)
    elif target.is_dir():
        sorries = []
        for lean_file in target.rglob("*.lean"):
            sorries.extend(find_sorries_in_file(lean_file))
        return sorries
    else:
        raise ValueError(f"{target} is not a file or directory")

def format_text(sorries: List[Sorry]) -> str:
    """Format sorries as human-readable text"""
    output = []
    output.append(f"Found {len(sorries)} sorry statement(s)\n")
    output.append("=" * 80)

    for i, sorry in enumerate(sorries, 1):
        output.append(f"\n[{i}] {sorry.file}:{sorry.line}")
        if sorry.in_declaration:
            output.append(f"    In: {sorry.in_declaration}")

        if sorry.documentation:
            output.append("    Documentation:")
            for doc in sorry.documentation:
                output.append(f"      • {doc}")

        output.append("\n    Context:")
        for line in sorry.context_before[-2:]:
            output.append(f"      {line}")
        output.append(f"      >>> SORRY <<<")
        for line in sorry.context_after[:2]:
            output.append(f"      {line}")
        output.append("")

    return "\n".join(output)

def format_markdown(sorries: List[Sorry]) -> str:
    """Format sorries as Markdown"""
    output = []
    output.append(f"# Sorry Analysis Report\n")
    output.append(f"**Total sorries found:** {len(sorries)}\n")

    # Group by file
    by_file = {}
    for sorry in sorries:
        by_file.setdefault(sorry.file, []).append(sorry)

    for filepath, file_sorries in sorted(by_file.items()):
        output.append(f"## {filepath}\n")
        output.append(f"**Count:** {len(file_sorries)}\n")

        for sorry in file_sorries:
            output.append(f"### Line {sorry.line}")
            if sorry.in_declaration:
                output.append(f"**Declaration:** `{sorry.in_declaration}`\n")

            if sorry.documentation:
                output.append("**Documentation:**")
                for doc in sorry.documentation:
                    output.append(f"- {doc}")
                output.append("")

            output.append("**Context:**")
            output.append("```lean")
            for line in sorry.context_before[-2:]:
                output.append(line)
            output.append("sorry  -- ⚠️")
            for line in sorry.context_after[:2]:
                output.append(line)
            output.append("```\n")

    return "\n".join(output)

def format_json(sorries: List[Sorry]) -> str:
    """Format sorries as JSON"""
    return json.dumps({
        'total_count': len(sorries),
        'sorries': [asdict(s) for s in sorries]
    }, indent=2)

def interactive_mode(sorries: List[Sorry]):
    """Interactive mode to navigate and select sorries"""
    if not sorries:
        print("No sorries found!")
        return

    # Group by file
    by_file = {}
    for sorry in sorries:
        by_file.setdefault(sorry.file, []).append(sorry)

    print(f"\n{'='*80}")
    print(f"Found {len(sorries)} sorry statement(s) across {len(by_file)} file(s)")
    print(f"{'='*80}\n")

    # Display files with sorry counts
    files = sorted(by_file.items(), key=lambda x: len(x[1]), reverse=True)
    print("Files with sorries:")
    for i, (filepath, file_sorries) in enumerate(files, 1):
        print(f"  [{i}] {filepath} ({len(file_sorries)} sorries)")

    print("\nOptions:")
    print("  [1-N] - View sorries in file N")
    print("  [q]   - Quit")

    while True:
        try:
            choice = input("\nSelect file (or 'q' to quit): ").strip()
            if choice.lower() == 'q':
                break

            idx = int(choice) - 1
            if 0 <= idx < len(files):
                filepath, file_sorries = files[idx]
                show_file_sorries(filepath, file_sorries)
            else:
                print("Invalid selection")
        except (ValueError, EOFError, KeyboardInterrupt):
            print("\nExiting...")
            break

def show_file_sorries(filepath: str, sorries: List[Sorry]):
    """Show sorries in a specific file with navigation"""
    print(f"\n{'='*80}")
    print(f"File: {filepath}")
    print(f"{'='*80}\n")

    for i, sorry in enumerate(sorries, 1):
        print(f"[{i}] Line {sorry.line}", end="")
        if sorry.in_declaration:
            print(f" - {sorry.in_declaration}", end="")
        print()

    print("\nOptions:")
    print("  [1-N]  - View sorry details")
    print("  [o N]  - Open file at sorry N in $EDITOR")
    print("  [b]    - Back to file list")
    print("  [q]    - Quit")

    while True:
        try:
            choice = input("\nSelect sorry (or 'b'/'q'): ").strip()

            if choice.lower() == 'q':
                sys.exit(0)
            elif choice.lower() == 'b':
                return
            elif choice.lower().startswith('o '):
                # Open in editor
                try:
                    idx = int(choice.split()[1]) - 1
                    if 0 <= idx < len(sorries):
                        sorry = sorries[idx]
                        editor = subprocess.os.environ.get('EDITOR', 'vim')
                        subprocess.call([editor, f"+{sorry.line}", sorry.file])
                    else:
                        print("Invalid selection")
                except (ValueError, IndexError):
                    print("Usage: o <number>")
            else:
                idx = int(choice) - 1
                if 0 <= idx < len(sorries):
                    show_sorry_details(sorries[idx])
                else:
                    print("Invalid selection")
        except (ValueError, EOFError, KeyboardInterrupt):
            print("\nExiting...")
            sys.exit(0)

def show_sorry_details(sorry: Sorry):
    """Show detailed information about a specific sorry"""
    print(f"\n{'─'*80}")
    print(f"Sorry at {sorry.file}:{sorry.line}")
    if sorry.in_declaration:
        print(f"Declaration: {sorry.in_declaration}")
    print(f"{'─'*80}")

    if sorry.documentation:
        print("\nDocumentation:")
        for doc in sorry.documentation:
            print(f"  • {doc}")

    print("\nContext:")
    print("─" * 40)
    for line in sorry.context_before[-5:]:
        print(f"  {line}")
    print(f"  >>> SORRY HERE <<<")
    for line in sorry.context_after[:5]:
        print(f"  {line}")
    print("─" * 40)

    input("\nPress Enter to continue...")

def main():
    if len(sys.argv) < 2:
        print(__doc__)
        sys.exit(1)

    target = Path(sys.argv[1])
    format_type = 'text'
    interactive = False

    # Parse arguments
    for arg in sys.argv[2:]:
        if arg.startswith('--format='):
            format_type = arg.split('=')[1]
        elif arg == '--interactive':
            interactive = True

    if not target.exists():
        print(f"Error: {target} does not exist", file=sys.stderr)
        sys.exit(1)

    # Find all sorries
    sorries = find_sorries(target)

    # Interactive mode takes precedence
    if interactive:
        interactive_mode(sorries)
        sys.exit(0 if len(sorries) == 0 else 1)

    # Format output
    if format_type == 'json':
        print(format_json(sorries))
    elif format_type == 'markdown':
        print(format_markdown(sorries))
    else:
        print(format_text(sorries))

    # Exit code: 0 if no sorries, 1 if sorries found
    sys.exit(0 if len(sorries) == 0 else 1)

if __name__ == '__main__':
    main()
