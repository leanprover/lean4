#!/usr/bin/env python3
"""
Analyze let binding usage to detect false-positive optimization candidates.

Helps avoid the #1 pitfall: inlining let bindings that are used multiple times,
which actually INCREASES token count instead of reducing it.
"""

import re
import sys
from pathlib import Path
from typing import List, Tuple, Optional
from dataclasses import dataclass

@dataclass
class LetBinding:
    """Represents a let binding with usage information."""
    name: str
    line_number: int
    definition: str
    definition_tokens: int
    uses_count: int
    use_locations: List[int]
    recommendation: str
    token_impact: str

def count_tokens(text: str) -> int:
    """Estimate token count for text."""
    # Simple heuristic: count words, operators, and punctuation
    tokens = len(re.findall(r'\w+|[^\w\s]', text))
    return tokens

def find_let_bindings(file_path: Path) -> List[Tuple[int, str, str]]:
    """Find all let bindings in file with their definitions."""
    if not file_path.exists():
        return []

    with open(file_path, 'r', encoding='utf-8') as f:
        lines = f.readlines()

    bindings = []
    for i, line in enumerate(lines):
        # Match: let <name> := <definition>
        # or: let <name> : <type> := <definition>
        match = re.search(r'let\s+(\w+)\s*(?::\s*[^:]+)?\s*:=\s*(.+)', line)
        if match:
            name = match.group(1)
            definition = match.group(2).rstrip()
            bindings.append((i + 1, name, definition))

    return bindings

def count_binding_uses(file_path: Path, binding_name: str,
                       def_line: int) -> Tuple[int, List[int]]:
    """Count how many times a binding is used after its definition."""
    with open(file_path, 'r', encoding='utf-8') as f:
        lines = f.readlines()

    uses = 0
    locations = []

    # Look for uses after the definition line
    for i in range(def_line, len(lines)):
        line = lines[i]
        # Skip comments
        line = re.sub(r'--.*$', '', line)

        # Count occurrences of the binding name (as whole word)
        pattern = r'\b' + re.escape(binding_name) + r'\b'
        matches = len(re.findall(pattern, line))

        if matches > 0:
            uses += matches
            locations.append(i + 1)

    # Subtract 1 for the definition itself
    if locations and locations[0] == def_line:
        uses -= 1
        locations = locations[1:] if len(locations) > 1 else locations

    return uses, locations

def analyze_binding(file_path: Path, line_number: int, name: str,
                   definition: str) -> LetBinding:
    """Analyze a single let binding for optimization potential."""
    def_tokens = count_tokens(definition)
    uses_count, use_locations = count_binding_uses(file_path, name, line_number)

    # Calculate token impact
    # Current: def_tokens (definition) + ~2 tokens per use (just the name)
    current_tokens = def_tokens + (uses_count * 2)

    # After inlining: def_tokens * uses_count
    inlined_tokens = def_tokens * uses_count

    token_diff = current_tokens - inlined_tokens

    # Generate recommendation
    if uses_count == 0:
        recommendation = "UNUSED - Consider removing"
        token_impact = "N/A"
    elif uses_count == 1:
        if def_tokens < 10:
            recommendation = "SAFE TO INLINE - Single use, small definition"
            token_impact = f"Saves ~{def_tokens + 2} tokens"
        else:
            recommendation = "CONSIDER INLINE - Single use, check readability"
            token_impact = f"Saves ~{def_tokens + 2} tokens"
    elif uses_count == 2:
        if token_diff > 0:
            recommendation = "MAYBE INLINE - Marginal benefit, check readability"
            token_impact = f"Saves ~{token_diff} tokens"
        else:
            recommendation = "SKIP - Breaking even or worse"
            token_impact = f"Would INCREASE by ~{abs(token_diff)} tokens"
    else:  # uses_count >= 3
        recommendation = "⚠️ DON'T INLINE - Multiple uses"
        token_impact = f"Would INCREASE by ~{abs(token_diff)} tokens"

    return LetBinding(
        name=name,
        line_number=line_number,
        definition=definition,
        definition_tokens=def_tokens,
        uses_count=uses_count,
        use_locations=use_locations,
        recommendation=recommendation,
        token_impact=token_impact
    )

def analyze_file(file_path: Path, verbose: bool = False) -> List[LetBinding]:
    """Analyze all let bindings in a file."""
    bindings_data = find_let_bindings(file_path)

    analyzed = []
    for line_num, name, definition in bindings_data:
        binding = analyze_binding(file_path, line_num, name, definition)
        analyzed.append(binding)

    return analyzed

def format_output(file_path: Path, bindings: List[LetBinding],
                 verbose: bool = False) -> str:
    """Format analysis results."""
    if not bindings:
        return f"No let bindings found in {file_path}"

    output = []
    output.append(f"\n{'='*70}")
    output.append(f"Let Binding Usage Analysis: {file_path}")
    output.append(f"{'='*70}\n")

    # Group by recommendation category
    dont_inline = [b for b in bindings if "DON'T INLINE" in b.recommendation]
    safe_to_inline = [b for b in bindings if "SAFE TO INLINE" in b.recommendation]
    consider = [b for b in bindings if "CONSIDER" in b.recommendation or "MAYBE" in b.recommendation]
    skip = [b for b in bindings if "SKIP" in b.recommendation]
    unused = [b for b in bindings if "UNUSED" in b.recommendation]

    # Report high-risk false positives first
    if dont_inline:
        output.append(f"⚠️  HIGH-RISK FALSE POSITIVES ({len(dont_inline)}):")
        output.append(f"{'─'*70}")
        for b in dont_inline:
            output.append(f"\n  {b.name} (line {b.line_number})")
            output.append(f"    Used: {b.uses_count} times (lines: {', '.join(map(str, b.use_locations[:5]))}{'...' if len(b.use_locations) > 5 else ''})")
            output.append(f"    Definition: ~{b.definition_tokens} tokens")
            output.append(f"    Impact: {b.token_impact}")
            output.append(f"    → {b.recommendation}")
            if verbose:
                output.append(f"    Code: {b.definition[:60]}{'...' if len(b.definition) > 60 else ''}")
        output.append("")

    # Safe optimizations
    if safe_to_inline:
        output.append(f"✅ SAFE TO OPTIMIZE ({len(safe_to_inline)}):")
        output.append(f"{'─'*70}")
        for b in safe_to_inline:
            output.append(f"\n  {b.name} (line {b.line_number})")
            output.append(f"    Used: {b.uses_count} time(s)")
            output.append(f"    Impact: {b.token_impact}")
            if verbose:
                output.append(f"    Code: {b.definition[:60]}{'...' if len(b.definition) > 60 else ''}")
        output.append("")

    # Marginal cases
    if consider or skip:
        output.append(f"⚡ MARGINAL CASES ({len(consider) + len(skip)}):")
        output.append(f"{'─'*70}")
        for b in (consider + skip):
            output.append(f"\n  {b.name} (line {b.line_number})")
            output.append(f"    Used: {b.uses_count} times")
            output.append(f"    Impact: {b.token_impact}")
            output.append(f"    → {b.recommendation}")
        output.append("")

    # Unused bindings
    if unused:
        output.append(f"🗑️  UNUSED BINDINGS ({len(unused)}):")
        output.append(f"{'─'*70}")
        for b in unused:
            output.append(f"\n  {b.name} (line {b.line_number})")
            output.append(f"    → {b.recommendation}")
        output.append("")

    # Summary
    output.append(f"{'='*70}")
    output.append(f"SUMMARY")
    output.append(f"{'='*70}")
    output.append(f"  Total let bindings: {len(bindings)}")
    output.append(f"  ⚠️  Don't inline (used ≥3 times): {len(dont_inline)}")
    output.append(f"  ✅ Safe to inline (used ≤1 time): {len(safe_to_inline)}")
    output.append(f"  ⚡ Marginal (used 2 times): {len(consider) + len(skip)}")
    output.append(f"  🗑️  Unused: {len(unused)}")
    output.append("")

    if dont_inline:
        output.append(f"⚠️  WARNING: {len(dont_inline)} bindings would INCREASE tokens if inlined!")
        output.append(f"   These are FALSE POSITIVES for let+have+exact pattern.")
        output.append("")

    return '\n'.join(output)

def analyze_specific_binding(file_path: Path, line_number: int) -> Optional[str]:
    """Analyze a specific let binding at given line number."""
    bindings = find_let_bindings(file_path)

    for line, name, definition in bindings:
        if line == line_number:
            binding = analyze_binding(file_path, line, name, definition)

            output = []
            output.append(f"\n{'='*70}")
            output.append(f"Analysis: {name} (line {line_number})")
            output.append(f"{'='*70}\n")
            output.append(f"Definition: {definition}")
            output.append(f"Definition size: ~{binding.definition_tokens} tokens\n")
            output.append(f"Usage:")
            output.append(f"  Count: {binding.uses_count} times")
            output.append(f"  Locations: {', '.join(map(str, binding.use_locations))}\n")
            output.append(f"Token Impact:")
            output.append(f"  Current: ~{binding.definition_tokens + binding.uses_count * 2} tokens")
            output.append(f"           ({binding.definition_tokens} def + {binding.uses_count} × 2 uses)")
            output.append(f"  Inlined: ~{binding.definition_tokens * binding.uses_count} tokens")
            output.append(f"           ({binding.definition_tokens} × {binding.uses_count} repetitions)")
            output.append(f"  {binding.token_impact}\n")
            output.append(f"{'─'*70}")
            output.append(f"RECOMMENDATION: {binding.recommendation}")
            output.append(f"{'─'*70}\n")

            return '\n'.join(output)

    return f"No let binding found at line {line_number} in {file_path}"

def main():
    import argparse

    parser = argparse.ArgumentParser(
        description='Analyze let binding usage to avoid false-positive optimizations',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # Analyze all let bindings in a file
  %(prog)s MyFile.lean

  # Analyze specific let binding at line 42
  %(prog)s MyFile.lean --line 42

  # Verbose output with definitions
  %(prog)s MyFile.lean --verbose

  # Analyze all .lean files in directory
  %(prog)s src/ --recursive

Why this matters:
  - 93%% of detected let+have+exact patterns are false positives!
  - Inlining a let binding used 5+ times makes code LONGER
  - This tool helps you skip the false positives

Key insight:
  If let binding is used ≥3 times, DON'T inline it.
  Current approach is already optimal.
        """
    )

    parser.add_argument('path', help='Lean file or directory to analyze')
    parser.add_argument('--line', type=int, help='Analyze specific let binding at this line')
    parser.add_argument('--verbose', '-v', action='store_true',
                       help='Show binding definitions')
    parser.add_argument('--recursive', '-r', action='store_true',
                       help='Recursively analyze directory')

    args = parser.parse_args()

    path = Path(args.path)

    if not path.exists():
        print(f"Error: {path} does not exist", file=sys.stderr)
        return 1

    # Specific line analysis
    if args.line:
        if not path.is_file():
            print(f"Error: --line requires a file, not a directory", file=sys.stderr)
            return 1
        result = analyze_specific_binding(path, args.line)
        print(result)
        return 0

    # Collect files
    files = []
    if path.is_file():
        if path.suffix == '.lean':
            files = [path]
        else:
            print(f"Error: {path} is not a .lean file", file=sys.stderr)
            return 1
    else:
        if args.recursive:
            files = list(path.rglob('*.lean'))
        else:
            files = list(path.glob('*.lean'))

    if not files:
        print(f"No .lean files found in {path}", file=sys.stderr)
        return 1

    # Analyze files
    for file_path in files:
        bindings = analyze_file(file_path, args.verbose)
        print(format_output(file_path, bindings, args.verbose))

    return 0

if __name__ == '__main__':
    sys.exit(main())
