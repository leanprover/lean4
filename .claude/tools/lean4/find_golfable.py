#!/usr/bin/env python3
"""
Find proof-golfing opportunities in Lean 4 files.

Identifies optimization patterns with estimated reduction potential.
"""

import re
import sys
from pathlib import Path
from typing import List, Tuple, Optional
from dataclasses import dataclass

@dataclass
class GolfablePattern:
    """Represents a proof optimization opportunity."""
    pattern_type: str
    file_path: str
    line_number: int
    line_count: int
    snippet: str
    reduction_estimate: str
    priority: str

def count_lines_in_range(lines: List[str], start_idx: int, end_idx: int) -> int:
    """Count non-empty, non-comment lines in a range."""
    count = 0
    for i in range(start_idx, min(end_idx, len(lines))):
        line = lines[i].strip()
        if line and not line.startswith('--'):
            count += 1
    return count

def count_binding_uses(lines: List[str], binding_name: str, start_idx: int) -> int:
    """Count how many times a binding is used after its definition."""
    uses = 0
    for i in range(start_idx, len(lines)):
        line = lines[i]
        # Skip comments
        line = re.sub(r'--.*$', '', line)
        # Count occurrences as whole word
        pattern = r'\b' + re.escape(binding_name) + r'\b'
        uses += len(re.findall(pattern, line))
    # Subtract 1 for definition itself (appears on start line)
    return max(0, uses - 1)

def find_let_have_exact(file_path: Path, lines: List[str], filter_multi_use: bool = False) -> List[GolfablePattern]:
    """Find let + have + exact patterns (HIGHEST value).

    Args:
        filter_multi_use: If True, filter out let bindings used ≥3 times (false positives)
    """
    patterns = []
    i = 0

    while i < len(lines):
        line = lines[i].strip()

        # Look for "let" statements
        match = re.match(r'let\s+(\w+)\s*:', line)
        if match:
            let_name = match.group(1)

            # Check if followed by have and exact within next 15 lines
            has_have = False
            has_exact = False
            end_idx = min(i + 15, len(lines))

            for j in range(i + 1, end_idx):
                next_line = lines[j].strip()
                if re.match(r'have\s+\w+\s*:', next_line):
                    has_have = True
                if next_line.startswith('exact '):
                    has_exact = True

                    if has_have:
                        # Check if this is a false positive (multiple uses)
                        if filter_multi_use:
                            uses = count_binding_uses(lines, let_name, i)
                            if uses >= 3:
                                # FALSE POSITIVE - skip this one
                                i = j
                                break

                        # Found the pattern!
                        line_count = count_lines_in_range(lines, i, j + 1)
                        snippet = '\n'.join(lines[i:min(j+3, len(lines))])

                        patterns.append(GolfablePattern(
                            pattern_type="let + have + exact",
                            file_path=str(file_path),
                            line_number=i + 1,  # 1-indexed
                            line_count=line_count,
                            snippet=snippet[:200] + "..." if len(snippet) > 200 else snippet,
                            reduction_estimate="60-80%",
                            priority="HIGH"
                        ))
                        i = j
                        break
        i += 1

    return patterns

def find_by_exact(file_path: Path, lines: List[str]) -> List[GolfablePattern]:
    """Find 'by exact' wrapper patterns."""
    patterns = []

    for i, line in enumerate(lines):
        # Look for lines ending with "by" followed by "exact" on next line
        if re.search(r':=\s*by\s*$', line.strip()):
            if i + 1 < len(lines) and lines[i + 1].strip().startswith('exact '):
                snippet = f"{line.strip()}\n  {lines[i + 1].strip()}"

                patterns.append(GolfablePattern(
                    pattern_type="by exact wrapper",
                    file_path=str(file_path),
                    line_number=i + 1,
                    line_count=2,
                    snippet=snippet,
                    reduction_estimate="50%",
                    priority="MEDIUM"
                ))

    return patterns

def find_calc_chains(file_path: Path, lines: List[str]) -> List[GolfablePattern]:
    """Find calc chains with 'by' tactics that might simplify."""
    patterns = []
    i = 0

    while i < len(lines):
        line = lines[i].strip()

        if line.startswith('calc ') or re.match(r'_\s+[<>=]', line):
            # Count calc chain lines
            j = i + 1
            calc_lines = 1
            while j < len(lines) and (lines[j].strip().startswith('_') or
                                       lines[j].strip().startswith('calc')):
                calc_lines += 1
                j += 1

            if calc_lines >= 4:  # Only flag longer chains
                snippet = '\n'.join(lines[i:min(i+5, len(lines))])

                patterns.append(GolfablePattern(
                    pattern_type="calc chain",
                    file_path=str(file_path),
                    line_number=i + 1,
                    line_count=calc_lines,
                    snippet=snippet[:200] + "..." if len(snippet) > 200 else snippet,
                    reduction_estimate="30-50%",
                    priority="MEDIUM"
                ))
                i = j - 1
        i += 1

    return patterns

def find_constructor_branches(file_path: Path, lines: List[str]) -> List[GolfablePattern]:
    """Find constructor branches with multiple lines."""
    patterns = []
    i = 0

    while i < len(lines):
        line = lines[i].strip()

        if line == 'constructor':
            # Count lines in branches
            branch_lines = 0
            j = i + 1
            while j < len(lines) and lines[j].startswith('  '):
                branch_lines += 1
                j += 1

            if branch_lines >= 6:  # Multiple branches with content
                snippet = '\n'.join(lines[i:min(i+10, len(lines))])

                patterns.append(GolfablePattern(
                    pattern_type="constructor branches",
                    file_path=str(file_path),
                    line_number=i + 1,
                    line_count=branch_lines,
                    snippet=snippet[:200] + "..." if len(snippet) > 200 else snippet,
                    reduction_estimate="25-50%",
                    priority="LOW"
                ))
                i = j - 1
        i += 1

    return patterns

def find_multiple_haves(file_path: Path, lines: List[str]) -> List[GolfablePattern]:
    """Find proofs with 5+ consecutive 'have' statements."""
    patterns = []
    i = 0

    while i < len(lines):
        if re.match(r'\s*have\s+\w+\s*:', lines[i]):
            # Count consecutive haves
            j = i + 1
            have_count = 1
            while j < len(lines) and re.match(r'\s*have\s+\w+\s*:', lines[j]):
                have_count += 1
                j += 1

            if have_count >= 5:
                snippet = '\n'.join(lines[i:min(i+7, len(lines))])

                patterns.append(GolfablePattern(
                    pattern_type="multiple haves",
                    file_path=str(file_path),
                    line_number=i + 1,
                    line_count=have_count * 2,  # Rough estimate
                    snippet=snippet[:200] + "..." if len(snippet) > 200 else snippet,
                    reduction_estimate="10-30%",
                    priority="LOW"
                ))
                i = j - 1
        i += 1

    return patterns

def find_have_calc(file_path: Path, lines: List[str]) -> List[GolfablePattern]:
    """Find have statements used once in immediately following calc chain.

    Pattern:
        have h_name : Type := proof
        calc expr
            relationship value := h_name

    Where h_name is used exactly once in the calc and nowhere else.
    """
    patterns = []
    i = 0

    while i < len(lines):
        line = lines[i].strip()

        # Look for "have" statements with binding name
        # Match: "have h_name : Type := proof" or multi-line variants
        match = re.match(r'have\s+(\w+)\s*:', line)
        if match:
            have_name = match.group(1)
            have_line = i

            # Look for calc in next 5 lines (allowing some spacing)
            calc_line = None
            for j in range(i + 1, min(i + 6, len(lines))):
                if re.match(r'\s*calc\s+', lines[j]):
                    calc_line = j
                    break

            if calc_line is not None:
                # Find the end of calc block (next unindented line or theorem/lemma/def)
                calc_end = calc_line + 1
                base_indent = len(lines[calc_line]) - len(lines[calc_line].lstrip())

                for j in range(calc_line + 1, min(calc_line + 20, len(lines))):
                    line_content = lines[j]
                    stripped = line_content.strip()

                    # Empty lines or comments don't end calc
                    if not stripped or stripped.startswith('--'):
                        calc_end = j + 1
                        continue

                    # Check indentation
                    indent = len(line_content) - len(line_content.lstrip())

                    # If less indented than calc start, we've exited the calc block
                    if indent <= base_indent and not re.match(r'\s*[<>=≤≥_]', line_content):
                        break

                    calc_end = j + 1

                # Count uses of have_name within calc block
                calc_uses = 0
                for j in range(calc_line, calc_end):
                    calc_text = lines[j]
                    # Remove comments
                    calc_text = re.sub(r'--.*$', '', calc_text)
                    # Count occurrences as whole word
                    pattern = r'\b' + re.escape(have_name) + r'\b'
                    calc_uses += len(re.findall(pattern, calc_text))

                # Count uses after calc block
                after_calc_uses = 0
                for j in range(calc_end, min(calc_end + 20, len(lines))):
                    after_text = lines[j]
                    # Stop at next theorem/lemma/def
                    if re.match(r'\s*(theorem|lemma|def|example)\s+', after_text):
                        break
                    # Remove comments
                    after_text = re.sub(r'--.*$', '', after_text)
                    # Count occurrences
                    pattern = r'\b' + re.escape(have_name) + r'\b'
                    after_calc_uses += len(re.findall(pattern, after_text))

                # Pattern detected: exactly 1 use in calc, 0 uses after
                if calc_uses == 1 and after_calc_uses == 0:
                    # Get proof term length (rough estimate)
                    have_full_text = lines[have_line:calc_line]
                    proof_length = sum(len(l.strip()) for l in have_full_text)

                    # Determine priority based on proof length
                    if proof_length > 80:
                        priority = "LOW"  # Long proof, readability matters
                        reduction = "30-40%"
                    else:
                        priority = "MEDIUM"
                        reduction = "40-50%"

                    snippet_lines = lines[have_line:min(calc_end, have_line + 8)]
                    snippet = ''.join(snippet_lines)

                    patterns.append(GolfablePattern(
                        pattern_type="have-calc single-use",
                        file_path=str(file_path),
                        line_number=have_line + 1,  # 1-indexed
                        line_count=calc_line - have_line + 1,
                        snippet=snippet[:200] + "..." if len(snippet) > 200 else snippet,
                        reduction_estimate=reduction,
                        priority=priority
                    ))

                    i = calc_end - 1

        i += 1

    return patterns

def analyze_file(file_path: Path, pattern_types: Optional[List[str]] = None,
                filter_false_positives: bool = False) -> List[GolfablePattern]:
    """Analyze a file for optimization patterns.

    Args:
        pattern_types: Specific patterns to search for (or 'all')
        filter_false_positives: If True, filter out let bindings used ≥3 times
    """
    if not file_path.exists():
        return []

    with open(file_path, 'r', encoding='utf-8') as f:
        lines = f.readlines()

    all_patterns = []

    # If no specific patterns requested, find all
    if pattern_types is None or 'all' in pattern_types:
        pattern_types = ['let-have-exact', 'have-calc', 'by-exact', 'calc', 'constructor', 'multiple-haves']

    for pattern_type in pattern_types:
        if pattern_type == 'let-have-exact':
            patterns = find_let_have_exact(file_path, lines, filter_false_positives)
        elif pattern_type == 'have-calc':
            patterns = find_have_calc(file_path, lines)
        elif pattern_type == 'by-exact':
            patterns = find_by_exact(file_path, lines)
        elif pattern_type == 'calc':
            patterns = find_calc_chains(file_path, lines)
        elif pattern_type == 'constructor':
            patterns = find_constructor_branches(file_path, lines)
        elif pattern_type == 'multiple-haves':
            patterns = find_multiple_haves(file_path, lines)
        else:
            continue

        all_patterns.extend(patterns)

    # Sort by priority and potential savings
    priority_order = {'HIGH': 0, 'MEDIUM': 1, 'LOW': 2}
    all_patterns.sort(key=lambda p: (priority_order[p.priority], -p.line_count))

    return all_patterns

def format_output(patterns: List[GolfablePattern], verbose: bool = False) -> str:
    """Format patterns for display."""
    if not patterns:
        return "No optimization opportunities found."

    output = []
    output.append(f"\n{'='*70}")
    output.append(f"Found {len(patterns)} optimization opportunities")
    output.append(f"{'='*70}\n")

    for i, pattern in enumerate(patterns, 1):
        output.append(f"{i}. {pattern.pattern_type.upper()} [{pattern.priority} PRIORITY]")
        output.append(f"   File: {pattern.file_path}:{pattern.line_number}")
        output.append(f"   Lines: {pattern.line_count} | Est. reduction: {pattern.reduction_estimate}")

        if verbose:
            output.append(f"\n   Preview:")
            for line in pattern.snippet.split('\n')[:5]:
                output.append(f"   | {line}")

        output.append("")

    # Summary by priority
    high = sum(1 for p in patterns if p.priority == 'HIGH')
    med = sum(1 for p in patterns if p.priority == 'MEDIUM')
    low = sum(1 for p in patterns if p.priority == 'LOW')

    output.append(f"Summary: {high} HIGH, {med} MEDIUM, {low} LOW priority")
    output.append(f"Expected total reduction: 30-40% with systematic optimization\n")

    return '\n'.join(output)

def main():
    import argparse

    parser = argparse.ArgumentParser(
        description='Find proof-golfing opportunities in Lean 4 files',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # Find all patterns in a file
  %(prog)s MyFile.lean

  # Find specific pattern types
  %(prog)s MyFile.lean --patterns let-have-exact by-exact

  # Show code snippets
  %(prog)s MyFile.lean --verbose

  # Analyze all .lean files in directory
  %(prog)s src/ --recursive

Pattern types:
  let-have-exact  : let + have + exact pattern (HIGHEST value, 60-80%% reduction)
  have-calc       : have used once in following calc (MEDIUM value, 40-50%% reduction)
  by-exact        : by-exact wrapper pattern (50%% reduction)
  calc            : Long calc chains (30-50%% reduction)
  constructor     : Constructor branches (25-50%% reduction)
  multiple-haves  : 5+ consecutive haves (10-30%% reduction)
  all             : All patterns (default)
        """
    )

    parser.add_argument('path', help='Lean file or directory to analyze')
    parser.add_argument('--patterns', nargs='+', default=['all'],
                       help='Pattern types to search for (default: all)')
    parser.add_argument('--verbose', '-v', action='store_true',
                       help='Show code snippets for each pattern')
    parser.add_argument('--recursive', '-r', action='store_true',
                       help='Recursively analyze directory')
    parser.add_argument('--filter-false-positives', '--filter', '-f', action='store_true',
                       help='Filter out let bindings used ≥3 times (reduces false positives by ~93%%)')

    args = parser.parse_args()

    path = Path(args.path)

    if not path.exists():
        print(f"Error: Path {path} does not exist", file=sys.stderr)
        return 1

    # Collect files to analyze
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
    all_patterns = []
    for file_path in files:
        patterns = analyze_file(file_path, args.patterns, args.filter_false_positives)
        all_patterns.extend(patterns)

    # Output results
    output = format_output(all_patterns, args.verbose)
    if args.filter_false_positives and all_patterns:
        # Add note about filtering
        output += "\nNote: False positive filtering enabled (let bindings used ≥3 times excluded)\n"
    print(output)

    return 0

if __name__ == '__main__':
    sys.exit(main())
