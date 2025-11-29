#!/usr/bin/env python3
"""
Count tokens in Lean 4 code for proof optimization comparison.

Provides rough token estimates to compare optimization candidates.
"""

import re
import sys
from pathlib import Path
from typing import List, Tuple

# Token weight estimates based on typical Lean tokenization
TOKEN_WEIGHTS = {
    # Single-token keywords
    'let': 1, 'have': 1, 'exact': 1, 'intro': 1, 'by': 1, 'fun': 1,
    'calc': 1, 'if': 1, 'then': 1, 'else': 1, 'match': 1, 'with': 1,
    'do': 1, 'return': 1, 'sorry': 1, 'rw': 1, 'simp': 1, 'ring': 1,
    'omega': 1, 'linarith': 1, 'apply': 1, 'refine': 1, 'cases': 1,
    'constructor': 1, 'rcases': 1, 'obtain': 1,

    # Multi-token constructs (rough estimates)
    ':=': 1, '=>': 1, '↦': 1, '|': 1, '·': 1, '∀': 1, '∃': 1,
    '→': 1, '←': 1, '↔': 1, '∧': 1, '∨': 1, '¬': 1,
    '≤': 1, '≥': 1, '≠': 1, '<': 1, '>': 1, '=': 1,
    '+': 1, '-': 1, '*': 1, '/': 1, '^': 1,
    '⟨': 1, '⟩': 1, '(': 1, ')': 1, '[': 1, ']': 1, '{': 1, '}': 1,
}

def estimate_line_tokens(line: str) -> int:
    """Estimate token count for a single line."""
    # Remove comments
    line = re.sub(r'--.*$', '', line).strip()
    if not line:
        return 0

    tokens = 0

    # Count known keywords
    for keyword, weight in TOKEN_WEIGHTS.items():
        tokens += line.count(keyword) * weight

    # Count identifiers (rough heuristic: words not in TOKEN_WEIGHTS)
    words = re.findall(r'\b\w+\b', line)
    for word in words:
        if word not in TOKEN_WEIGHTS:
            # Most identifiers are 1-2 tokens
            # Longer names might be multiple tokens
            if len(word) > 15:
                tokens += 2
            else:
                tokens += 1

    # Count function applications: (fun ... => ...)
    fun_lambdas = len(re.findall(r'\(fun\s+\w+\s+=>', line))
    tokens += fun_lambdas * 3  # fun, param, =>

    # Count type annotations: (x : Type)
    type_annots = len(re.findall(r':\s*\w+', line))
    tokens += type_annots * 2  # : and type name

    # Add baseline for punctuation and structure
    # Each line typically has 2-4 tokens of overhead
    tokens += 2

    return max(tokens, 1)  # Minimum 1 token per non-empty line

def count_code_tokens(code: str) -> Tuple[int, int]:
    """
    Count tokens in code snippet.

    Returns: (line_count, token_estimate)
    """
    lines = code.split('\n')
    non_empty_lines = 0
    total_tokens = 0

    for line in lines:
        cleaned = line.strip()
        if cleaned and not cleaned.startswith('--'):
            non_empty_lines += 1
            total_tokens += estimate_line_tokens(line)

    return (non_empty_lines, total_tokens)

def read_file_range(file_path: Path, start_line: int, end_line: int) -> str:
    """Read specific line range from file."""
    if not file_path.exists():
        raise FileNotFoundError(f"{file_path} not found")

    with open(file_path, 'r', encoding='utf-8') as f:
        lines = f.readlines()

    # Convert to 0-indexed
    start_idx = start_line - 1
    end_idx = end_line

    if start_idx < 0 or end_idx > len(lines):
        raise ValueError(f"Line range {start_line}-{end_line} out of bounds")

    return ''.join(lines[start_idx:end_idx])

def format_comparison(before: Tuple[int, int], after: Tuple[int, int]) -> str:
    """Format before/after comparison."""
    before_lines, before_tokens = before
    after_lines, after_tokens = after

    line_diff = before_lines - after_lines
    line_pct = (line_diff / before_lines * 100) if before_lines > 0 else 0

    token_diff = before_tokens - after_tokens
    token_pct = (token_diff / before_tokens * 100) if before_tokens > 0 else 0

    output = []
    output.append("\n" + "="*60)
    output.append("Optimization Comparison")
    output.append("="*60)
    output.append(f"\nBEFORE:")
    output.append(f"  Lines:  {before_lines}")
    output.append(f"  Tokens: {before_tokens} (estimated)")
    output.append(f"\nAFTER:")
    output.append(f"  Lines:  {after_lines}")
    output.append(f"  Tokens: {after_tokens} (estimated)")
    output.append(f"\nREDUCTION:")
    output.append(f"  Lines:  -{line_diff} ({line_pct:.1f}%)")
    output.append(f"  Tokens: -{token_diff} ({token_pct:.1f}%)")

    if token_pct > 50:
        output.append(f"\n✅ Excellent optimization! (>{token_pct:.0f}% reduction)")
    elif token_pct > 30:
        output.append(f"\n✅ Good optimization (>{token_pct:.0f}% reduction)")
    elif token_pct > 10:
        output.append(f"\n→ Moderate optimization (~{token_pct:.0f}% reduction)")
    else:
        output.append(f"\n⚠️  Minimal benefit (<{token_pct:.0f}% reduction)")

    output.append("")

    return '\n'.join(output)

def main():
    import argparse

    parser = argparse.ArgumentParser(
        description='Count tokens in Lean 4 code for optimization comparison',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # Count tokens in code snippet
  %(prog)s "lemma foo := by exact bar"

  # Count tokens in file range
  %(prog)s MyFile.lean:10-15

  # Compare before/after optimization
  %(prog)s --before "let x := def; have h := proof; exact result x h" \\
           --after "exact result def proof"

  # Compare file ranges
  %(prog)s --before-file MyFile.lean:10-15 \\
           --after-file MyFile.lean:20-22

Token estimates are rough approximations for comparison purposes.
        """
    )

    parser.add_argument('code', nargs='?', help='Code snippet or file:line-range')
    parser.add_argument('--before', help='Before optimization (code or file:range)')
    parser.add_argument('--after', help='After optimization (code or file:range)')
    parser.add_argument('--before-file', help='Before file with range (file:start-end)')
    parser.add_argument('--after-file', help='After file with range (file:start-end)')

    args = parser.parse_args()

    # Comparison mode
    if args.before or args.before_file:
        if not (args.after or args.after_file):
            print("Error: --after or --after-file required for comparison", file=sys.stderr)
            return 1

        # Parse before
        if args.before_file:
            match = re.match(r'(.+):(\d+)-(\d+)$', args.before_file)
            if not match:
                print(f"Error: Invalid format '{args.before_file}'. Use file:start-end", file=sys.stderr)
                return 1
            file_path, start, end = match.groups()
            before_code = read_file_range(Path(file_path), int(start), int(end))
        else:
            before_code = args.before

        # Parse after
        if args.after_file:
            match = re.match(r'(.+):(\d+)-(\d+)$', args.after_file)
            if not match:
                print(f"Error: Invalid format '{args.after_file}'. Use file:start-end", file=sys.stderr)
                return 1
            file_path, start, end = match.groups()
            after_code = read_file_range(Path(file_path), int(start), int(end))
        else:
            after_code = args.after

        # Count and compare
        before_stats = count_code_tokens(before_code)
        after_stats = count_code_tokens(after_code)

        print(format_comparison(before_stats, after_stats))
        return 0

    # Single count mode
    if not args.code:
        parser.print_help()
        return 1

    # Check if it's a file:range
    match = re.match(r'(.+):(\d+)-(\d+)$', args.code)
    if match:
        file_path, start, end = match.groups()
        code = read_file_range(Path(file_path), int(start), int(end))
    else:
        code = args.code

    lines, tokens = count_code_tokens(code)

    print(f"\nToken Count")
    print("="*40)
    print(f"Lines:  {lines}")
    print(f"Tokens: {tokens} (estimated)")
    print(f"Avg:    {tokens/lines:.1f} tokens/line" if lines > 0 else "")
    print()

    return 0

if __name__ == '__main__':
    sys.exit(main())
