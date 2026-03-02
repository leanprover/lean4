#!/usr/bin/env python3
"""
Lean name demangler.

Demangles C symbol names produced by the Lean 4 compiler back into
readable Lean hierarchical names.

Usage as a filter (like c++filt):
    echo "l_Lean_Meta_Sym_main" | python lean_demangle.py

Usage as a module:
    from lean_demangle import demangle_lean_name
    print(demangle_lean_name("l_Lean_Meta_Sym_main"))
"""

import sys


# ---------------------------------------------------------------------------
# String.mangle / unmangle
# ---------------------------------------------------------------------------

def _is_ascii_alnum(ch):
    """Check if ch is an ASCII letter or digit (matching Lean's isAlpha/isDigit)."""
    return ('a' <= ch <= 'z') or ('A' <= ch <= 'Z') or ('0' <= ch <= '9')


def mangle_string(s):
    """Port of Lean's String.mangle: escape a single string for C identifiers."""
    result = []
    for ch in s:
        if _is_ascii_alnum(ch):
            result.append(ch)
        elif ch == '_':
            result.append('__')
        else:
            code = ord(ch)
            if code < 0x100:
                result.append('_x' + format(code, '02x'))
            elif code < 0x10000:
                result.append('_u' + format(code, '04x'))
            else:
                result.append('_U' + format(code, '08x'))
    return ''.join(result)


def _parse_hex(s, pos, n):
    """Parse n lowercase hex digits at pos. Returns (new_pos, value) or None."""
    if pos + n > len(s):
        return None
    val = 0
    for i in range(n):
        c = s[pos + i]
        if '0' <= c <= '9':
            val = (val << 4) | (ord(c) - ord('0'))
        elif 'a' <= c <= 'f':
            val = (val << 4) | (ord(c) - ord('a') + 10)
        else:
            return None
    return (pos + n, val)


# ---------------------------------------------------------------------------
# Name mangling (for round-trip verification)
# ---------------------------------------------------------------------------

def _check_disambiguation(m):
    """Port of Lean's checkDisambiguation: does mangled string m need a '00' prefix?"""
    pos = 0
    while pos < len(m):
        ch = m[pos]
        if ch == '_':
            pos += 1
            continue
        if ch == 'x':
            return _parse_hex(m, pos + 1, 2) is not None
        if ch == 'u':
            return _parse_hex(m, pos + 1, 4) is not None
        if ch == 'U':
            return _parse_hex(m, pos + 1, 8) is not None
        if '0' <= ch <= '9':
            return True
        return False
    # all underscores or empty
    return True


def _need_disambiguation(prev_component, mangled_next):
    """Port of Lean's needDisambiguation."""
    # Check if previous component (as a string) ends with '_'
    prev_ends_underscore = (isinstance(prev_component, str) and
                            len(prev_component) > 0 and
                            prev_component[-1] == '_')
    return prev_ends_underscore or _check_disambiguation(mangled_next)


def mangle_name(components, prefix="l_"):
    """
    Mangle a list of name components (str or int) into a C symbol.
    Port of Lean's Name.mangle.
    """
    if not components:
        return prefix

    parts = []
    prev = None
    for i, comp in enumerate(components):
        if isinstance(comp, int):
            if i == 0:
                parts.append(str(comp) + '_')
            else:
                parts.append('_' + str(comp) + '_')
        else:
            m = mangle_string(comp)
            if i == 0:
                if _check_disambiguation(m):
                    parts.append('00' + m)
                else:
                    parts.append(m)
            else:
                if _need_disambiguation(prev, m):
                    parts.append('_00' + m)
                else:
                    parts.append('_' + m)
        prev = comp

    return prefix + ''.join(parts)


# ---------------------------------------------------------------------------
# Name demangling
# ---------------------------------------------------------------------------

def demangle_body(s):
    """
    Demangle a string produced by Name.mangleAux (without prefix).
    Returns a list of components (str or int).

    This is a faithful port of Lean's Name.demangleAux from NameMangling.lean.
    """
    components = []
    length = len(s)

    def emit(comp):
        components.append(comp)

    def decode_num(pos, n):
        """Parse remaining digits, emit numeric component, continue."""
        while pos < length:
            ch = s[pos]
            if '0' <= ch <= '9':
                n = n * 10 + (ord(ch) - ord('0'))
                pos += 1
            else:
                # Expect '_' (trailing underscore of numeric encoding)
                pos += 1  # skip '_'
                emit(n)
                if pos >= length:
                    return pos
                # Skip separator '_' and go to name_start
                pos += 1
                return name_start(pos)
        # End of string
        emit(n)
        return pos

    def name_start(pos):
        """Start parsing a new name component."""
        if pos >= length:
            return pos
        ch = s[pos]
        pos += 1
        if '0' <= ch <= '9':
            # Check for '00' disambiguation
            if ch == '0' and pos < length and s[pos] == '0':
                pos += 1
                return demangle_main(pos, "", 0)
            else:
                return decode_num(pos, ord(ch) - ord('0'))
        elif ch == '_':
            return demangle_main(pos, "", 1)
        else:
            return demangle_main(pos, ch, 0)

    def demangle_main(pos, acc, ucount):
        """Main demangling loop."""
        while pos < length:
            ch = s[pos]
            pos += 1

            if ch == '_':
                ucount += 1
                continue

            if ucount % 2 == 0:
                # Even underscores: literal underscores in component name
                acc += '_' * (ucount // 2) + ch
                ucount = 0
                continue

            # Odd ucount: separator or escape
            if '0' <= ch <= '9':
                # End current str component, start number
                emit(acc + '_' * (ucount // 2))
                if ch == '0' and pos < length and s[pos] == '0':
                    pos += 1
                    return demangle_main(pos, "", 0)
                else:
                    return decode_num(pos, ord(ch) - ord('0'))

            # Try hex escapes
            if ch == 'x':
                result = _parse_hex(s, pos, 2)
                if result is not None:
                    new_pos, val = result
                    acc += '_' * (ucount // 2) + chr(val)
                    pos = new_pos
                    ucount = 0
                    continue

            if ch == 'u':
                result = _parse_hex(s, pos, 4)
                if result is not None:
                    new_pos, val = result
                    acc += '_' * (ucount // 2) + chr(val)
                    pos = new_pos
                    ucount = 0
                    continue

            if ch == 'U':
                result = _parse_hex(s, pos, 8)
                if result is not None:
                    new_pos, val = result
                    acc += '_' * (ucount // 2) + chr(val)
                    pos = new_pos
                    ucount = 0
                    continue

            # Name separator
            emit(acc)
            acc = '_' * (ucount // 2) + ch
            ucount = 0

        # End of string
        acc += '_' * (ucount // 2)
        if acc:
            emit(acc)
        return pos

    name_start(0)
    return components


# ---------------------------------------------------------------------------
# Prefix handling for lp_ (package prefix)
# ---------------------------------------------------------------------------

def _is_valid_string_mangle(s):
    """Check if s is a valid output of String.mangle (no trailing bare _)."""
    pos = 0
    length = len(s)
    while pos < length:
        ch = s[pos]
        if _is_ascii_alnum(ch):
            pos += 1
        elif ch == '_':
            if pos + 1 >= length:
                return False  # trailing bare _
            nch = s[pos + 1]
            if nch == '_':
                pos += 2
            elif nch == 'x' and _parse_hex(s, pos + 2, 2) is not None:
                pos = _parse_hex(s, pos + 2, 2)[0]
            elif nch == 'u' and _parse_hex(s, pos + 2, 4) is not None:
                pos = _parse_hex(s, pos + 2, 4)[0]
            elif nch == 'U' and _parse_hex(s, pos + 2, 8) is not None:
                pos = _parse_hex(s, pos + 2, 8)[0]
            else:
                return False
        else:
            return False
    return True


def _skip_string_mangle(s, pos):
    """
    Skip past a String.mangle output in s starting at pos.
    Returns the position after the mangled string (where we expect the separator '_').
    This is a greedy scan.
    """
    length = len(s)
    while pos < length:
        ch = s[pos]
        if _is_ascii_alnum(ch):
            pos += 1
        elif ch == '_':
            if pos + 1 < length:
                nch = s[pos + 1]
                if nch == '_':
                    pos += 2
                elif nch == 'x' and _parse_hex(s, pos + 2, 2) is not None:
                    pos = _parse_hex(s, pos + 2, 2)[0]
                elif nch == 'u' and _parse_hex(s, pos + 2, 4) is not None:
                    pos = _parse_hex(s, pos + 2, 4)[0]
                elif nch == 'U' and _parse_hex(s, pos + 2, 8) is not None:
                    pos = _parse_hex(s, pos + 2, 8)[0]
                else:
                    return pos  # bare '_': separator
            else:
                return pos
        else:
            return pos
    return pos


def _find_lp_body(s):
    """
    Given s = everything after 'lp_' in a symbol, find where the declaration
    body (Name.mangleAux output) starts.
    Returns the start index of the body within s, or None.

    Strategy: try all candidate split points where the package part is a valid
    String.mangle output and the body round-trips. Prefer the longest valid
    package name (most specific match).
    """
    length = len(s)

    # Collect candidate split positions: every '_' that could be the separator
    candidates = []
    pos = 0
    while pos < length:
        if s[pos] == '_':
            candidates.append(pos)
        pos += 1

    # Try each candidate; collect all valid splits
    valid_splits = []
    for split_pos in candidates:
        pkg_part = s[:split_pos]
        if not pkg_part:
            continue
        if not _is_valid_string_mangle(pkg_part):
            continue
        body = s[split_pos + 1:]
        if not body:
            continue
        components = demangle_body(body)
        if not components:
            continue
        remangled = mangle_name(components, prefix="")
        if remangled == body:
            first = components[0]
            # Score: prefer first component starting with uppercase
            has_upper = isinstance(first, str) and first and first[0].isupper()
            valid_splits.append((split_pos, has_upper))

    if valid_splits:
        # Among splits where first decl component starts uppercase, pick longest pkg.
        # Otherwise pick shortest pkg.
        upper_splits = [s for s in valid_splits if s[1]]
        if upper_splits:
            best = max(upper_splits, key=lambda x: x[0])
        else:
            best = min(valid_splits, key=lambda x: x[0])
        return best[0] + 1

    # Fallback: greedy String.mangle scan
    greedy_pos = _skip_string_mangle(s, 0)
    if greedy_pos < length and s[greedy_pos] == '_':
        return greedy_pos + 1

    return None


# ---------------------------------------------------------------------------
# Format name components for display
# ---------------------------------------------------------------------------

def format_name(components):
    """Format a list of name components as a dot-separated string."""
    return '.'.join(str(c) for c in components)


# ---------------------------------------------------------------------------
# Human-friendly postprocessing
# ---------------------------------------------------------------------------

# Compiler-generated suffix components — exact match
_SUFFIX_FLAGS_EXACT = {
    '_redArg':  'arity\u2193',
    '_boxed':   'boxed',
    '_impl':    'impl',
}

# Compiler-generated suffix prefixes — match with optional _N index
# e.g., _lam, _lam_0, _lam_3, _lambda_0, _closed_2
_SUFFIX_FLAGS_PREFIX = {
    '_lam':     '\u03bb',
    '_lambda':  '\u03bb',
    '_elam':    '\u03bb',
    '_jp':      'jp',
    '_closed':  'closed',
}


def _match_suffix(component):
    """
    Check if a string component is a compiler-generated suffix.
    Returns the flag label or None.

    Handles both exact matches (_redArg, _boxed) and indexed suffixes
    (_lam_0, _lambda_2, _closed_0) produced by appendIndexAfter.
    """
    if not isinstance(component, str):
        return None
    if component in _SUFFIX_FLAGS_EXACT:
        return _SUFFIX_FLAGS_EXACT[component]
    if component in _SUFFIX_FLAGS_PREFIX:
        return _SUFFIX_FLAGS_PREFIX[component]
    # Check for indexed suffix: prefix + _N
    for prefix, label in _SUFFIX_FLAGS_PREFIX.items():
        if component.startswith(prefix + '_'):
            rest = component[len(prefix) + 1:]
            if rest.isdigit():
                return label
    return None


def _strip_private(components):
    """Strip _private.Module.0. prefix. Returns (stripped_parts, is_private)."""
    if (len(components) >= 3 and isinstance(components[0], str) and
            components[0] == '_private'):
        for i in range(1, len(components)):
            if components[i] == 0:
                if i + 1 < len(components):
                    return components[i + 1:], True
                break
    return components, False


def _strip_spec_suffixes(components):
    """Strip trailing spec_N components (from appendIndexAfter)."""
    parts = list(components)
    while parts and isinstance(parts[-1], str) and parts[-1].startswith('spec_'):
        rest = parts[-1][5:]
        if rest.isdigit():
            parts.pop()
        else:
            break
    return parts


def _is_spec_index(component):
    """Check if a component is a spec_N index (from appendIndexAfter)."""
    return (isinstance(component, str) and
            component.startswith('spec_') and component[5:].isdigit())


def _parse_spec_entries(rest):
    """Parse _at_..._spec pairs into separate spec context entries.

    Given components starting from the first _at_, returns:
    - entries: list of component lists, one per _at_..._spec block
    - remaining: components after the last _spec N (trailing suffixes)
    """
    entries = []
    current_ctx = None
    remaining = []
    skip_next = False

    for p in rest:
        if skip_next:
            skip_next = False
            continue
        if isinstance(p, str) and p == '_at_':
            if current_ctx is not None:
                entries.append(current_ctx)
            current_ctx = []
            continue
        if isinstance(p, str) and p == '_spec':
            if current_ctx is not None:
                entries.append(current_ctx)
                current_ctx = None
            skip_next = True
            continue
        if isinstance(p, str) and p.startswith('_spec'):
            if current_ctx is not None:
                entries.append(current_ctx)
                current_ctx = None
            continue
        if current_ctx is not None:
            current_ctx.append(p)
        else:
            remaining.append(p)

    if current_ctx is not None:
        entries.append(current_ctx)

    return entries, remaining


def _process_spec_context(components):
    """Process a spec context into a clean name and its flags.

    Returns (name_parts, flags) where name_parts are the cleaned components
    and flags is a deduplicated list of flag labels from compiler suffixes.
    """
    parts = list(components)
    parts, _ = _strip_private(parts)

    name_parts = []
    ctx_flags = []
    seen = set()

    for p in parts:
        flag = _match_suffix(p)
        if flag is not None:
            if flag not in seen:
                ctx_flags.append(flag)
                seen.add(flag)
        elif _is_spec_index(p):
            pass
        else:
            name_parts.append(p)

    return name_parts, ctx_flags


def postprocess_name(components):
    """
    Transform raw demangled components into a human-friendly display string.

    Applies:
    - Private name cleanup: _private.Module.0.Name.foo -> Name.foo [private]
    - Hygienic name cleanup: strips _@.module._hygCtx._hyg.N
    - Suffix folding: _redArg, _boxed, _lam_0, etc. -> [flags]
    - Specialization: f._at_.g._spec.N -> f spec at g
      Shown after base [flags], with context flags: spec at g[ctx_flags]
    """
    if not components:
        return ""

    parts = list(components)
    flags = []
    spec_entries = []

    # --- Strip _private prefix ---
    parts, is_private = _strip_private(parts)

    # --- Strip hygienic suffixes: everything from _@ onward ---
    at_idx = None
    for i, p in enumerate(parts):
        if isinstance(p, str) and p.startswith('_@'):
            at_idx = i
            break
    if at_idx is not None:
        parts = parts[:at_idx]

    # --- Handle specialization: _at_ ... _spec N ---
    at_positions = [i for i, p in enumerate(parts)
                    if isinstance(p, str) and p == '_at_']
    if at_positions:
        first_at = at_positions[0]
        base = parts[:first_at]
        rest = parts[first_at:]

        entries, remaining = _parse_spec_entries(rest)
        for ctx_components in entries:
            ctx_name, ctx_flags = _process_spec_context(ctx_components)
            if ctx_name or ctx_flags:
                spec_entries.append((ctx_name, ctx_flags))

        parts = base + remaining

    # --- Collect suffix flags from the end ---
    while parts:
        last = parts[-1]
        flag = _match_suffix(last)
        if flag is not None:
            flags.append(flag)
            parts.pop()
        elif isinstance(last, int) and len(parts) >= 2:
            prev_flag = _match_suffix(parts[-2])
            if prev_flag is not None:
                flags.append(prev_flag)
                parts.pop()  # remove the number
                parts.pop()  # remove the suffix
            else:
                break
        else:
            break

    if is_private:
        flags.append('private')

    # --- Format result ---
    name = '.'.join(str(c) for c in parts) if parts else '?'
    result = name
    if flags:
        flag_str = ', '.join(flags)
        result += f' [{flag_str}]'

    for ctx_name, ctx_flags in spec_entries:
        ctx_str = '.'.join(str(c) for c in ctx_name) if ctx_name else '?'
        if ctx_flags:
            ctx_flag_str = ', '.join(ctx_flags)
            result += f' spec at {ctx_str}[{ctx_flag_str}]'
        else:
            result += f' spec at {ctx_str}'

    return result


# ---------------------------------------------------------------------------
# Main demangling entry point
# ---------------------------------------------------------------------------

def demangle_lean_name_raw(mangled):
    """
    Demangle a Lean C symbol, preserving all internal name components.

    Returns the exact demangled name with all compiler-generated suffixes
    intact. Use demangle_lean_name() for human-friendly output.
    """
    try:
        return _demangle_lean_name_inner(mangled, human_friendly=False)
    except Exception:
        return mangled


def demangle_lean_name(mangled):
    """
    Demangle a C symbol name produced by the Lean 4 compiler.

    Returns a human-friendly demangled name with compiler suffixes folded
    into readable flags. Use demangle_lean_name_raw() to preserve all
    internal components.
    """
    try:
        return _demangle_lean_name_inner(mangled, human_friendly=True)
    except Exception:
        return mangled


def _demangle_lean_name_inner(mangled, human_friendly=True):
    """Inner demangle that may raise on malformed input."""

    if mangled == "_lean_main":
        return "[lean] main"

    # Handle lean_ runtime functions
    if human_friendly and mangled.startswith("lean_apply_"):
        rest = mangled[11:]
        if rest.isdigit():
            return f"<apply/{rest}>"

    # Strip .cold.N suffix (LLVM linker cold function clones)
    cold_suffix = ""
    core = mangled
    dot_pos = core.find('.cold.')
    if dot_pos >= 0:
        cold_suffix = " " + core[dot_pos:]
        core = core[:dot_pos]
    elif core.endswith('.cold'):
        cold_suffix = " .cold"
        core = core[:-5]

    result = _demangle_core(core, human_friendly)
    if result is None:
        return mangled
    return result + cold_suffix


def _demangle_core(mangled, human_friendly=True):
    """Demangle a symbol without .cold suffix. Returns None if not a Lean name."""

    fmt = postprocess_name if human_friendly else format_name

    # _init_ prefix
    if mangled.startswith("_init_"):
        rest = mangled[6:]
        body, pkg_display = _strip_lean_prefix(rest)
        if body is None:
            return None
        components = demangle_body(body)
        if not components:
            return None
        name = fmt(components)
        if pkg_display:
            return f"[init] {name} ({pkg_display})"
        return f"[init] {name}"

    # initialize_ prefix (module init functions)
    if mangled.startswith("initialize_"):
        rest = mangled[11:]
        # With package: initialize_lp_{pkg}_{body} or initialize_l_{body}
        body, pkg_display = _strip_lean_prefix(rest)
        if body is not None:
            components = demangle_body(body)
            if components:
                name = fmt(components)
                if pkg_display:
                    return f"[module_init] {name} ({pkg_display})"
                return f"[module_init] {name}"
        # Without package: initialize_{Name.mangleAux(moduleName)}
        if rest:
            components = demangle_body(rest)
            if components:
                return f"[module_init] {fmt(components)}"
        return None

    # l_ or lp_ prefix
    body, pkg_display = _strip_lean_prefix(mangled)
    if body is None:
        return None
    components = demangle_body(body)
    if not components:
        return None
    name = fmt(components)
    if pkg_display:
        return f"{name} ({pkg_display})"
    return name


def _strip_lean_prefix(s):
    """
    Strip the l_ or lp_ prefix from a mangled symbol.
    Returns (body, pkg_display) where body is the Name.mangleAux output
    and pkg_display is None or a string describing the package.
    Returns (None, None) if the string doesn't have a recognized prefix.
    """
    if s.startswith("l_"):
        return (s[2:], None)

    if s.startswith("lp_"):
        after_lp = s[3:]
        body_start = _find_lp_body(after_lp)
        if body_start is not None:
            pkg_mangled = after_lp[:body_start - 1]
            # Unmangle the package name
            pkg_components = demangle_body(pkg_mangled)
            if pkg_components and len(pkg_components) == 1 and isinstance(pkg_components[0], str):
                pkg_display = pkg_components[0]
            else:
                pkg_display = pkg_mangled
            return (after_lp[body_start:], pkg_display)
        # Fallback: treat everything after lp_ as body
        return (after_lp, "?")

    return (None, None)


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def main():
    """Filter stdin or arguments, demangling Lean names."""
    import argparse
    parser = argparse.ArgumentParser(
        description="Demangle Lean 4 C symbol names (like c++filt for Lean)")
    parser.add_argument('names', nargs='*',
                        help='Names to demangle (reads stdin if none given)')
    parser.add_argument('--raw', action='store_true',
                        help='Output exact demangled names without postprocessing')
    args = parser.parse_args()

    demangle = demangle_lean_name_raw if args.raw else demangle_lean_name

    if args.names:
        for name in args.names:
            print(demangle(name))
    else:
        for line in sys.stdin:
            print(demangle(line.rstrip('\n')))


if __name__ == '__main__':
    main()
