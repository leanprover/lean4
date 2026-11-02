#!/usr/bin/env python3
"""
Generate the native symbol table and the export list of `lean.js`.

Usage: wasm_symbols.py --nm NM --registry OUT.c --exports OUT.json --lean ARCHIVE... --runtime ARCHIVE...

The interpreter switches to native code by looking up a declaration's mangled symbol at run time
(`lookup_symbol_in_cur_exe` in `src/library/ir_interpreter.cpp`). Natively the dynamic symbol table of
`libleanshared.so` answers that; in `lean.js` the table lives inside the module instead, because Emscripten's
`dlsym` enumerates every export on each call and every export costs JavaScript in every pthread.

The table holds every global symbol of the Lean archives (`libInit.a`, `libStd.a`, `libLean.a`): the compiled
declarations, their constants and the module initializers. Their wasm object files give each function's type, so
the table's declarations match the definitions exactly. The export list for `-sEXPORTED_FUNCTIONS=@file` holds the
global symbols of the runtime archives, which the interpreter still resolves through `dlsym`.
"""
import argparse
import json
import os
import struct
import subprocess
import sys

# Emscripten's own metadata symbols never survive as wasm exports, and the link synthesizes `main` from its
# `__main_argc_argv`/`__main_void` alias, which therefore cannot be requested
NOT_EXPORTED = ('_Z', '__em_js__', '__em_lib_deps_', '__start_em_', '__stop_em_')
MAIN_ALIASES = ('__main_argc_argv', '__main_void')
VALTYPES = {0x7f: 'int', 0x7e: 'long long', 0x7d: 'float', 0x7c: 'double'}
SYM_BINDING_LOCAL, SYM_UNDEFINED, SYM_EXPLICIT_NAME = 0x2, 0x10, 0x40


class Reader:
    def __init__(self, data):
        self.data, self.pos = data, 0

    def byte(self):
        self.pos += 1
        return self.data[self.pos - 1]

    def leb(self):
        result = shift = 0
        while True:
            b = self.byte()
            result |= (b & 0x7f) << shift
            shift += 7
            if not b & 0x80:
                return result

    def bytes(self, n):
        self.pos += n
        return self.data[self.pos - n:self.pos]

    def name(self):
        return self.bytes(self.leb()).decode()

    def done(self):
        return self.pos >= len(self.data)


def archive_members(path):
    """(name, data) of every member of a GNU `ar` archive"""
    with open(path, 'rb') as f:
        data = f.read()
    if data[:8] != b'!<arch>\n':
        sys.exit(f'wasm_symbols.py: {path} is not an ar archive')
    pos, long_names = 8, b''
    while pos + 60 <= len(data):
        header = data[pos:pos + 60]
        name, size = header[:16].decode().rstrip(), int(header[48:58])
        body = data[pos + 60:pos + 60 + size]
        pos += 60 + size + (size & 1)
        if name == '//':
            long_names = body
        elif name.startswith('/') and name[1:].isdigit():
            start = int(name[1:])
            yield long_names[start:long_names.index(b'\n', start)].decode().rstrip('/'), body
        elif name != '/':
            yield name.rstrip('/'), body


def wasm_symbols(data):
    """name -> (params, results) for the defined global functions, name -> None for the defined global data"""
    r = Reader(data)
    if r.bytes(4) != b'\0asm':
        return None
    r.bytes(4)
    types, imported_functions, function_types, linking = [], 0, [], None
    while not r.done():
        section_id, size = r.byte(), r.leb()
        section = Reader(r.bytes(size))
        if section_id == 1:
            for _ in range(section.leb()):
                section.byte()
                params = [VALTYPES[section.byte()] for _ in range(section.leb())]
                results = [VALTYPES[section.byte()] for _ in range(section.leb())]
                types.append((params, results))
        elif section_id == 2:
            for _ in range(section.leb()):
                section.name(), section.name()
                kind = section.byte()
                if kind == 0:
                    imported_functions += 1
                    section.leb()
                elif kind in (1, 2):  # table: reftype then limits; memory: limits
                    if kind == 1:
                        section.byte()
                    flags = section.byte()
                    section.leb()
                    if flags & 1:
                        section.leb()
                elif kind == 3:
                    section.byte(), section.byte()
                elif kind == 4:
                    section.byte(), section.leb()
        elif section_id == 3:
            function_types = [section.leb() for _ in range(section.leb())]
        elif section_id == 0 and section.name() == 'linking':
            linking = section
    symbols = {}
    if linking is None:
        return symbols
    linking.leb()
    while not linking.done():
        subsection_id, size = linking.byte(), linking.leb()
        sub = Reader(linking.bytes(size))
        if subsection_id != 8:
            continue
        for _ in range(sub.leb()):
            kind, flags = sub.byte(), sub.leb()
            defined = not flags & SYM_UNDEFINED
            if kind == 0:
                index = sub.leb()
                if defined or flags & SYM_EXPLICIT_NAME:
                    name = sub.name()
                if defined and not flags & SYM_BINDING_LOCAL:
                    symbols[name] = types[function_types[index - imported_functions]]
            elif kind == 1:
                name = sub.name()
                if defined:
                    sub.leb(), sub.leb(), sub.leb()
                    if not flags & SYM_BINDING_LOCAL:
                        symbols[name] = None
            elif kind in (2, 4, 5):
                sub.leb()
                if defined or flags & SYM_EXPLICIT_NAME:
                    sub.name()
            elif kind == 3:
                sub.leb()
    return symbols


def list_symbols(nm, archive):
    """name -> set of `nm` type letters of the global symbols defined in `archive`"""
    out = subprocess.run([nm, '--defined-only', '--extern-only', '--format=posix', archive],
                         check=True, capture_output=True, text=True).stdout
    symbols = {}
    for line in out.splitlines():
        fields = line.split()
        if len(fields) < 2 or line.endswith(':'):
            continue
        symbols.setdefault(fields[0], set()).add(fields[1])
    return symbols


def write_if_changed(path, content):
    if os.path.exists(path):
        with open(path, encoding='utf-8') as f:
            if f.read() == content:
                return False
    with open(path, 'w', encoding='utf-8') as f:
        f.write(content)
    return True


def declaration(name, signature):
    if signature is None:
        return f'extern char {name}[];'
    params, results = signature
    return f'extern {results[0] if results else "void"} {name}({", ".join(params) or "void"});'


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--nm', required=True, help='llvm-nm (or emnm) that understands the archives')
    ap.add_argument('--registry', required=True, help='C file to write')
    ap.add_argument('--exports', required=True, help='JSON file to write (EXPORTED_FUNCTIONS=@file)')
    ap.add_argument('--lean', nargs='+', required=True, help='the archives of compiled Lean code (wasm objects)')
    ap.add_argument('--runtime', nargs='+', required=True, help='the C and C++ archives')
    args = ap.parse_args()

    table = {}
    for archive in args.lean:
        for member, data in archive_members(archive):
            symbols = wasm_symbols(data)
            if symbols is None:
                sys.exit(f'wasm_symbols.py: {archive}({member}) is not a wasm object')
            table.update(symbols)
        listed = set(list_symbols(args.nm, archive))
        if listed != set(table) & listed or not listed <= set(table):
            sys.exit(f'wasm_symbols.py: the symbols read from {archive} differ from what {args.nm} lists: '
                     f'{sorted(listed ^ (set(table) & listed) | (listed - set(table)))[:10]}')
    runtime = {}
    for archive in args.runtime:
        runtime.update(list_symbols(args.nm, archive))
    if not all(name.isascii() for name in list(table) + list(runtime)):
        sys.exit('wasm_symbols.py: non-ASCII symbol name')
    exported = sorted(name for name in runtime
                      if name not in table and name.isidentifier()
                      and not name.startswith(NOT_EXPORTED) and name not in MAIN_ALIASES)

    names = sorted(table)
    lines = ['// Generated by script/wasm_symbols.py from the Lean archives that `lean.js` links; do not edit.',
             '#include <string.h>', '']
    lines += [declaration(name, table[name]) for name in names]
    lines += ['', 'static const struct { const char * name; void * addr; } lean_native_symbols[] = {']
    lines += [f'    {{"{name}", (void *){"&" if table[name] is not None else ""}{name}}},' for name in names]
    lines += ['};', '',
              '// the interpreter\'s symbol lookup on Emscripten, see `lookup_symbol_in_cur_exe`',
              'void * lean_lookup_native_symbol(char const * name) {',
              '    size_t lo = 0, hi = sizeof(lean_native_symbols) / sizeof(lean_native_symbols[0]);',
              '    while (lo < hi) {',
              '        size_t mid = lo + (hi - lo) / 2;',
              '        int c = strcmp(name, lean_native_symbols[mid].name);',
              '        if (c == 0) {',
              '            return lean_native_symbols[mid].addr;',
              '        } else if (c < 0) {',
              '            hi = mid;',
              '        } else {',
              '            lo = mid + 1;',
              '        }',
              '    }',
              '    return NULL;',
              '}', '']
    registry_changed = write_if_changed(args.registry, '\n'.join(lines))

    exports = sorted(set(['_' + name for name in exported] + ['_main', '_malloc', '_free', '_lean_lookup_native_symbol']))
    exports_changed = write_if_changed(args.exports, json.dumps(exports, indent=1) + '\n')

    functions = sum(1 for name in names if table[name] is not None)
    print(f'wasm_symbols.py: {len(names)} symbols in the table ({functions} functions, {len(names) - functions} data), '
          f'{len(exports)} exports; {"rewrote" if registry_changed else "kept"} {args.registry}, '
          f'{"rewrote" if exports_changed else "kept"} {args.exports}')


if __name__ == '__main__':
    main()
