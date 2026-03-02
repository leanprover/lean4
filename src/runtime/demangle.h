/*
Copyright (c) 2025 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once

/*
 * Demangle Lean symbol names in backtrace lines.
 *
 * lean_demangle_symbol(symbol):
 *   Given a mangled C symbol name (e.g. "l_Lean_Meta_Grind_foo"),
 *   returns a malloc'd string with the demangled name (e.g. "Lean.Meta.Grind.foo"),
 *   or nullptr if the symbol is not a Lean name.
 *
 * lean_demangle_bt_line(line):
 *   Given a backtrace line from backtrace_symbols(), extracts the symbol,
 *   demangles it, and returns a malloc'd string with the demangled name
 *   substituted in. Returns nullptr if nothing was demangled.
 *
 * Callers must free() non-null return values.
 */

char * lean_demangle_symbol(const char * symbol);
char * lean_demangle_bt_line(const char * line);
