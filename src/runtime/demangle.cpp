/*
Copyright (c) 2025 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura

C++ port of the Lean name demangling algorithm (Name.demangleAux from
NameMangling.lean) and human-friendly postprocessing. Used to make
runtime backtraces readable.
*/
#include <cstdlib>
#include <cstring>
#include <string>
#include <vector>
#include "runtime/demangle.h"

namespace {

// ---------------------------------------------------------------------------
// Name component: either a string or a number
// ---------------------------------------------------------------------------

struct Component {
    bool is_num;
    std::string str;
    unsigned num;
    Component() : is_num(false), num(0) {}
    static Component mk_str(std::string s) { Component c; c.str = std::move(s); return c; }
    static Component mk_str(char ch) { Component c; c.str = std::string(1, ch); return c; }
    static Component mk_num(unsigned n) { Component c; c.is_num = true; c.num = n; return c; }
};

using Components = std::vector<Component>;

// ---------------------------------------------------------------------------
// Hex parsing and UTF-8 encoding
// ---------------------------------------------------------------------------

int parse_hex(const char * s, int pos, int len, int n_digits, unsigned & out_val) {
    if (pos + n_digits > len) return 0;
    unsigned val = 0;
    for (int i = 0; i < n_digits; i++) {
        char c = s[pos + i];
        if (c >= '0' && c <= '9')
            val = (val << 4) | (unsigned)(c - '0');
        else if (c >= 'a' && c <= 'f')
            val = (val << 4) | (unsigned)(c - 'a' + 10);
        else
            return 0;
    }
    out_val = val;
    return n_digits;
}

void append_utf8(std::string & out, unsigned cp) {
    if (cp < 0x80) {
        out += (char)cp;
    } else if (cp < 0x800) {
        out += (char)(0xC0 | (cp >> 6));
        out += (char)(0x80 | (cp & 0x3F));
    } else if (cp < 0x10000) {
        out += (char)(0xE0 | (cp >> 12));
        out += (char)(0x80 | ((cp >> 6) & 0x3F));
        out += (char)(0x80 | (cp & 0x3F));
    } else if (cp < 0x110000) {
        out += (char)(0xF0 | (cp >> 18));
        out += (char)(0x80 | ((cp >> 12) & 0x3F));
        out += (char)(0x80 | ((cp >> 6) & 0x3F));
        out += (char)(0x80 | (cp & 0x3F));
    }
}

// ---------------------------------------------------------------------------
// Core demangling: produces a component list
// Port of Name.demangleAux from NameMangling.lean
// ---------------------------------------------------------------------------

void demangle_main(const char * s, int pos, int len,
                   std::string & acc, int ucount, Components & out);
void name_start(const char * s, int pos, int len, Components & out);

void decode_num(const char * s, int pos, int len,
                unsigned n, Components & out) {
    while (pos < len) {
        char ch = s[pos];
        if (ch >= '0' && ch <= '9') {
            n = n * 10 + (unsigned)(ch - '0');
            pos++;
        } else {
            pos++; // skip trailing '_'
            out.push_back(Component::mk_num(n));
            if (pos >= len) return;
            pos++; // skip separator '_'
            name_start(s, pos, len, out);
            return;
        }
    }
    out.push_back(Component::mk_num(n));
}

void name_start(const char * s, int pos, int len, Components & out) {
    if (pos >= len) return;
    char ch = s[pos];
    pos++;
    if (ch >= '0' && ch <= '9') {
        if (ch == '0' && pos < len && s[pos] == '0') {
            pos++;
            std::string acc;
            demangle_main(s, pos, len, acc, 0, out);
        } else {
            decode_num(s, pos, len, (unsigned)(ch - '0'), out);
        }
    } else if (ch == '_') {
        std::string acc;
        demangle_main(s, pos, len, acc, 1, out);
    } else {
        std::string acc(1, ch);
        demangle_main(s, pos, len, acc, 0, out);
    }
}

void demangle_main(const char * s, int pos, int len,
                   std::string & acc, int ucount, Components & out) {
    while (pos < len) {
        char ch = s[pos];
        pos++;

        if (ch == '_') { ucount++; continue; }

        if (ucount % 2 == 0) {
            for (int i = 0; i < ucount / 2; i++) acc += '_';
            acc += ch;
            ucount = 0;
            continue;
        }

        // Odd ucount: separator or escape
        if (ch >= '0' && ch <= '9') {
            for (int i = 0; i < ucount / 2; i++) acc += '_';
            out.push_back(Component::mk_str(std::move(acc)));
            if (ch == '0' && pos < len && s[pos] == '0') {
                pos++;
                acc.clear();
                demangle_main(s, pos, len, acc, 0, out);
                return;
            } else {
                decode_num(s, pos, len, (unsigned)(ch - '0'), out);
                return;
            }
        }

        unsigned hex_val;
        int consumed;
        if (ch == 'x') {
            consumed = parse_hex(s, pos, len, 2, hex_val);
            if (consumed > 0) {
                for (int i = 0; i < ucount / 2; i++) acc += '_';
                append_utf8(acc, hex_val);
                pos += consumed; ucount = 0; continue;
            }
        }
        if (ch == 'u') {
            consumed = parse_hex(s, pos, len, 4, hex_val);
            if (consumed > 0) {
                for (int i = 0; i < ucount / 2; i++) acc += '_';
                append_utf8(acc, hex_val);
                pos += consumed; ucount = 0; continue;
            }
        }
        if (ch == 'U') {
            consumed = parse_hex(s, pos, len, 8, hex_val);
            if (consumed > 0) {
                for (int i = 0; i < ucount / 2; i++) acc += '_';
                append_utf8(acc, hex_val);
                pos += consumed; ucount = 0; continue;
            }
        }

        // Name separator
        out.push_back(Component::mk_str(std::move(acc)));
        acc.clear();
        for (int i = 0; i < ucount / 2; i++) acc += '_';
        acc += ch;
        ucount = 0;
    }

    for (int i = 0; i < ucount / 2; i++) acc += '_';
    if (!acc.empty())
        out.push_back(Component::mk_str(std::move(acc)));
}

bool demangle_body(const char * s, int len, Components & out) {
    if (len == 0) return false;
    name_start(s, 0, len, out);
    return !out.empty();
}

// Convenience: demangle to flat dot-separated string (used for lp_ validation)
bool demangle_body_flat(const char * s, int len, std::string & out) {
    Components comps;
    if (!demangle_body(s, len, comps)) return false;
    for (size_t i = 0; i < comps.size(); i++) {
        if (i > 0) out += '.';
        if (comps[i].is_num) out += std::to_string(comps[i].num);
        else out += comps[i].str;
    }
    return true;
}

// ---------------------------------------------------------------------------
// Format components as dot-separated string
// ---------------------------------------------------------------------------

std::string format_name(const Components & comps) {
    std::string out;
    for (size_t i = 0; i < comps.size(); i++) {
        if (i > 0) out += '.';
        if (comps[i].is_num) out += std::to_string(comps[i].num);
        else out += comps[i].str;
    }
    return out;
}

// ---------------------------------------------------------------------------
// Human-friendly postprocessing
// Port of postprocess_name from lean_demangle.py
// ---------------------------------------------------------------------------

// Suffix flag labels (UTF-8 encoded)
static const char * FLAG_ARITY_DOWN = "arity\xe2\x86\x93";  // arity↓
static const char * FLAG_BOXED     = "boxed";
static const char * FLAG_IMPL      = "impl";
static const char * FLAG_LAMBDA    = "\xce\xbb";             // λ
static const char * FLAG_JP        = "jp";
static const char * FLAG_CLOSED    = "closed";

// Check if a string consists entirely of ASCII digits.
bool is_all_digits(const char * s) {
    if (!*s) return false;
    while (*s) { if (*s < '0' || *s > '9') return false; s++; }
    return true;
}

bool starts_with_str(const std::string & s, const char * prefix) {
    size_t plen = strlen(prefix);
    return s.size() >= plen && s.compare(0, plen, prefix) == 0;
}

// Match a compiler-generated suffix component. Returns flag label or nullptr.
const char * match_suffix(const Component & c) {
    if (c.is_num) return nullptr;
    const std::string & s = c.str;
    // Exact matches
    if (s == "_redArg") return FLAG_ARITY_DOWN;
    if (s == "_boxed")  return FLAG_BOXED;
    if (s == "_impl")   return FLAG_IMPL;
    // Exact or indexed prefix matches
    if (s == "_lam" || s == "_lambda" || s == "_elam") return FLAG_LAMBDA;
    if (s == "_jp") return FLAG_JP;
    if (s == "_closed") return FLAG_CLOSED;
    // Indexed: _lam_N, _lambda_N, _elam_N, _jp_N, _closed_N
    struct { const char * prefix; size_t len; const char * flag; } indexed[] = {
        {"_lam_",    5, FLAG_LAMBDA},
        {"_lambda_", 8, FLAG_LAMBDA},
        {"_elam_",   6, FLAG_LAMBDA},
        {"_jp_",     4, FLAG_JP},
        {"_closed_", 8, FLAG_CLOSED},
    };
    for (auto & e : indexed) {
        if (s.size() > e.len && s.compare(0, e.len, e.prefix) == 0 &&
            is_all_digits(s.c_str() + e.len))
            return e.flag;
    }
    return nullptr;
}

// Check if component is a spec_N index.
bool is_spec_index(const Component & c) {
    if (c.is_num) return false;
    return starts_with_str(c.str, "spec_") && c.str.size() > 5 &&
           is_all_digits(c.str.c_str() + 5);
}

// Strip _private.Module.0. prefix. Returns (begin index past the strip, is_private).
struct StripResult { size_t begin; bool is_private; };

StripResult strip_private(const Components & parts, size_t begin, size_t end) {
    if (end - begin >= 3 && !parts[begin].is_num && parts[begin].str == "_private") {
        for (size_t i = begin + 1; i < end; i++) {
            if (parts[i].is_num && parts[i].num == 0) {
                if (i + 1 < end)
                    return {i + 1, true};
                break;
            }
        }
    }
    return {begin, false};
}

// Spec context entry: name components + context flags
struct SpecEntry {
    std::string name;
    std::vector<const char *> flags;
};

// Process a spec context: strip private, collect flags, format name
SpecEntry process_spec_context(const Components & comps, size_t begin, size_t end) {
    SpecEntry entry;
    auto sr = strip_private(comps, begin, end);

    std::vector<const char *> seen_flags;
    std::string name;
    bool first = true;

    for (size_t i = sr.begin; i < end; i++) {
        const char * flag = match_suffix(comps[i]);
        if (flag) {
            // Deduplicate
            bool dup = false;
            for (auto f : entry.flags) { if (f == flag) { dup = true; break; } }
            if (!dup) entry.flags.push_back(flag);
        } else if (is_spec_index(comps[i])) {
            // skip
        } else {
            if (!first) name += '.';
            if (comps[i].is_num) name += std::to_string(comps[i].num);
            else name += comps[i].str;
            first = false;
        }
    }
    entry.name = std::move(name);
    return entry;
}

std::string postprocess_name(const Components & components) {
    if (components.empty()) return "";

    size_t n = components.size();

    // --- Strip _private prefix ---
    auto sr = strip_private(components, 0, n);
    size_t begin = sr.begin;
    bool is_private = sr.is_private;

    // Copy relevant range into a working vector
    Components parts(components.begin() + begin, components.begin() + n);

    // --- Strip hygienic suffixes: everything from _@ onward ---
    {
        size_t cut = parts.size();
        for (size_t i = 0; i < parts.size(); i++) {
            if (!parts[i].is_num && starts_with_str(parts[i].str, "_@")) {
                cut = i;
                break;
            }
        }
        parts.resize(cut);
    }

    // --- Handle specialization: _at_ ... _spec N ---
    std::vector<SpecEntry> spec_entries;
    {
        // Find first _at_
        int first_at = -1;
        for (size_t i = 0; i < parts.size(); i++) {
            if (!parts[i].is_num && parts[i].str == "_at_") {
                first_at = (int)i;
                break;
            }
        }

        if (first_at >= 0) {
            Components base(parts.begin(), parts.begin() + first_at);
            // Parse _at_..._spec entries
            Components current_ctx;
            bool in_ctx = false;
            Components remaining;
            bool skip_next = false;

            for (size_t i = first_at; i < parts.size(); i++) {
                if (skip_next) { skip_next = false; continue; }
                if (!parts[i].is_num && parts[i].str == "_at_") {
                    if (in_ctx) {
                        auto entry = process_spec_context(current_ctx, 0, current_ctx.size());
                        if (!entry.name.empty() || !entry.flags.empty())
                            spec_entries.push_back(std::move(entry));
                        current_ctx.clear();
                    }
                    in_ctx = true;
                    continue;
                }
                if (!parts[i].is_num && parts[i].str == "_spec") {
                    if (in_ctx) {
                        auto entry = process_spec_context(current_ctx, 0, current_ctx.size());
                        if (!entry.name.empty() || !entry.flags.empty())
                            spec_entries.push_back(std::move(entry));
                        current_ctx.clear();
                        in_ctx = false;
                    }
                    skip_next = true;
                    continue;
                }
                if (!parts[i].is_num && starts_with_str(parts[i].str, "_spec")) {
                    if (in_ctx) {
                        auto entry = process_spec_context(current_ctx, 0, current_ctx.size());
                        if (!entry.name.empty() || !entry.flags.empty())
                            spec_entries.push_back(std::move(entry));
                        current_ctx.clear();
                        in_ctx = false;
                    }
                    continue;
                }
                if (in_ctx)
                    current_ctx.push_back(parts[i]);
                else
                    remaining.push_back(parts[i]);
            }
            if (in_ctx && !current_ctx.empty()) {
                auto entry = process_spec_context(current_ctx, 0, current_ctx.size());
                if (!entry.name.empty() || !entry.flags.empty())
                    spec_entries.push_back(std::move(entry));
            }

            parts = base;
            parts.insert(parts.end(), remaining.begin(), remaining.end());
        }
    }

    // --- Collect suffix flags from the end ---
    std::vector<const char *> flags;
    while (!parts.empty()) {
        const Component & last = parts.back();
        const char * flag = match_suffix(last);
        if (flag) {
            flags.push_back(flag);
            parts.pop_back();
        } else if (last.is_num && parts.size() >= 2) {
            const char * prev_flag = match_suffix(parts[parts.size() - 2]);
            if (prev_flag) {
                flags.push_back(prev_flag);
                parts.pop_back(); // number
                parts.pop_back(); // suffix
            } else {
                break;
            }
        } else {
            break;
        }
    }

    if (is_private) flags.push_back("private");

    // --- Format result ---
    std::string result = parts.empty() ? "?" : format_name(parts);

    if (!flags.empty()) {
        result += " [";
        for (size_t i = 0; i < flags.size(); i++) {
            if (i > 0) result += ", ";
            result += flags[i];
        }
        result += ']';
    }

    for (auto & entry : spec_entries) {
        std::string ctx_str = entry.name.empty() ? "?" : entry.name;
        if (!entry.flags.empty()) {
            result += " spec at " + ctx_str + "[";
            for (size_t i = 0; i < entry.flags.size(); i++) {
                if (i > 0) result += ", ";
                result += entry.flags[i];
            }
            result += ']';
        } else {
            result += " spec at " + ctx_str;
        }
    }

    return result;
}

// ---------------------------------------------------------------------------
// Prefix handling and lp_ splitting
// ---------------------------------------------------------------------------

const char * starts_with(const char * s, const char * prefix) {
    size_t plen = strlen(prefix);
    if (strncmp(s, prefix, plen) == 0) return s + plen;
    return nullptr;
}

bool has_upper_start(const char * s, int len) {
    if (len == 0) return false;
    int pos = 0;
    if (pos + 1 < len && s[pos] == '0' && s[pos + 1] == '0') pos += 2;
    while (pos < len && s[pos] == '_') pos++;
    if (pos >= len) return false;
    return s[pos] >= 'A' && s[pos] <= 'Z';
}

bool is_valid_string_mangle(const char * s, int end) {
    int pos = 0;
    while (pos < end) {
        char ch = s[pos];
        if ((ch >= 'a' && ch <= 'z') || (ch >= 'A' && ch <= 'Z') || (ch >= '0' && ch <= '9')) {
            pos++;
        } else if (ch == '_') {
            if (pos + 1 >= end) return false;
            char nch = s[pos + 1];
            unsigned v;
            if (nch == '_') { pos += 2; }
            else if (nch == 'x' && parse_hex(s, pos + 2, end, 2, v)) { pos += 4; }
            else if (nch == 'u' && parse_hex(s, pos + 2, end, 4, v)) { pos += 6; }
            else if (nch == 'U' && parse_hex(s, pos + 2, end, 8, v)) { pos += 10; }
            else return false;
        } else {
            return false;
        }
    }
    return true;
}

int find_lp_body(const char * s, int len) {
    int best = -1;
    bool best_has_upper = false;

    for (int i = 0; i < len; i++) {
        if (s[i] != '_') continue;
        if (i == 0) continue;
        if (!is_valid_string_mangle(s, i)) continue;
        int body_start = i + 1;
        int body_len = len - body_start;
        if (body_len <= 0) continue;

        Components test;
        if (!demangle_body(s + body_start, body_len, test)) continue;

        bool upper = has_upper_start(s + body_start, body_len);
        if (upper) {
            if (!best_has_upper || i > best - 1) {
                best = body_start;
                best_has_upper = true;
            }
        } else if (!best_has_upper) {
            if (best == -1) best = body_start;
        }
    }
    return best;
}

void unmangle_pkg(const char * s, int len, std::string & out) {
    std::string tmp;
    if (demangle_body_flat(s, len, tmp) && tmp.find('.') == std::string::npos) {
        out += tmp;
    } else {
        out.append(s, len);
    }
}

// ---------------------------------------------------------------------------
// Helper to produce final malloc'd string
// ---------------------------------------------------------------------------

char * to_malloc_str(const std::string & s) {
    char * ret = (char *)malloc(s.size() + 1);
    if (ret) memcpy(ret, s.c_str(), s.size() + 1);
    return ret;
}

// Demangle body and postprocess to human-friendly string.
bool demangle_and_postprocess(const char * body, int body_len, std::string & out) {
    Components comps;
    if (!demangle_body(body, body_len, comps)) return false;
    out = postprocess_name(comps);
    return true;
}

} // anonymous namespace

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

char * lean_demangle_symbol(const char * symbol) {
    if (!symbol || !symbol[0]) return nullptr;

    int slen = (int)strlen(symbol);

    // Handle lean_apply_N -> <apply/N>
    {
        const char * rest = starts_with(symbol, "lean_apply_");
        if (rest && is_all_digits(rest)) {
            std::string result = "<apply/";
            result += rest;
            result += '>';
            return to_malloc_str(result);
        }
    }

    // Strip .cold.N or .cold suffix
    int core_len = slen;
    const char * cold_suffix = nullptr;
    int cold_suffix_len = 0;
    for (int i = 0; i < slen; i++) {
        if (symbol[i] == '.' && i + 5 <= slen && strncmp(symbol + i, ".cold", 5) == 0) {
            core_len = i;
            cold_suffix = symbol + i;
            cold_suffix_len = slen - i;
            break;
        }
    }

    std::string core(symbol, core_len);
    const char * cs = core.c_str();

    // _lean_main
    if (core == "_lean_main") {
        std::string result = "[lean] main";
        if (cold_suffix) { result += ' '; result.append(cold_suffix, cold_suffix_len); }
        return to_malloc_str(result);
    }

    std::string out;
    const char * rest;

    // _init_l_ prefix
    if ((rest = starts_with(cs, "_init_l_")) != nullptr) {
        int body_len = core_len - (int)(rest - cs);
        if (body_len > 0 && demangle_and_postprocess(rest, body_len, out)) {
            std::string result = "[init] " + out;
            if (cold_suffix) { result += ' '; result.append(cold_suffix, cold_suffix_len); }
            return to_malloc_str(result);
        }
    }

    // _init_lp_ prefix
    if ((rest = starts_with(cs, "_init_lp_")) != nullptr) {
        int after_len = core_len - (int)(rest - cs);
        int body_idx = find_lp_body(rest, after_len);
        if (body_idx >= 0) {
            std::string pkg_out;
            unmangle_pkg(rest, body_idx - 1, pkg_out);
            if (demangle_and_postprocess(rest + body_idx, after_len - body_idx, out)) {
                std::string result = "[init] " + out + " (" + pkg_out + ")";
                if (cold_suffix) { result += ' '; result.append(cold_suffix, cold_suffix_len); }
                return to_malloc_str(result);
            }
        }
    }

    // initialize_l_ prefix
    if ((rest = starts_with(cs, "initialize_l_")) != nullptr) {
        int body_len = core_len - (int)(rest - cs);
        if (body_len > 0 && demangle_and_postprocess(rest, body_len, out)) {
            std::string result = "[module_init] " + out;
            if (cold_suffix) { result += ' '; result.append(cold_suffix, cold_suffix_len); }
            return to_malloc_str(result);
        }
    }

    // initialize_lp_ prefix
    if ((rest = starts_with(cs, "initialize_lp_")) != nullptr) {
        int after_len = core_len - (int)(rest - cs);
        int body_idx = find_lp_body(rest, after_len);
        if (body_idx >= 0) {
            std::string pkg_out;
            unmangle_pkg(rest, body_idx - 1, pkg_out);
            if (demangle_and_postprocess(rest + body_idx, after_len - body_idx, out)) {
                std::string result = "[module_init] " + out + " (" + pkg_out + ")";
                if (cold_suffix) { result += ' '; result.append(cold_suffix, cold_suffix_len); }
                return to_malloc_str(result);
            }
        }
    }

    // initialize_ (bare module init)
    if ((rest = starts_with(cs, "initialize_")) != nullptr) {
        int body_len = core_len - (int)(rest - cs);
        if (body_len > 0 && demangle_and_postprocess(rest, body_len, out)) {
            std::string result = "[module_init] " + out;
            if (cold_suffix) { result += ' '; result.append(cold_suffix, cold_suffix_len); }
            return to_malloc_str(result);
        }
    }

    // l_ prefix
    if ((rest = starts_with(cs, "l_")) != nullptr) {
        int body_len = core_len - (int)(rest - cs);
        if (body_len > 0 && demangle_and_postprocess(rest, body_len, out)) {
            if (cold_suffix) { out += ' '; out.append(cold_suffix, cold_suffix_len); }
            return to_malloc_str(out);
        }
    }

    // lp_ prefix
    if ((rest = starts_with(cs, "lp_")) != nullptr) {
        int after_len = core_len - (int)(rest - cs);
        int body_idx = find_lp_body(rest, after_len);
        if (body_idx >= 0) {
            std::string pkg_out;
            unmangle_pkg(rest, body_idx - 1, pkg_out);
            if (demangle_and_postprocess(rest + body_idx, after_len - body_idx, out)) {
                std::string result = out + " (" + pkg_out + ")";
                if (cold_suffix) { result += ' '; result.append(cold_suffix, cold_suffix_len); }
                return to_malloc_str(result);
            }
        }
    }

    return nullptr;
}

// ---------------------------------------------------------------------------
// Backtrace line parsing
// ---------------------------------------------------------------------------

static const char * extract_symbol(const char * line, int * sym_len) {
    int len = (int)strlen(line);

    // Linux (glibc): ./lean(l_Lean_Meta_foo+0x2a) [0x555...]
    for (int i = 0; i < len; i++) {
        if (line[i] == '(') {
            int start = i + 1;
            for (int j = start; j < len; j++) {
                if (line[j] == '+' || line[j] == ')') {
                    if (j > start) { *sym_len = j - start; return line + start; }
                    break;
                }
            }
            break;
        }
    }

    // macOS: 2   lean   0x100abc123 l_Lean_Meta_foo + 42
    for (int i = 0; i + 1 < len; i++) {
        if (line[i] == '0' && line[i + 1] == 'x') {
            int j = i + 2;
            while (j < len && ((line[j] >= '0' && line[j] <= '9') ||
                               (line[j] >= 'a' && line[j] <= 'f') ||
                               (line[j] >= 'A' && line[j] <= 'F'))) j++;
            while (j < len && line[j] == ' ') j++;
            if (j >= len) return nullptr;
            int start = j;
            while (j < len) {
                if (j + 2 < len && line[j] == ' ' && line[j + 1] == '+' && line[j + 2] == ' ')
                    break;
                j++;
            }
            if (j > start) { *sym_len = j - start; return line + start; }
            return nullptr;
        }
    }

    return nullptr;
}

char * lean_demangle_bt_line(const char * line) {
    if (!line) return nullptr;

    int sym_len = 0;
    const char * sym = extract_symbol(line, &sym_len);
    if (!sym || sym_len == 0) return nullptr;

    // Make null-terminated copy
    char * sym_copy = (char *)malloc(sym_len + 1);
    if (!sym_copy) return nullptr;
    memcpy(sym_copy, sym, sym_len);
    sym_copy[sym_len] = '\0';

    char * demangled = lean_demangle_symbol(sym_copy);
    free(sym_copy);
    if (!demangled) return nullptr;

    // Reconstruct line with demangled name
    int line_len = (int)strlen(line);
    int dem_len = (int)strlen(demangled);
    int prefix_len = (int)(sym - line);
    int suffix_start = prefix_len + sym_len;
    int suffix_len = line_len - suffix_start;

    int new_len = prefix_len + dem_len + suffix_len;
    char * result = (char *)malloc(new_len + 1);
    if (!result) { free(demangled); return nullptr; }

    memcpy(result, line, prefix_len);
    memcpy(result + prefix_len, demangled, dem_len);
    memcpy(result + prefix_len + dem_len, line + suffix_start, suffix_len);
    result[new_len] = '\0';

    free(demangled);
    return result;
}
