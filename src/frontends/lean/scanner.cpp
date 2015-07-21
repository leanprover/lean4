/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <cctype>
#include <string>
#include "util/exception.h"
#include "util/utf8.h"
#include "frontends/lean/scanner.h"
#include "frontends/lean/parser_config.h"

namespace lean {
unsigned scanner::get_utf8_size(unsigned char c) {
    unsigned r = ::lean::get_utf8_size(c);
    if (r == 0)
        throw_exception("invalid utf-8 head character");
    return r;
}

unsigned char to_uchar(char c) { return static_cast<unsigned char>(c); }

unsigned utf8_to_unicode(char const * begin, char const * end) {
    unsigned result = 0;
    if (begin == end)
        return result;
    auto it = begin;
    unsigned c = to_uchar(*it);
    ++it;
    if (c < 128)
        return c;
    unsigned mask     = (1u << 6) -1;
    unsigned hmask    = mask;
    unsigned shift    = 0;
    unsigned num_bits = 0;
    while ((c & 0xC0) == 0xC0) {
        c <<= 1;
        c &= 0xff;
        num_bits += 6;
        hmask >>= 1;
        shift++;
        result <<= 6;
        if (it == end)
            return 0;
        result |= *it & mask;
        ++it;
    }
    result |= ((c >> shift) & hmask) << num_bits;
    return result;
}

bool is_greek_unicode(unsigned u) { return 0x391 <= u && u <= 0x3DD; }
bool is_letter_like_unicode(unsigned u) {
    return
        (0x3b1  <= u && u <= 0x3c9 && u != 0x3bb) || // Lower greek, but lambda
        (0x391  <= u && u <= 0x3A9 && u != 0x3A0 && u != 0x3A3) || // Upper greek, but Pi and Sigma
        (0x3ca  <= u && u <= 0x3fb) ||               // Coptic letters
        (0x1f00 <= u && u <= 0x1ffe) ||              // Polytonic Greek Extended Character Set
        (0x2100 <= u && u <= 0x214f);                // Letter like block
}
bool is_super_sub_script_alnum_unicode(unsigned u) {
    return
        (0x2070 <= u && u <= 0x2079) || // most (numeric) superscripts
        (0x207f <= u && u <= 0x2089) || // n superscript and numberic subscripts
        (0x2090 <= u && u <= 0x209c) || // letter-like subscripts
        u == 0x00B2 ||  // 2 superscript
        u == 0x00B3 ||  // 3 superscript
        u == 0x00B9;    // 1 superscript
}

void scanner::next() {
    lean_assert(m_curr != EOF);
    m_spos++;
    while (m_spos >= static_cast<int>(m_curr_line.size())) {
        if (m_last_line) {
            m_curr = EOF;
            return;
        } else {
            m_curr_line.clear();
            if (std::getline(m_stream, m_curr_line)) {
                m_curr_line.push_back('\n');
                m_sline++;
                m_spos  = 0;
                m_upos  = 0;
                m_curr  = m_curr_line[m_spos];
                m_uskip = get_utf8_size(m_curr);
                m_uskip--;
                return;
            } else {
                m_last_line = true;
                m_curr      = EOF;
                return;
            }
        }
    }
    m_curr = m_curr_line[m_spos];
    if (m_uskip > 0) {
        if (!is_utf8_next(m_curr))
            throw_exception("invalid utf-8 sequence character");
        m_uskip--;
    } else {
        m_upos++;
        m_uskip = get_utf8_size(m_curr);
        m_uskip--;
    }
}

void scanner::check_not_eof(char const * error_msg) {
    if (curr() == EOF) throw_exception(error_msg);
}

[[ noreturn ]] void scanner::throw_exception(char const * msg) {
    unsigned line = m_sline;
    unsigned pos  = m_upos;
    while (curr() != EOF && !std::isspace(curr()))
        next();
    throw parser_exception(msg, m_stream_name.c_str(), line, pos);
}

static char const * g_end_error_str_msg = "unexpected end of string";

auto scanner::read_string() -> token_kind {
    lean_assert(curr() == '\"');
    next();
    m_buffer.clear();
    while (true) {
        check_not_eof(g_end_error_str_msg);
        char c = curr();
        if (c == '\"') {
            next();
            return token_kind::String;
        } else if (c == '\\') {
            next();
            check_not_eof(g_end_error_str_msg);
            c = curr();
            if (c != '\\' && c != '\"' && c != 'n')
                throw_exception("invalid escape sequence");
            if (c == 'n')
                c = '\n';
        }
        m_buffer += c;
        next();
    }
}

auto scanner::read_quoted_symbol() -> token_kind {
    lean_assert(curr() == '`');
    next();
    if (std::isdigit(curr()))
        throw_exception("first character of a quoted symbols cannot be a digit");
    m_buffer.clear();
    while (true) {
        check_not_eof("unexpected quoted identifier");
        char c = curr();
        next();
        if (c == '`') {
            m_name_val = name(m_buffer.c_str());
            return token_kind::QuotedSymbol;
        } else if (c != ' ' && c != '\"' && c != '\n' && c != '\t') {
            m_buffer += c;
        } else {
            throw_exception("invalid quoted symbol, invalid character");
        }
    }
}

bool scanner::is_next_digit() {
    lean_assert(curr() != EOF);
    if (m_spos + 1 < static_cast<int>(m_curr_line.size()))
        return std::isdigit(m_curr_line[m_spos+1]);
    else
        return false;
}

auto scanner::read_number() -> token_kind {
    lean_assert('0' <= curr() && curr() <= '9');
    mpq q(1);
    m_num_val = curr() - '0';
    next();
    bool is_decimal = false;

    while (true) {
        char c = curr();
        if ('0' <= c && c <= '9') {
            m_num_val = 10*m_num_val + (c - '0');
            if (is_decimal)
                q *= 10;
            next();
        } else if (c == '.') {
            // Num. is not a decimal. It should be at least Num.0
            if (is_next_digit()) {
                if (is_decimal)
                    break;
                is_decimal = true;
                next();
            } else {
                break;
            }
        } else {
            break;
        }
    }
    if (is_decimal)
        m_num_val /= q;
    return is_decimal ? token_kind::Decimal : token_kind::Numeral;
}

void scanner::read_single_line_comment() {
    while (true) {
        if (curr() == '\n') {
            next();
            return;
        } else if (curr() == EOF) {
            return;
        } else {
            next();
        }
    }
}

void scanner::read_comment_block() {
    unsigned nesting = 1;
    while (true) {
        char c = curr();
        check_not_eof("unexpected end of comment block");
        next();
        if (c == '/') {
            if (curr() == '-') {
                next();
                nesting++;
            }
        } else if (c == '-') {
            if (curr() == '/') {
                next();
                nesting--;
                if (nesting == 0)
                    return;
            }
        }
    }
}

// Read until the end_str is found, store all characters (not including end_str) in m_buffer.
// Throw a parser exception error_msg if end of file is found before end_str.
void scanner::read_until(char const * end_str, char const * error_msg) {
    lean_assert(end_str);
    lean_assert(end_str[0]);
    m_buffer.clear();
    while (true) {
        check_not_eof(error_msg);
        char c = curr_next();
        if (c == end_str[0]) {
            m_aux_buffer.clear();
            m_aux_buffer += c;
            unsigned i = 1;
            while (true) {
                if (!end_str[i])
                    return;
                check_not_eof(error_msg);
                c = curr_next();
                if (c != end_str[i]) {
                    m_buffer += m_aux_buffer;
                    break;
                }
                i++;
            }
        } else {
            m_buffer += c;
        }
    }
}

auto scanner::read_script_block() -> token_kind {
    read_until("*)", "unexpected end of script");
    return token_kind::ScriptBlock;
}

void scanner::move_back(unsigned offset, unsigned u_offset) {
    lean_assert(m_uskip == 0);
    if (offset != 0) {
        if (curr() == EOF) {
            m_curr = 0;
            m_spos--;
            m_upos--;
            offset--;
            u_offset--;
        }
        if (offset != 0) {
            m_spos -= offset;
            m_upos -= u_offset;
        }
        next();
    }
}

void scanner::next_utf_core(char c, buffer<char> & cs) {
    cs.push_back(c);
    while (m_uskip > 0) {
        next();
        cs.push_back(curr());
    }
}

void scanner::next_utf(buffer<char> & cs) {
    next();
    next_utf_core(curr(), cs);
}

static bool is_id_first(buffer<char> const & cs, unsigned i) {
    if (std::isalpha(cs[i]) || cs[i] == '_')
        return true;
    unsigned u = utf8_to_unicode(cs.begin() + i, cs.end());
    return is_letter_like_unicode(u);
}

static bool is_id_rest(buffer<char> const & cs, unsigned i)  {
    if (std::isalnum(cs[i]) || cs[i] == '_' || cs[i] == '\'')
        return true;
    unsigned u = utf8_to_unicode(cs.begin() + i, cs.end());
    return is_letter_like_unicode(u) || is_super_sub_script_alnum_unicode(u);
}

static char const * g_error_key_msg = "unexpected token";

auto scanner::read_key_cmd_id() -> token_kind {
    buffer<char> cs;
    next_utf_core(curr(), cs);
    unsigned num_utfs  = 1;
    unsigned id_sz     = 0;
    unsigned id_utf_sz = 0;
    if (is_id_first(cs, 0)) {
        id_sz = cs.size();
        while (true) {
            id_sz     = cs.size();
            id_utf_sz = num_utfs;
            unsigned i = id_sz;
            next_utf(cs);
            num_utfs++;
            if (is_id_rest(cs, i)) {
            } else if (cs[i] == '.') {
                next_utf(cs);
                num_utfs++;
                if (!is_id_first(cs, i+1))
                    break;
            } else {
                break;
            }
        }
    }
    unsigned i = 0;
    token_table const * it  = m_tokens;
    token_info const * info = nullptr;
    unsigned key_sz       = 0;
    unsigned key_utf_sz   = 0;
    while (i < id_sz) {
        it = find(*it, cs[i]);
        i++;
        if (!it)
            break;
        if (auto new_info = value_of(*it)) {
            lean_assert(m_uskip == 0);
            info       = new_info;
            key_sz     = i;
            key_utf_sz = id_utf_sz; // this is imprecise if key_sz < id_sz, but this case is irrelevant
        }
    }

    while (it) {
        if (i == cs.size()) {
            next_utf(cs);
            num_utfs++;
        }
        it = find(*it, cs[i]);
        i++;
        if (!it)
            break;
        if (auto new_info = value_of(*it)) {
            lean_assert(m_uskip == 0);
            info       = new_info;
            key_sz     = i;
            key_utf_sz = num_utfs;
            lean_assert(key_sz > id_sz);
        }
    }

    if (id_sz == 0 && key_sz == 0)
        throw_exception(g_error_key_msg);
    if (id_sz > key_sz) {
        move_back(cs.size() - id_sz, num_utfs - id_utf_sz);
        m_name_val = name();
        std::string & id_part = m_buffer;
        id_part.clear();
        for (unsigned i = 0; i < id_sz; i++) {
            if (cs[i] == '.') {
                m_name_val = name(m_name_val, id_part.c_str());
                id_part.clear();
            } else {
                id_part.push_back(cs[i]);
            }
        }
        m_name_val = name(m_name_val, id_part.c_str());
        return token_kind::Identifier;
    } else {
        move_back(cs.size() - key_sz, num_utfs - key_utf_sz);
        m_token_info = *info;
        return m_token_info.is_command() ? token_kind::CommandKeyword : token_kind::Keyword;
    }
}

static name * g_begin_script_tk         = nullptr;
static name * g_begin_comment_tk        = nullptr;
static name * g_begin_comment_block_tk  = nullptr;

void initialize_scanner() {
    g_begin_script_tk        = new name("(*");
    g_begin_comment_tk       = new name("--");
    g_begin_comment_block_tk = new name("/-");
}

void finalize_scanner() {
    delete g_begin_script_tk;
    delete g_begin_comment_tk;
    delete g_begin_comment_block_tk;
}

auto scanner::scan(environment const & env) -> token_kind {
    m_tokens = &get_token_table(env);
    while (true) {
        char c = curr();
        m_pos  = m_upos;
        m_line = m_sline;
        switch (c) {
        case ' ': case '\r': case '\t': case '\n':
            next();
            break;
        case '\"':
            return read_string();
        case '`':
            if (m_in_notation) {
                return read_quoted_symbol();
            } else {
                next();
                return token_kind::Backtick;
            }
        case -1:
            return token_kind::Eof;
        default:
            if (std::isdigit(c)) {
                return read_number();
            } else {
                token_kind k = read_key_cmd_id();
                if (k == token_kind::Keyword) {
                    // We treat '(--', '(*', '--' as "keywords.
                    name const & n = m_token_info.value();
                    if (n == *g_begin_comment_tk)
                        read_single_line_comment();
                    else if (n == *g_begin_comment_block_tk)
                        read_comment_block();
                    else if (n == *g_begin_script_tk)
                        return read_script_block();
                    else
                        return k;
                } else {
                    return k;
                }
            }
        }
    }
}

scanner::scanner(std::istream & strm, char const * strm_name, unsigned line):
    m_tokens(nullptr), m_stream(strm) {
    m_stream_name = strm_name ? strm_name : "[unknown]";
    m_sline = line;
    m_line  = line;
    m_spos  = 0;
    m_upos  = 0;
    m_in_notation = false;
    if (std::getline(m_stream, m_curr_line)) {
        m_last_line = false;
        m_curr_line.push_back('\n');
        m_curr  = m_curr_line[m_spos];
        m_uskip = get_utf8_size(m_curr);
        m_uskip--;
    } else {
        m_last_line = true;
        m_curr      = EOF;
        m_uskip     = 0;
    }
}

std::ostream & operator<<(std::ostream & out, scanner::token_kind k) {
    out << static_cast<unsigned>(k);
    return out;
}
}
