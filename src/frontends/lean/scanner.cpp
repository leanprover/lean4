/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <cctype>
#include <string>
#include "util/exception.h"
#include "frontends/lean/scanner.h"
#include "frontends/lean/parser_config.h"

namespace lean {
bool is_utf8_next(unsigned char c) { return (c & 0xC0) == 0x80; }

unsigned scanner::get_utf8_size(unsigned char c) {
    if ((c & 0x80) == 0)
        return 1;
    else if ((c & 0xE0) == 0xC0)
        return 2;
    else if ((c & 0xF0) == 0xE0)
        return 3;
    else if ((c & 0xF8) == 0xF0)
        return 4;
    else if ((c && 0xFC) == 0xF8)
        return 5;
    else if ((c && 0xFE) == 0xFC)
        return 6;
    else if (c == 0xFF)
        return 1;
    else
        throw_exception("invalid utf-8 head character");
}

void scanner::set_line(unsigned p) {
    m_line  = p;
    m_sline = p;
}

void scanner::next() {
    lean_assert(m_curr != EOF);
    m_curr = m_stream.get();
    m_spos++;
    if (m_uskip > 0) {
        if (!is_utf8_next(m_curr)) {
            throw_exception("invalid utf-8 sequence character");
        }
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

auto scanner::read_string() -> token_kind {
    static char const * end_error_msg = "unexpected end of string";
    lean_assert(curr() == '\"');
    next();
    m_buffer.clear();
    while (true) {
        check_not_eof(end_error_msg);
        update_line();
        char c = curr();
        if (c == '\"') {
            next();
            return token_kind::String;
        } else if (c == '\\') {
            next();
            check_not_eof(end_error_msg);
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
    char c = m_stream.get();
    bool r = std::isdigit(c);
    m_stream.unget();
    return r;
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
            new_line();
            next();
            return;
        } else if (curr() == EOF) {
            return;
        } else {
            next();
        }
    }
}

// Try to consume str, return true if success.
// Throw a parser exception error_msg if end of file is found
bool scanner::consume(char const * str, char const * error_msg) {
    if (curr() == str[0]) {
        next();
        unsigned i = 1;
        while (true) {
            if (!str[i])
                return true;
            check_not_eof(error_msg);
            update_line();
            if (curr_next() != str[i])
                return false;
            i++;
        }
    } else {
        return false;
    }
}

static char const * g_begin_comment_block = "(--";
static char const * g_end_comment_block = "--)";

void scanner::read_comment_block() {
    static char const * end_error_msg = "unexpected end of comment block";
    unsigned nesting = 1;
    while (true) {
        if (consume(g_begin_comment_block, end_error_msg)) {
            nesting++;
        }
        if (consume(g_end_comment_block, end_error_msg)) {
            nesting--;
            if (nesting == 0)
                return;
        }
        check_not_eof(end_error_msg);
        update_line();
        next();
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
        update_line();
        char c = curr_next();
        if (c == end_str[0]) {
            m_aux_buffer.clear();
            m_aux_buffer += c;
            unsigned i = 1;
            while (true) {
                if (!end_str[i])
                    return;
                check_not_eof(error_msg);
                update_line();
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
            m_stream.clear();
            m_spos--;
            m_upos--;
            offset--;
            u_offset--;
        }
        if (offset != 0) {
            m_stream.seekg(-static_cast<std::streamoff>(offset), std::ios_base::cur);
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
    return std::isalpha(cs[i]) || cs[i] == '_';
}

static bool is_id_rest(buffer<char> const & cs, unsigned i)  {
    return std::isalnum(cs[i]) || cs[i] == '_' || cs[i] == '\'';
}

auto scanner::read_key_cmd_id() -> token_kind {
    static char const * error_msg = "unexpected token";
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
                if (!is_id_rest(cs, i+1))
                    break;
            } else {
                break;
            }
        }
    }

    unsigned i = 0;
    token_table const * it  = find(*m_tokens, cs[i]);
    token_info const * info = nullptr;
    unsigned key_sz       = 0;
    unsigned key_utf_sz   = 0;
    unsigned aux_num_utfs = id_utf_sz;
    if (it) {
        if (aux_num_utfs == 0)
            aux_num_utfs = 1;
        info = value_of(*it);
        if (info) {
            lean_assert(m_uskip == 0);
            key_sz     = 1;
            key_utf_sz = aux_num_utfs;
        }
        while (it) {
            i++;
            if (i == cs.size()) {
                next_utf(cs);
                num_utfs++;
                aux_num_utfs = num_utfs;
            }
            it = find(*it, cs[i]);
            if (it) {
                if (auto new_info = value_of(*it)) {
                    lean_assert(m_uskip == 0);
                    info       = new_info;
                    key_sz     = i+1;
                    key_utf_sz = aux_num_utfs;
                }
            } else {
                break;
            }
        }
    }

    if (id_sz == 0 && key_sz == 0)
        throw_exception(error_msg);
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
        m_token_info = info;
        return info->is_command() ? token_kind::CommandKeyword : token_kind::Keyword;
    }
}

static name g_begin_script_tk("(*");
static name g_begin_comment_tk("--");
static name g_begin_comment_block_tk("(--");

auto scanner::scan(environment const & env) -> token_kind {
    m_tokens = &get_token_table(env);
    while (true) {
        char c = curr();
        m_pos  = m_upos;
        m_line = m_sline;
        switch (c) {
        case ' ': case '\r': case '\t':
            next();
            break;
        case '\n':
            next(); new_line();
            break;
        case '\"':
            return read_string();
        case '`':
            return read_quoted_symbol();
        case -1:
            return token_kind::Eof;
        default:
            if (std::isdigit(c)) {
                return read_number();
            } else {
                token_kind k = read_key_cmd_id();
                if (k == token_kind::Keyword) {
                    // We treat '(--', '(*', '--' as "keywords.
                    name const & n = m_token_info->value();
                    if (n == g_begin_comment_tk)
                        read_single_line_comment();
                    else if (n == g_begin_comment_block_tk)
                        read_comment_block();
                    else if (n == g_begin_script_tk)
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

scanner::scanner(std::istream & strm, char const * strm_name):
    m_tokens(nullptr), m_stream(strm), m_spos(0), m_upos(0), m_uskip(0), m_sline(1), m_curr(0), m_pos(0), m_line(1),
    m_token_info(nullptr) {
    m_stream_name = strm_name ? strm_name : "[unknown]";
    next();
}

std::ostream & operator<<(std::ostream & out, scanner::token_kind k) {
    out << static_cast<unsigned>(k);
    return out;
}
}
