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
void scanner::set_line(unsigned p) {
    m_line  = p;
    m_sline = p;
}

void scanner::next() {
    lean_assert(m_curr != EOF);
    m_curr = m_stream.get();
    m_spos++;
}

void scanner::check_not_eof(char const * error_msg) {
    if (curr() == EOF) throw_exception(error_msg);
}

[[ noreturn ]] void scanner::throw_exception(char const * msg) {
    unsigned line = m_sline;
    unsigned pos  = m_spos;
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

static bool is_id_first(char c) { return std::isalpha(c) || c == '_'; }
static bool is_id_rest(char c)  { return std::isalnum(c) || c == '_' || c == '\''; }

void scanner::move_back(std::streamoff offset) {
    if (offset != 0) {
        if (curr() == EOF) {
            m_curr = 0;
            m_stream.clear();
            m_spos--;
        }
        m_stream.seekg(offset, std::ios_base::cur);
        m_spos += offset;
        next();
    }
}

bool scanner::is_next_id_rest() {
    lean_assert(curr() != EOF);
    char c = m_stream.get();
    bool r = is_id_rest(c);
    m_stream.unget();
    return r;
}

auto scanner::read_key_cmd_id() -> token_kind {
    static char const * error_msg = "unexpected token";
    char c = curr();
    unsigned num_cs = 1; // number of characters read
    token_table const * it    = find(*m_tokens, c);
    token_info const * info = nullptr;
    unsigned key_size       = 0;
    if (it) {
        info = value_of(*it);
        if (info)
            key_size = 1;
    }
    std::string & id_part = m_buffer;
    bool is_id = is_id_first(c);
    unsigned id_size = 0;
    if (is_id) {
        m_name_val = name();
        id_part.clear();
        id_part.push_back(c);
        id_size = 1;
    }

    while (it || is_id) {
        next();
        c = curr();
        if (c != EOF)
            num_cs++;

        if (is_id) {
            if (is_id_rest(c)) {
                id_part.push_back(c);
                id_size++;
            } else if (c == '.' && is_next_id_rest()) {
                m_name_val = name(m_name_val, id_part.c_str());
                id_size++;
                id_part.clear();
            } else {
                is_id = false;
                m_name_val = name(m_name_val, id_part.c_str());
                if (!it)
                    return token_kind::Identifier;
            }
        }

        if (it) {
            it = find(*it, c);
            if (it) {
                if (auto new_info = value_of(*it)) {
                    info     = new_info;
                    key_size = num_cs;
                }
            } else if (!is_id) {
                if (id_size > key_size) {
                    move_back(static_cast<std::streamoff>(id_size) - static_cast<std::streamoff>(num_cs));
                    return token_kind::Identifier;
                } else if (info) {
                    move_back(static_cast<std::streamoff>(key_size) - static_cast<std::streamoff>(num_cs));
                    m_token_info = info;
                    return info->is_command() ? token_kind::CommandKeyword : token_kind::Keyword;
                }
            }
        }
    }
    throw_exception(error_msg);
}

static name g_begin_script_tk("(*");
static name g_begin_comment_tk("--");
static name g_begin_comment_block_tk("(--");

auto scanner::scan(environment const & env) -> token_kind {
    m_tokens = &get_token_table(env);
    while (true) {
        char c = curr();
        m_pos  = m_spos;
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
    m_tokens(nullptr), m_stream(strm), m_spos(0), m_sline(1), m_curr(0), m_pos(0), m_line(1),
    m_token_info(nullptr) {
    m_stream_name = strm_name ? strm_name : "[unknown]";
    next();
}

std::ostream & operator<<(std::ostream & out, scanner::token_kind k) {
    out << static_cast<unsigned>(k);
    return out;
}
}
