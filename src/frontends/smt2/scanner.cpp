/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#include <cctype>
#include <string>
#include "util/parser_exception.h"
#include "util/utf8.h"
#include "frontends/smt2/scanner.h"

namespace lean {
namespace smt2 {

static char const * g_end_error_str_msg = "unexpected end of string";
static char const * g_end_error_qsym_msg = "unexpected end of quoted symbol";

static scanner::char_kind g_char_to_kind[256];

// Util
static unsigned char to_uchar(char c) { return static_cast<unsigned char>(c); }
static scanner::char_kind get_kind(char c) { return g_char_to_kind[to_uchar(c)]; }

[[ noreturn ]] void scanner::throw_exception(char const * msg) {
    auto pos = get_pos_info();
    while (curr() != EOF && !std::isspace(curr()))
        next();
    throw parser_exception(msg, m_stream_name.c_str(), pos);
}

[[ noreturn ]] void scanner::throw_exception(std::string const & msg) { throw_exception(msg.c_str()); }

void scanner::check_not_eof(char const * error_msg) {
    if (curr() == EOF) throw_exception(error_msg);
}

std::ostream & operator<<(std::ostream & out, scanner::token_kind k) {
    out << static_cast<unsigned>(k);
    return out;
}

bool scanner::is_next_digit() {
    lean_assert(curr() != EOF);
    if (m_cpos + 1 < static_cast<int>(m_curr_line.size()))
        return std::isdigit(m_curr_line[m_cpos+1]);
    else
        return false;
}

// Constructor
scanner::scanner(std::istream & strm, char const * strm_name): m_stream(strm) {
    m_stream_name = strm_name ? strm_name : "[unknown]";
    if (std::getline(m_stream, m_curr_line)) {
        m_last_line = false;
        m_curr_line.push_back('\n');
        m_curr  = m_curr_line[m_cpos];
    } else {
        m_last_line = true;
        m_curr      = EOF;
    }
}

// The core readers
void scanner::read_comment() {
    lean_assert(curr() == ';');
    next();
    while (true) {
        char c = curr();
        next();
        if (c == '\n')
            return;
    }
}

void scanner::read_simple_symbol_core() {
    while (true) {
        char c = curr();
        switch (get_kind(c)) {
        case char_kind::SIMPLE_SYMBOL:
        case char_kind::NUMBER:
            m_str_val += c;
            next();
            break;
        default:
            return;
        }
    }
}

void scanner::read_simple_symbol() {
    lean_assert(get_kind(curr()) == scanner::char_kind::SIMPLE_SYMBOL);
    m_str_val.clear();
    m_str_val += curr();
    next();
    read_simple_symbol_core();
}

void scanner::read_keyword() {
    lean_assert(curr() == ':');
    m_str_val.clear();
    m_str_val += curr();
    next();
    read_simple_symbol_core();
}

void scanner::read_quoted_symbol() {
    lean_assert(curr() == '|');
    m_str_val.clear();
    next();
    while (true) {
        check_not_eof(g_end_error_qsym_msg);
        char c = curr();
        if (c == '\\') {
            throw_exception("character '\' not allowed in quoted symbols");
        } else if (c == '|') {
            next();
            return;
        } else {
            m_str_val += c;
            next();
        }
    }
}

void scanner::read_string() {
    lean_assert(curr() == '"');
    next();
    m_str_val.clear();
    while (true) {
        check_not_eof(g_end_error_str_msg);
        char c = curr();
        // "" ==> "
        // " ==> <end-of-string>
        if (c == '\"') {
            next();
            if (curr() != '\"') {
                return;
            }
        }
        m_str_val += c;
        next();
    }
}

scanner::token_kind scanner::read_number() {
    lean_assert('0' <= curr() && curr() <= '9');
    char c = curr();
    next();

    mpq denom(1);
    m_num_val = c - '0';

    bool starts_with_zero = (c == '0');
    bool first = true;
    bool is_decimal = false;
    while (true) {
        c = curr();
        if ('0' <= c && c <= '9') {
            if (first && starts_with_zero) {
                throw_exception("invalid numeral: non-zero numerals cannot start with 0");
            }
            m_num_val = 10*m_num_val + (c - '0');
            if (is_decimal)
                denom *= 10;
            next();
        } else if (c == '.') {
            if (is_decimal) {
                break;
            } else if (is_next_digit()) {
                is_decimal = true;
                next();
            } else {
                break;
            }
        } else {
            break;
        }
        first = false;
    }

    if (is_decimal)
        m_num_val /= denom;
    return is_decimal ? token_kind::FLOAT : token_kind::INT;
}

void scanner::read_hex_bv_literal() {
    lean_assert(curr() == 'x');
    next();
    char c = curr();

    m_num_val = 0;
    m_bv_size = 0;

    while (true) {
        if ('0' <= c && c <= '9') {
            m_num_val *= 16;
            m_num_val += (c - '0');
        } else if ('a' <= c && c <= 'f') {
            m_num_val *= 16;
            m_num_val += (10 + (c - 'a'));
        } else if ('A' <= c && c <= 'F') {
            m_num_val *= 16;
            m_num_val += (10 + (c - 'A'));
        } else if (m_bv_size == 0) {
            throw_exception("invalid hexadecimal bit-vector literal: bit-vector literals cannot be empty");
        } else {
            return;
        }

        m_bv_size += 4;
        next();
        c = curr();
    }
}

void scanner::read_bin_bv_literal() {
    lean_assert(curr() == 'b');
    next();
    char c = curr();

    m_num_val = 0;
    m_bv_size = 0;

    while (c == '0' || c == '1') {
        m_num_val *= 2;
        m_num_val += (c - '0');
        m_bv_size += 1;
        next();
        c = curr();
    }

    if (m_bv_size == 0) {
        throw_exception("invalid binary bit-vector literal: bit-vector literals cannot be empty");
    }
}

void scanner::read_bv_literal() {
    lean_assert(curr() == '#');
    next();
    char c = curr();
    if (c == 'x') {
        read_hex_bv_literal();
    } else if (c == 'b') {
        read_bin_bv_literal();
    } else {
        throw_exception("invalid bit-vector literal: # must be followed by either 'x' or 'b'");
    }
}

// Main loop
scanner::token_kind scanner::scan() {
    while (true) {
        char c = curr();
        m_tpos  = m_cpos;
        m_tline = m_cline;
        switch (get_kind(c)) {
        case char_kind::END:
            return token_kind::END;
        case char_kind::WHITESPACE:
            next();
            break;
        case char_kind::COMMENT:
            read_comment();
            break;
        case char_kind::LEFT_PAREN:
            next();
            return token_kind::LEFT_PAREN;
        case char_kind::RIGHT_PAREN:
            next();
            return token_kind::RIGHT_PAREN;
        case char_kind::KEYWORD:
            read_keyword();
            return token_kind::KEYWORD;
        case char_kind::QUOTED_SYMBOL:
            read_quoted_symbol();
            return token_kind::SYMBOL;
        case char_kind::STRING:
            read_string();
            return token_kind::STRING;
        case char_kind::NUMBER:
            // We return the result since we do not know yet whether it is an INT or a FLOAT
            return read_number();
        case char_kind::BV:
            read_bv_literal();
            return token_kind::BV;
        case char_kind::SIMPLE_SYMBOL:
            read_simple_symbol();
            return token_kind::SYMBOL;
        case char_kind::UNEXPECTED:
            throw_exception(std::string("unexpected character: ") + c);
        }
    }
}

// Get next char
void scanner::next() {
    lean_assert(m_curr != EOF);
    m_cpos++;
    while (m_cpos >= static_cast<int>(m_curr_line.size())) {
        if (m_last_line) {
            m_curr = EOF;
            return;
        } else {
            m_curr_line.clear();
            if (std::getline(m_stream, m_curr_line)) {
                m_curr_line.push_back('\n');
                m_cline++;
                m_cpos  = 0;
                m_curr  = m_curr_line[m_cpos];
                m_tpos  = 0;
                return;
            } else {
                m_last_line = true;
                m_curr      = EOF;
                return;
            }
        }
    }
    m_curr = m_curr_line[m_cpos];
}


// Setup and teardown

static void initialize_g_char_to_kind() {
    for (int i = 0; i < 256; ++i) {
        g_char_to_kind[i] = scanner::char_kind::UNEXPECTED;
    }

    // (1) EOF
    g_char_to_kind[to_uchar(EOF)] = scanner::char_kind::END;

    // (2) Space
    g_char_to_kind[9] = scanner::char_kind::WHITESPACE;
    g_char_to_kind[16] = scanner::char_kind::WHITESPACE;
    g_char_to_kind[13] = scanner::char_kind::WHITESPACE;
    g_char_to_kind[32] = scanner::char_kind::WHITESPACE;
    g_char_to_kind[to_uchar('\n')] = scanner::char_kind::WHITESPACE;

    // (3) Comment
    g_char_to_kind[to_uchar(';')] = scanner::char_kind::COMMENT;

    // (4) Left-paren
    g_char_to_kind[to_uchar('(')] = scanner::char_kind::LEFT_PAREN;

    // (5) Right-paren
    g_char_to_kind[to_uchar(')')] = scanner::char_kind::RIGHT_PAREN;

    // (6) Keyword
    g_char_to_kind[to_uchar(':')] = scanner::char_kind::KEYWORD;

    // (7) Quoted symbol
    g_char_to_kind[to_uchar('|')] = scanner::char_kind::QUOTED_SYMBOL;

    // (8) String
    g_char_to_kind[to_uchar('"')] = scanner::char_kind::STRING;

    // (9) Number
    lean_assert('0' < '9');
    for (char ch = '0'; ch <= '9'; ++ch) {
        g_char_to_kind[to_uchar(ch)] = scanner::char_kind::NUMBER;
    }

    // (10) BV
    g_char_to_kind[to_uchar('#')] = scanner::char_kind::BV;

    // (11) Symbol
    lean_assert('a' < 'z');
    for (char ch = 'a'; ch <= 'z'; ++ch) {
        g_char_to_kind[to_uchar(ch)] = scanner::char_kind::SIMPLE_SYMBOL;
    }
    lean_assert('A' < 'Z');
    for (char ch = 'A'; ch <= 'Z'; ++ch) {
        g_char_to_kind[to_uchar(ch)] = scanner::char_kind::SIMPLE_SYMBOL;
    }

    g_char_to_kind[to_uchar('+')] = scanner::char_kind::SIMPLE_SYMBOL;
    g_char_to_kind[to_uchar('-')] = scanner::char_kind::SIMPLE_SYMBOL;
    g_char_to_kind[to_uchar('/')] = scanner::char_kind::SIMPLE_SYMBOL;
    g_char_to_kind[to_uchar('*')] = scanner::char_kind::SIMPLE_SYMBOL;
    g_char_to_kind[to_uchar('=')] = scanner::char_kind::SIMPLE_SYMBOL;
    g_char_to_kind[to_uchar('%')] = scanner::char_kind::SIMPLE_SYMBOL;
    g_char_to_kind[to_uchar('?')] = scanner::char_kind::SIMPLE_SYMBOL;
    g_char_to_kind[to_uchar('!')] = scanner::char_kind::SIMPLE_SYMBOL;
    g_char_to_kind[to_uchar('.')] = scanner::char_kind::SIMPLE_SYMBOL;
    g_char_to_kind[to_uchar('$')] = scanner::char_kind::SIMPLE_SYMBOL;
    g_char_to_kind[to_uchar('_')] = scanner::char_kind::SIMPLE_SYMBOL;
    g_char_to_kind[to_uchar('~')] = scanner::char_kind::SIMPLE_SYMBOL;
    g_char_to_kind[to_uchar('&')] = scanner::char_kind::SIMPLE_SYMBOL;
    g_char_to_kind[to_uchar('^')] = scanner::char_kind::SIMPLE_SYMBOL;
    g_char_to_kind[to_uchar('<')] = scanner::char_kind::SIMPLE_SYMBOL;
    g_char_to_kind[to_uchar('>')] = scanner::char_kind::SIMPLE_SYMBOL;
    g_char_to_kind[to_uchar('@')] = scanner::char_kind::SIMPLE_SYMBOL;
}

void initialize_scanner() {
    initialize_g_char_to_kind();
}

void finalize_scanner() { }

}}
