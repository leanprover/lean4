/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <cstdio>
#include <string>
#include <algorithm>
#include "lean_scanner.h"
#include "debug.h"
#include "exception.h"

namespace lean {

static name g_lambda_unicode("\u03BB");
static name g_pi_unicode("\u03A0");
static name g_arrow_unicode("\u2192");
static name g_lambda_name("fun");
static name g_type_name("Type");
static name g_pi_name("Pi");
static name g_let_name("let");
static name g_in_name("in");
static name g_arrow_name("->");
static name g_eq_name("=");
static name g_forall_name("forall");
static name g_forall_unicode("\u2200");
static name g_exists_name("exists");
static name g_exists_unicode("\u2203");

static char g_normalized[256];

/** \brief Auxiliary class for initializing global variable \c g_normalized. */
class init_normalized_table {
    void set(int i, char v) { g_normalized[static_cast<unsigned>(i)] = v; }
public:
    init_normalized_table() {
        // by default all characters are in group c,
        for (int i = 0; i <= 255; i++)
            set(i, 'c');

        // digits normalize to '0'
        for (int i = '0'; i <= '9'; i++)
            set(i, '0');

        // characters that can be used to create ids of group a
        for (int i = 'a'; i <= 'z'; i++)
            set(i, 'a');
        for (int i = 'A'; i <= 'Z'; i++)
            set(i, 'a');

        set('_', 'a');

        // characters that can be used to create ids of group b
        for (unsigned char b : {'=', '<', '>', '@', '^', '|', '&', '~', '+', '-', '*', '/', '\\', '$', '%', '?', ';', '[', ']'})
            set(b, 'b');

        // punctuation
        set('(', '(');
        set(')', ')');
        set('{', '{');
        set('}', '}');
        set(':', ':');
        set('.', '.');
        set(',', ',');

        // spaces
        set(' ',  ' ');
        set('\t', ' ');
        set('\r', ' ');

        // new line
        set('\n', '\n');

        // double quotes for strings
        set('\"', '\"');

        // eof
        set(255, -1);
    }
};

static init_normalized_table g_init_normalized_table;

char normalize(char c) {
    return g_normalized[static_cast<unsigned char>(c)];
}

scanner::scanner(std::istream& stream):
    m_spos(0),
    m_curr(0),
    m_line(1),
    m_pos(0),
    m_stream(stream) {
    next();
}

scanner::~scanner() {
}

void scanner::add_command_keyword(name const & n) {
    m_commands = cons(n, m_commands);
}

void scanner::throw_exception(char const * msg) {
    throw parser_exception(msg, m_line, m_spos);
}

void scanner::next() {
    lean_assert(m_curr != EOF);
    m_curr = m_stream.get();
    m_spos++;
}

bool scanner::check_next(char c) {
    lean_assert(m_curr != EOF);
    bool r = m_stream.get() == c;
    m_stream.unget();
    return r;
}

void scanner::read_comment() {
    lean_assert(curr() == '*');
    next();
    int nest = 1;
    while (true) {
        if (curr() == '*') {
            next();
            if (curr() == ')') {
                next();
                nest--;
                if (nest == 0)
                    return;
            }
        } else if (curr() == '(') {
            next();
            if (curr() == '*') {
                next();
                nest++;
            }
        } else if (curr() == '\n') {
            new_line();
            next();
        } else if (curr() == EOF) {
            throw_exception("unexpected end of comment");
        } else {
            next();
        }
    }
}

bool scanner::is_command(name const & n) const {
    return std::any_of(m_commands.begin(), m_commands.end(), [&](name const & c) { return c == n; });
}

/** \brief Auxiliary function for #read_a_symbol */
name scanner::mk_name(name const & curr, std::string const & buf, bool only_digits) {
    if (curr.is_anonymous()) {
        lean_assert(!only_digits);
        return name(buf.c_str());
    } else if (only_digits) {
        mpz val(buf.c_str());
        if (!val.is_unsigned_int())
            throw_exception("invalid hierarchical name, numeral is too big");
        return name(curr, val.get_unsigned_int());
    } else {
        return name(curr, buf.c_str());
    }
}

scanner::token scanner::read_a_symbol() {
    lean_assert(normalize(curr()) == 'a');
    m_buffer.clear();
    m_buffer += curr();
    m_name_val = name();
    next();
    bool only_digits = false;
    while (true) {
        if (normalize(curr()) == 'a') {
            if (only_digits)
                throw_exception("invalid hierarchical name, digit expected");
            m_buffer += curr();
            next();
        } else if (normalize(curr()) == '0') {
            m_buffer += curr();
            next();
        } else if (curr() == ':' && check_next(':')) {
            next();
            lean_assert(curr() == ':');
            next();
            m_name_val = mk_name(m_name_val, m_buffer, only_digits);
            m_buffer.clear();
            only_digits = (normalize(curr()) == '0');
        } else {
            m_name_val = mk_name(m_name_val, m_buffer, only_digits);
            if (m_name_val == g_lambda_name)
                return token::Lambda;
            else if (m_name_val == g_pi_name)
                return token::Pi;
            else if (m_name_val == g_forall_name)
                return token::Forall;
            else if (m_name_val == g_exists_name)
                return token::Exists;
            else if (m_name_val == g_type_name)
                return token::Type;
            else if (m_name_val == g_let_name)
                return token::Let;
            else if (m_name_val == g_in_name)
                return token::In;
            else
                return is_command(m_name_val) ? token::CommandId : token::Id;
        }
    }
}

scanner::token scanner::read_b_symbol() {
    lean_assert(normalize(curr()) == 'b');
    m_buffer.clear();
    m_buffer += curr();
    next();
    while (true) {
        if (normalize(curr()) == 'b') {
            m_buffer += curr();
            next();
        } else {
            m_name_val = name(m_buffer.c_str());
            if (m_name_val == g_arrow_name)
                return token::Arrow;
            else if (m_name_val == g_eq_name)
                return token::Eq;
            else
                return token::Id;
        }
    }
}

scanner::token scanner::read_c_symbol() {
    lean_assert(normalize(curr()) == 'c');
    m_buffer.clear();
    m_buffer += curr();
    next();
    while (true) {
        if (normalize(curr()) == 'c') {
            m_buffer += curr();
            next();
        } else {
            m_name_val = name(m_buffer.c_str());
            if (m_name_val == g_arrow_unicode)
                return token::Arrow;
            else if (m_name_val == g_lambda_unicode)
                return token::Lambda;
            else if (m_name_val == g_pi_unicode)
                return token::Pi;
            else if (m_name_val == g_forall_unicode)
                return token::Forall;
            else if (m_name_val == g_exists_unicode)
                return token::Exists;
            else
                return token::Id;
        }
    }
}

scanner::token scanner::read_number() {
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
            if (is_decimal)
                break;
            is_decimal = true;
            next();
        } else {
            break;
        }
    }
    if (is_decimal)
        m_num_val /= q;
    return is_decimal ? token::DecimalVal : token::IntVal;
}

scanner::token scanner::read_string() {
    lean_assert(curr() == '\"');
    next();
    m_buffer.clear();
    while (true) {
        char c = curr();
        if (c == EOF) {
            throw_exception("unexpected end of string");
        } else if (c == '\"') {
            next();
            return token::StringVal;
        } else if (c == '\n') {
            new_line();
        } else if (c == '\\') {
            next();
            c = curr();
            if (c == EOF)
                throw_exception("unexpected end of string");
            if (c != '\\' && c != '\"' && c != 'n')
                throw_exception("invalid escape sequence");
            if (c == 'n')
                c = '\n';
        }
        m_buffer += c;
        next();
    }
}

scanner::token scanner::scan() {
    while (true) {
        char c = curr();
        m_pos = m_spos;
        switch (normalize(c)) {
        case ' ':  next(); break;
        case '\n': next(); new_line(); break;
        case ':':  next();
            if (curr() == '=') {
                next();
                return token::Assign;
            } else {
                return token::Colon;
            }
        case ',':  next(); return token::Comma;
        case '.':  next(); return token::Period;
        case '(':
            next();
            if (curr() == '*') {
                read_comment();
                break;
            } else {
                return token::LeftParen;
            }
        case ')':  next(); return token::RightParen;
        case '{':  next(); return token::LeftCurlyBracket;
        case '}':  next(); return token::RightCurlyBracket;
        case 'a':  return read_a_symbol();
        case 'b':  return read_b_symbol();
        case 'c':  return read_c_symbol();
        case '0':  return read_number();
        case '\"': return read_string();
        case -1:   return token::Eof;
        default:   lean_unreachable();
        }
    }
}

std::ostream & operator<<(std::ostream & out, scanner::token const & t) {
    switch (t) {
    case scanner::token::LeftParen:         out << "("; break;
    case scanner::token::RightParen:        out << ")"; break;
    case scanner::token::LeftCurlyBracket:  out << "{"; break;
    case scanner::token::RightCurlyBracket: out << "}"; break;
    case scanner::token::Colon:             out << ":"; break;
    case scanner::token::Comma:             out << ","; break;
    case scanner::token::Period:            out << "."; break;
    case scanner::token::Lambda:            out << g_lambda_unicode; break;
    case scanner::token::Pi:                out << g_pi_unicode; break;
    case scanner::token::Forall:            out << g_forall_unicode; break;
    case scanner::token::Exists:            out << g_exists_unicode; break;
    case scanner::token::Arrow:             out << g_arrow_unicode; break;
    case scanner::token::Let:               out << "let"; break;
    case scanner::token::In:                out << "in"; break;
    case scanner::token::Id:                out << "Id"; break;
    case scanner::token::CommandId:         out << "CId"; break;
    case scanner::token::IntVal:            out << "Int"; break;
    case scanner::token::DecimalVal:        out << "Dec"; break;
    case scanner::token::StringVal:         out << "String"; break;
    case scanner::token::Eq:                out << "="; break;
    case scanner::token::Assign:            out << ":="; break;
    case scanner::token::Type:              out << "Type"; break;
    case scanner::token::Eof:               out << "EOF"; break;
    }
    return out;
}
}
