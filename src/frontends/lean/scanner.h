/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <string>
#include <iostream>
#include "kernel/pos_info_provider.h"
#include "util/name.h"
#include "util/flet.h"
#include "util/utf8.h"
#include "util/numerics/mpq.h"
#include "kernel/environment.h"
#include "library/io_state.h"
#include "frontends/lean/token_table.h"

namespace lean {
enum class token_kind {Keyword, CommandKeyword, Identifier, Numeral, Decimal,
        String, Char, QuotedSymbol,
        DocBlock, ModDocBlock, FieldNum, FieldName, Eof};

/**
    \brief Scanner. The behavior of the scanner is controlled using a token set.

    The scanner has builtin support for comments,
    identifiers, numerals, decimals, strings. Everything else is only
    accepted if they are in the token set.
*/
class scanner {
protected:
    token_table const * m_tokens;
    std::istream *      m_stream;
    std::string         m_stream_name;
    std::string         m_curr_line;
    bool                m_last_line;

    int                 m_spos;  // current position
    int                 m_upos;  // current position taking into account utf-8 encoding
    int                 m_uskip; // hack for decoding utf-8, it marks how many units to skip
    int                 m_sline; // current line
    uchar               m_curr;  // current char;

    int                 m_pos;   // start position of the token
    int                 m_line;  // line of the token

    name                m_name_val;
    token_info          m_token_info;
    mpq                 m_num_val;
    std::string         m_buffer;
    std::string         m_aux_buffer;

    bool                m_in_notation;
    bool                m_field_notation{true};

    [[ noreturn ]] void throw_exception(char const * msg);
    void next();
    void fetch_line();
    uchar curr() const { return m_curr; }
    uchar curr_next() { auto c = curr(); next(); return c; }
    void check_not_eof(char const * error_msg);
    bool is_next_digit();
    bool is_next_id_rest();
    void move_back(unsigned offset, unsigned u_offset);
    void read_single_line_comment();
    void read_comment_block();
    void read_until(uchar const * end_str, char const * error_msg);
    unsigned get_utf8_size(uchar c);
    void next_utf_core(uchar c, buffer<uchar> & cs);
    void next_utf(buffer<uchar> & cs);

    optional<unsigned> try_hex_to_unsigned(uchar c);
    optional<unsigned> try_digit_to_unsigned(int base, uchar c);
    unsigned hex_to_unsigned(uchar c);
    void read_quoted_char(char const * error_msg, std::string & r);
    token_kind read_string();
    token_kind read_char();
    token_kind read_hex_number();
    token_kind read_number();
    void read_field_idx();
    token_kind read_key_cmd_id();
    token_kind read_quoted_symbol();
    void read_doc_block_core();
    token_kind read_doc_block();
    token_kind read_mod_doc_block();

public:
    scanner(std::istream & strm, char const * strm_name = nullptr);
    scanner(std::istream & strm, char const * strm_name, pos_info const & pos);

    void skip_to_pos(pos_info const &);

    int get_line() const { return m_line; }
    int get_pos() const { return m_pos; }
    pos_info get_pos_info() const { return pos_info(m_line, m_pos); }
    token_kind scan(environment const & env);

    mpq const & get_num_val() const { return m_num_val; }
    name const & get_name_val() const { return m_name_val; }
    std::string const & get_str_val() const { return m_buffer; }
    token_info const & get_token_info() const { return m_token_info; }

    std::string const & get_stream_name() const { return m_stream_name; }

    class in_notation_ctx {
        flet<bool> m_in_notation;
    public:
        in_notation_ctx(scanner & s):m_in_notation(s.m_in_notation, true) {}
    };

    bool in_notation() const { return m_in_notation; }

    class field_notation_scope : public flet<bool> {
    public:
        field_notation_scope(scanner & s, bool flag):
            flet<bool>(s.m_field_notation, flag) {}
    };
};
std::ostream & operator<<(std::ostream & out, token_kind k);

class token {
    token_kind  m_kind;
    pos_info    m_pos;
    union {
        token_info *  m_info;     /* Keyword, CommandKeyword */
        name *        m_name_val; /* QuotedSymbol, Identifier, FieldName */
        mpq *         m_num_val;  /* Decimal, Numeral, FieldNum */
        std::string * m_str_val;  /* String, Char, DocBlock, ModDocBlock */
    };

    void dealloc();
    void copy(token const & tk);
    void steal(token && tk);

public:
    token(pos_info const & p); /*  EOF */
    token(token_kind k, pos_info const & p, token_info const & info);
    token(token_kind k, pos_info const & p, name const & v);
    token(token_kind k, pos_info const & p, mpq const & v);
    token(token_kind k, pos_info const & p, std::string const & v);
    token(token const & tk) { copy(tk); }
    token(token && tk) { steal(std::move(tk)); }
    ~token() { dealloc(); }

    token const & operator=(token const & tk) {
        if (this != &tk) {
            dealloc();
            copy(tk);
        }
        return *this;
    }

    token const & operator=(token && tk) {
        if (this != &tk) {
            dealloc();
            steal(std::move(tk));
        }
        return *this;
    }

    token_kind kind() const { return m_kind; }

    unsigned get_line() const { return m_pos.first; }
    unsigned get_col() const { return m_pos.second; }
    pos_info const & get_pos() const { return m_pos; }

    token_info const & get_token_info() const {
        lean_assert(m_kind == token_kind::Keyword || m_kind == token_kind::CommandKeyword);
        return *m_info;
    }

    name const & get_name_val() const {
        lean_assert(m_kind == token_kind::QuotedSymbol || m_kind == token_kind::Identifier);
        return *m_name_val;
    }

    mpq const & get_num_val() const {
        lean_assert(m_kind == token_kind::Decimal || m_kind == token_kind::Numeral);
        return *m_num_val;
    }

    std::string const & get_str_val() const {
        lean_assert(m_kind == token_kind::String || m_kind == token_kind::Char ||
                    m_kind == token_kind::DocBlock || m_kind == token_kind::ModDocBlock);
        return *m_str_val;
    }
};

/* Consume tokens from s until EOF, or a command token different from 'end', and return this token.
   The other consumed tokens are pushed into tk. */
token read_tokens(environment & env, io_state const & ios, scanner & s, buffer<token> & tk, bool use_exceptions);

void initialize_scanner();
void finalize_scanner();
}
