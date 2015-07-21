/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <string>
#include <iostream>
#include "util/name.h"
#include "util/flet.h"
#include "util/numerics/mpq.h"
#include "kernel/environment.h"
#include "frontends/lean/token_table.h"

namespace lean {
/**
    \brief Scanner. The behavior of the scanner is controlled using a token set.

    The scanner has builtin support for comments, script blocks,
    identifiers, numerals, decimals, strings. Everything else is only
    accepted if they are in the token set.
*/
class scanner {
public:
    enum class token_kind {Keyword, CommandKeyword, ScriptBlock, Identifier, Numeral, Decimal, String, QuotedSymbol, Backtick, Eof};
protected:
    token_table const * m_tokens;
    std::istream &      m_stream;
    std::string         m_stream_name;
    std::string         m_curr_line;
    bool                m_last_line;

    int                 m_spos;  // current position
    int                 m_upos;  // current position taking into account utf-8 encoding
    int                 m_uskip; // hack for decoding utf-8, it marks how many units to skip
    int                 m_sline; // current line
    char                m_curr;  // current char;

    int                 m_pos;   // start position of the token
    int                 m_line;  // line of the token

    name                m_name_val;
    token_info          m_token_info;
    mpq                 m_num_val;
    std::string         m_buffer;
    std::string         m_aux_buffer;

    bool                m_in_notation;


    [[ noreturn ]] void throw_exception(char const * msg);
    void next();
    char curr() const { return m_curr; }
    char curr_next() { char c = curr(); next(); return c; }
    void check_not_eof(char const * error_msg);
    bool is_next_digit();
    bool is_next_id_rest();
    void move_back(unsigned offset, unsigned u_offset);
    void read_single_line_comment();
    void read_comment_block();
    void read_until(char const * end_str, char const * error_msg);
    unsigned get_utf8_size(unsigned char c);
    void next_utf_core(char c, buffer<char> & cs);
    void next_utf(buffer<char> & cs);

    token_kind read_string();
    token_kind read_number();
    token_kind read_script_block();
    token_kind read_key_cmd_id();
    token_kind read_quoted_symbol();

public:
    scanner(std::istream & strm, char const * strm_name = nullptr, unsigned line = 1);

    int get_line() const { return m_line; }
    int get_pos() const { return m_pos; }
    token_kind scan(environment const & env);
    void set_line(unsigned p);

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
};
std::ostream & operator<<(std::ostream & out, scanner::token_kind k);
void initialize_scanner();
void finalize_scanner();
}
