/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#pragma once
#include <string>
#include <iostream>
#include "util/name.h"
#include "util/flet.h"
#include "util/numerics/mpq.h"
#include "kernel/pos_info_provider.h"
#include "kernel/environment.h"

namespace lean {
namespace smt2 {

typedef std::string symbol;

class scanner {
public:
    enum class token_kind { BEGIN, END, LEFT_PAREN, RIGHT_PAREN, KEYWORD, SYMBOL, STRING, INT, FLOAT, BV };

    enum class char_kind { END, WHITESPACE, COMMENT, LEFT_PAREN, RIGHT_PAREN, KEYWORD, QUOTED_SYMBOL, STRING, NUMBER, BV, SIMPLE_SYMBOL, UNEXPECTED };

private:
    std::istream &      m_stream;
    std::string         m_stream_name;
    std::string         m_curr_line{1};
    bool                m_last_line{1};

    char                m_curr;     // current char;
    int                 m_cline{0}; // line of the char
    int                 m_cpos{0};  // position of the char

    token_kind          m_token_kind; // current token;
    int                 m_tline;      // line of the token
    int                 m_tpos;       // start position of the token

    std::string         m_str_val;
    mpq                 m_num_val;
    unsigned            m_bv_size;

    [[ noreturn ]] void throw_exception(char const * msg);
    [[ noreturn ]] void throw_exception(std::string const & msg);

    void next();
    char curr() const { return m_curr; }
    char curr_next() { char c = curr(); next(); return c; }
    void check_not_eof(char const * error_msg);

    bool is_next_digit();
    void read_simple_symbol_core();
    void read_hex_bv_literal();
    void read_bin_bv_literal();

    void read_simple_symbol();
    void read_keyword();
    void read_quoted_symbol();
    void read_comment();
    token_kind read_number();
    void read_string();
    void read_bv_literal();

public:
    scanner(std::istream & strm, char const * strm_name);

    pos_info get_pos_info() const { return pos_info(m_cline + 1, m_cpos); }
    token_kind scan();

    mpq const & get_num_val() const { return m_num_val; }
    std::string const & get_str_val() const { return m_str_val; }
    symbol const & get_symbol_val() const { return m_str_val; }
    token_kind const & get_token_kind() const { return m_token_kind; }

    std::string const & get_stream_name() const { return m_stream_name; }
};

std::ostream & operator<<(std::ostream & out, scanner::token_kind k);
void initialize_scanner();
void finalize_scanner();
}}
