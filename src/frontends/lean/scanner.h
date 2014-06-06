/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include <iostream>
#include "util/name.h"
#include "util/numerics/mpq.h"
#include "frontends/lean/token_set.h"

namespace lean {
/**
    \brief Scanner. The behavior of the scanner is controlled using a token set.

    The scanner has builtin support for comments, script blocks,
    identifiers, numerals, decimals, strings. Everything else is only
    accepted if they are in the token set.
*/
class scanner {
public:
    enum class token_kind {Keyword, CommandKeyword, ScriptBlock, Identifier, Numeral, Decimal, String, Eof};
protected:
    token_set          m_tokens;
    std::istream &     m_stream;
    std::string        m_stream_name;

    int                m_spos;  // current position
    int                m_sline; // current line
    char               m_curr;  // current char;

    int                m_pos;   // start position of the token
    int                m_line;  // line of the token

    name               m_name_val;
    token_info const * m_token_info;
    mpq                m_num_val;
    std::string        m_buffer;
    std::string        m_aux_buffer;

    [[ noreturn ]] void throw_exception(char const * msg) const;
    void next();
    char curr() const { return m_curr; }
    char curr_next() { char c = curr(); next(); return c; }
    void new_line() { m_sline++; m_spos = 0; }
    void update_line() { if (curr() == '\n') new_line(); }
    void check_not_eof(char const * error_msg) const;
    bool is_next_digit();
    bool is_next_id_rest();
    void move_back(std::streamoff offset);
    bool consume(char const * str, char const * error_msg);
    void read_single_line_comment();
    void read_comment_block();
    void read_until(char const * end_str, char const * error_msg);

    token_kind read_string();
    token_kind read_number();
    token_kind read_script_block();
    token_kind read_key_cmd_id();

public:
    scanner(token_set const & tks, std::istream & strm, char const * strm_name = nullptr);

    int get_line() const { return m_line; }
    int get_pos() const { return m_pos; }
    token_kind scan();

    mpq const & get_num_val() const { return m_num_val; }
    name const & get_name_val() const { return m_name_val; }
    std::string const & get_str_val() const { return m_buffer; }
    token_info const & get_token_info() const { lean_assert(m_token_info); return *m_token_info; }
};
std::ostream & operator<<(std::ostream & out, scanner::token_kind k);
}
