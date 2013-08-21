/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <iostream>
#include <vector>
#include "mpq.h"
#include "name.h"
#include "list.h"

namespace lean {
/**
    \brief Lean scanner.
*/
class scanner {
public:
    enum class token {
        LeftParen, RightParen, LeftCurlyBracket, RightCurlyBracket, Colon, Comma, Period, Lambda, Pi, Arrow,
        Let, In, Forall, Exists, Id, CommandId, IntVal, DecimalVal, StringVal, Eq, Assign, Type, Eof
    };
protected:
    int                m_spos; // position in the current line of the stream
    char               m_curr;  // current char;

    int                m_line;  // line
    int                m_pos;   // start position of the token
    std::istream &     m_stream;

    mpq                m_num_val;
    name               m_name_val;
    std::string        m_buffer;

    list<name>         m_commands;

    void  throw_exception(char const * msg);
    char  curr() const { return m_curr; }
    void  new_line() { m_line++; m_spos = 0; }
    void  next();
    bool  check_next(char c);
    void  read_comment();
    name  mk_name(name const & curr, std::string const & buf, bool only_digits);
    token read_a_symbol();
    token read_b_symbol();
    token read_c_symbol();
    token read_number();
    token read_string();
    bool  is_command(name const & n) const;

public:
    scanner(std::istream& stream);
    ~scanner();

    /** \brief Register a new command keyword. */
    void add_command_keyword(name const & n);
    void set_command_keywords(list<name> const & l) { m_commands = l; }

    int get_line() const { return m_line; }
    int get_pos() const { return m_pos; }
    token scan();

    name const & get_name_val() const { return m_name_val; }
    mpq const &  get_num_val() const { return m_num_val; }
    std::string const & get_str_val() const { return m_buffer; }
};
std::ostream & operator<<(std::ostream & out, scanner::token const & t);
}
