/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Sebastian Ullrich
*/
#pragma once
#include "kernel/pos_info_provider.h"
#include <string>

namespace lean {
/** \brief Exception used to track parsing erros, it does not leak outside of this class. */
struct parser_error : public exception {
    pos_info m_pos;
    parser_error(char const * msg, pos_info const & p):exception(msg), m_pos(p) {}
    parser_error(sstream const & msg, pos_info const & p):exception(msg), m_pos(p) {}
    std::string const & get_msg() const { return m_msg; }
    virtual throwable * clone() const { return new parser_error(m_msg.c_str(), m_pos); }
    virtual void rethrow() const { throw *this; }
};

/** \brief Base class for frontend parsers with basic functions */
class abstract_parser : public pos_info_provider {
public:
    /** \brief Return the current position information */
    virtual pos_info pos() const = 0;

    /** \brief Return true iff the current token is a keyword (or command keyword) named \c tk */
    virtual bool curr_is_token(name const & tk) const = 0;
    /** \brief Return true iff the current token is a numeral */
    virtual bool curr_is_numeral() const = 0;
    /** \brief Read the next token if the current one is not End-of-file. */
    virtual void next() = 0;

    virtual unsigned parse_small_nat() = 0;
    virtual std::string parse_string_lit() = 0;
    virtual name_map<std::string> parse_kv_pairs() = 0;
};
}
