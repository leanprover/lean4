/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#pragma once
#include <string>
#include "util/message_definitions.h"
#include "util/parser_exception.h"
#include "util/option_ref.h"
#include "runtime/flet.h"

namespace lean {
/*
structure position :=
(line column : nat)
*/
class position : public object_ref {
public:
    position(unsigned line, unsigned column) : object_ref(mk_cnstr(0, nat(line), nat(column))) {}
    position(pos_info const & pos) : position(pos.first, pos.second) {}
    unsigned get_line() const { return static_cast<nat const &>(cnstr_get_ref(*this, 0)).get_small_value(); }
    unsigned get_column() const { return static_cast<nat const &>(cnstr_get_ref(*this, 1)).get_small_value(); }
    pos_info to_pos_info() const { return mk_pair(get_line(), get_column()); }
};

/*
inductive message_severity
| information | warning | error
*/
enum message_severity { INFORMATION, WARNING, ERROR };

/*
structure message :=
(filename : string)
(pos      : position)
(end_pos  : option position  := none)
(severity : message_severity := message_severity.error)
(caption  : string           := "")
(text     : string)
 */
class message : public object_ref {
public:
    message(std::string const & filename, pos_info const & pos, optional<pos_info> const & end_pos,
            message_severity severity, std::string const & caption, std::string const & text) :
        object_ref(mk_cnstr(0, string_ref(filename), position(pos),
                            option_ref<position>(end_pos ? some(position(*end_pos)) : optional<position>()),
                            nat(static_cast<unsigned>(severity)),
                            string_ref(caption), string_ref(text))) {}
    message(std::string const & filename, pos_info const & pos,
            message_severity severity, std::string const & caption, std::string const & text) :
        message(filename, pos, optional<pos_info>(), severity, caption, text) {}
    message(std::string const & filename, pos_info const & pos,
            message_severity severity, std::string const & text) :
        message(filename, pos, severity, std::string(), text) {}
    message(std::string const & filename, pos_info const & pos,
            message_severity severity) :
        message(filename, pos, severity, std::string()) {}
    message(parser_exception const & ex);

    std::string get_filename() const { return static_cast<string_ref const &>(cnstr_get_ref(*this, 0)).to_std_string(); }
    pos_info get_pos() const { return static_cast<position const &>(cnstr_get_ref(*this, 1)).to_pos_info(); }
    optional<pos_info> get_end_pos() const {
        auto pos = static_cast<option_ref<position> const &>(cnstr_get_ref(*this, 2)).get();
        return pos ? some(pos->to_pos_info()) : optional<pos_info>();
    }
    message_severity get_severity() const {
        return static_cast<message_severity>(static_cast<nat const &>(cnstr_get_ref(*this, 3)).get_small_value());
    }
    std::string get_caption() const { return static_cast<string_ref const &>(cnstr_get_ref(*this, 4)).to_std_string(); }
    std::string get_text() const { return static_cast<string_ref const &>(cnstr_get_ref(*this, 5)).to_std_string(); }

    bool is_error() const { return get_severity() >= ERROR; }
};

std::ostream & operator<<(std::ostream &, message const &);
void report_message(message const &);

/*
def message_log := list message
*/
using message_log = list_ref<message>;

bool has_errors(message_log const &);

struct scope_message_log : flet<message_log *> {
    scope_message_log(message_log *);
    scope_message_log(message_log & t) : scope_message_log(&t) {}
};
message_log * global_message_log();
}
