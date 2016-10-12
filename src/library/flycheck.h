/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <iostream>
#include "kernel/pos_info_provider.h"
#include "util/sexpr/options.h"
#include "library/io_state.h"
#include "library/messages.h"

namespace lean {
/** \brief Auxiliary object for "inserting" delimiters for flycheck */
class flycheck_message_stream : public message_stream {
    std::ostream & m_out;
public:
    flycheck_message_stream(std::ostream & out) : m_out(out) {}
    ~flycheck_message_stream() {}
    void report(message const & msg) override;
};
}
