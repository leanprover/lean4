/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <string>
#include "kernel/environment.h"
#include "library/attribute_manager.h"
#include "library/io_state.h"
namespace lean {
class parser;
class decl_attributes {
private:
    struct entry {
        attribute const * m_attr;
        attr_data_ptr     m_params;
    };

    bool               m_is_abbrev; // if true only abbreviation attributes are allowed
    bool               m_persistent;
    bool               m_parsing_only;
    list<entry>        m_entries;
    optional<unsigned> m_prio;
public:
    decl_attributes(bool is_abbrev = false, bool persistent = true);
    void parse(parser & p);
    environment apply(environment env, io_state const & ios, name const & d) const;
    bool is_parsing_only() const { return m_parsing_only; }
};
}
