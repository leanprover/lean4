/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/sstream.h"
#include "library/io_state.h"
#include "library/tactic/tactic_state.h"

namespace lean {
class elaborator_exception : public formatted_exception {
protected:
    bool m_ignore = false; // We ignore exceptions that mention synthetic sorrys.
public:
    elaborator_exception(optional<pos_info> const & p, format const & fmt):formatted_exception(p, fmt) {}
    elaborator_exception(optional<expr> const & e, format const & fmt):formatted_exception(e, fmt) {}
    elaborator_exception(expr const & e, format const & fmt):formatted_exception(e, fmt) {}
    elaborator_exception(expr const & e, sstream const & strm):formatted_exception(e, format(strm.str())) {}
    elaborator_exception(expr const & e, char const * msg):formatted_exception(e, format(msg)) {}

    elaborator_exception && ignore_if(bool b) { m_ignore = b; return std::move(*this); }
    bool is_ignored() const { return m_ignore; }

    virtual throwable * clone() const override;
    virtual void rethrow() const override { throw *this; }
};

class failed_to_synthesize_placeholder_exception : public elaborator_exception {
    expr         m_mvar;
    tactic_state m_state;
public:
    failed_to_synthesize_placeholder_exception(expr const & e, tactic_state const & s):
        elaborator_exception(e, "don't know how to synthesize placeholder"),
        m_mvar(e), m_state(s) {}
    virtual throwable * clone() const override {
        return new failed_to_synthesize_placeholder_exception(m_mvar, m_state);
    }
    failed_to_synthesize_placeholder_exception && ignore_if(bool b) { m_ignore = b; return std::move(*this); }
    virtual void rethrow() const override { throw *this; }
    expr const & get_mvar() const { return m_mvar; }
    tactic_state const & get_tactic_state() const { return m_state; }
    virtual format pp() const override;
};

class nested_elaborator_exception : public elaborator_exception {
    std::shared_ptr<elaborator_exception> m_exception;
    nested_elaborator_exception(optional<pos_info> const & p, format const & fmt,
                                std::shared_ptr<elaborator_exception> const & ex):
        elaborator_exception(p, fmt), m_exception(ex) {}
public:
    nested_elaborator_exception(optional<pos_info> const & p, elaborator_exception const & ex, format const & fmt):
        elaborator_exception(p, fmt),
        m_exception(static_cast<elaborator_exception*>(ex.clone())) {
        m_ignore = ex.is_ignored();
    }
    nested_elaborator_exception(expr const & ref, elaborator_exception const & ex, format const & fmt):
        nested_elaborator_exception(get_pos_info(ref), ex, fmt) {}
    nested_elaborator_exception && ignore_if(bool b) { m_ignore = b; return std::move(*this); }
    virtual void rethrow() const override { throw *this; }
    virtual throwable * clone() const override;
    virtual optional<pos_info> get_pos() const override;
    virtual format pp() const override;
};
}
