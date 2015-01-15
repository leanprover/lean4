/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <memory>
#include "util/exception.h"
#include "kernel/pos_info_provider.h"

namespace lean {
/** \brief Lean exception occurred when parsing file. */
class parser_nested_exception : public exception {
    std::shared_ptr<throwable>          m_exception;
    std::shared_ptr<pos_info_provider>  m_provider;
public:
    parser_nested_exception(std::shared_ptr<throwable> const & ex, std::shared_ptr<pos_info_provider> const & pr):
        exception("parser exception"), m_exception(ex), m_provider(pr) {}
    virtual ~parser_nested_exception() {}
    virtual throwable * clone() const { return new parser_nested_exception(m_exception, m_provider); }
    virtual void rethrow() const { throw *this; }
    virtual char const * what() const noexcept { return m_exception->what(); }
    throwable const & get_exception() const { return *(m_exception.get()); }
    pos_info_provider const & get_provider() const { return *(m_provider.get()); }
};
}
