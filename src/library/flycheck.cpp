/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/flycheck.h"

namespace lean {
flycheck_scope::flycheck_scope(std::ostream & out, options const & o, char const * kind):
    m_out(out),
    m_flycheck(o.get_bool("flycheck", false)) {
    if (m_flycheck) m_out << "FLYCHECK_BEGIN " << kind << std::endl;
}
flycheck_scope::~flycheck_scope() {
    if (m_flycheck) m_out << "FLYCHECK_END" << std::endl;
}
flycheck_output_scope::flycheck_output_scope(io_state const & ios, char const * stream_name, pos_info const & pos) :
        m_stream_name(stream_name), m_pos(pos),
        m_ios(ios),
        m_redirected_ios(ios),
        m_scoped_ios(), m_buffer() {
    if (ios.get_options().get_bool("flycheck", false)) {
        m_buffer = std::shared_ptr<string_output_channel>(new string_output_channel);
        m_redirected_ios.set_diagnostic_channel(m_buffer);
        m_scoped_ios = std::unique_ptr<scope_global_ios>(new scope_global_ios(m_redirected_ios));
        lean_assert(enabled());
    }
}
flycheck_output_scope::flycheck_output_scope(pos_info_provider const * provider, expr const & ref) :
    flycheck_output_scope(provider ? provider->get_file_name() : "unknown",
                          provider ? provider->get_pos_info_or_some(ref) : pos_info(0, 0)) {}
flycheck_output_scope::~flycheck_output_scope() {
    if (enabled()) {
        auto redirected_output = m_buffer->str();
        if (!redirected_output.empty())
            m_ios.report(message(m_stream_name, m_pos, INFORMATION, "trace output", redirected_output));
    }
}
}
