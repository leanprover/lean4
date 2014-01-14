/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include "kernel/for_each_fn.h"
#include "library/io_state_stream.h"
#include "library/parser_nested_exception.h"
#include "library/error_handling/error_handling.h"
#include "frontends/lean/parser_imp.h"

namespace lean {
void parser_imp::display_error_pos(unsigned line, unsigned pos) {
    regular(m_io_state) << m_strm_name << ":" << line << ":";
    if (pos != static_cast<unsigned>(-1))
        regular(m_io_state) << pos << ":";
    regular(m_io_state) << " error:";
}

void parser_imp::display_error_pos(pos_info const & p) { display_error_pos(p.first, p.second); }

void parser_imp::display_error(char const * msg, unsigned line, unsigned pos) {
    display_error_pos(line, pos);
    regular(m_io_state) << " " << msg << endl;
}

std::pair<unsigned, unsigned> parser_imp::lean_pos_info_provider::get_pos_info(expr const & e) const {
    expr const & o = m_parser->m_elaborator.get_original(e);
    auto it = m_parser->m_expr_pos_info.find(o);
    if (it == m_parser->m_expr_pos_info.end())
        return m_pos;
    return it->second;
}

char const * parser_imp::lean_pos_info_provider::get_file_name() const {
    return m_parser->m_strm_name.c_str();
}

void parser_imp::display_error(tactic_cmd_error const & ex) {
    display_error(ex.what(), ex.m_pos.first, ex.m_pos.second);
    display_proof_state(ex.m_state);
}

void parser_imp::display_error(exception const & ex) {
    lean_pos_info_provider pos_provider(m_this.lock(), m_last_cmd_pos);
    ::lean::display_error(m_io_state, &pos_provider, ex);
}

void parser_imp::display_error(script_exception const & ex) {
    lean_pos_info_provider pos_provider(m_this.lock(), m_last_script_pos);
    ::lean::display_error(m_io_state, &pos_provider, ex);
}

#define CATCH(ShowError, ThrowError)                    \
m_found_errors = true;                                  \
if (!m_use_exceptions && m_show_errors) { ShowError ; } \
sync();                                                 \
if (m_use_exceptions) { ThrowError ; }

/**
   \brief Execute the given function \c f, and handle exceptions occurring
   when executing \c f.
   The parameter \c s is an error synchronization procedure.
*/
void parser_imp::protected_call(std::function<void()> && f, std::function<void()> && sync) {
    try {
        f();
    } catch (tactic_cmd_error & ex) {
        CATCH(display_error(ex),
              throw parser_exception(ex.what(), m_strm_name.c_str(), ex.m_pos.first, ex.m_pos.second));
    } catch (parser_exception & ex) {
        CATCH(regular(m_io_state) << ex.what() << endl,
              throw);
    } catch (parser_error & ex) {
        CATCH(display_error(ex.what(), ex.m_pos.first, ex.m_pos.second),
              throw parser_exception(ex.what(), m_strm_name.c_str(), ex.m_pos.first, ex.m_pos.second));
    } catch (interrupted & ex) {
        reset_interrupt();
        if (m_verbose)
            regular(m_io_state) << "!!!Interrupted!!!" << endl;
        sync();
        if (m_use_exceptions)
            throw;
    } catch (script_exception & ex) {
        reset_interrupt();
        CATCH(display_error(ex),
              throw parser_nested_exception(std::shared_ptr<exception>(ex.clone()),
                                            std::shared_ptr<pos_info_provider>(new lean_pos_info_provider(m_this.lock(), m_last_script_pos))));
    } catch (exception & ex) {
        reset_interrupt();
        CATCH(display_error(ex),
              throw parser_nested_exception(std::shared_ptr<exception>(ex.clone()),
                                            std::shared_ptr<pos_info_provider>(new lean_pos_info_provider(m_this.lock(), m_last_cmd_pos))));
    }
}
}
