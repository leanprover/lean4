/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/blast/action_result.h"

namespace lean {
namespace blast {
void trace_curre_state();
void trace(char const * msg);
void trace_action(char const * a);
void trace_curre_state_if(action_result r);
bool is_trace_enabled();
class scope_trace {
    bool m_old;
public:
    scope_trace(options const & o);
    scope_trace(bool enable);
    ~scope_trace();
};
}}
