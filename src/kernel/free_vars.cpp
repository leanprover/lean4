/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include "free_vars.h"
#include "sets.h"

namespace lean {

class has_free_var_functor {
    expr_cell_offset_set m_visited;
public:
    bool apply(expr const & e, unsigned offset) {
        // handle easy cases
        switch (e.kind()) {
        case expr_kind::Constant: case expr_kind::Prop: case expr_kind::Type: case expr_kind::Numeral:
            return false;
        case expr_kind::Var:
            return var_idx(e) >= offset;
        case expr_kind::App: case expr_kind::Lambda: case expr_kind::Pi:
            break;
        }

        if (e.raw()->is_closed())
            return false;

        if (is_shared(e)) {
            expr_cell_offset p(e.raw(), offset);
            if (m_visited.find(p) != m_visited.end())
                return false;
            m_visited.insert(p);
        }

        bool result = false;

        switch (e.kind()) {
        case expr_kind::Constant: case expr_kind::Prop: case expr_kind::Type: case expr_kind::Numeral: case expr_kind::Var:
            // easy cases were already handled
            lean_unreachable(); return false;
        case expr_kind::App:
            result = std::any_of(begin_args(e), end_args(e), [=](expr const & arg){ return apply(arg, offset); });
            break;
        case expr_kind::Lambda:
        case expr_kind::Pi:
            result = apply(abst_type(e), offset) || apply(abst_body(e), offset + 1);
            break;
        }

        if (!result)
            e.raw()->set_closed();

        return result;
    }
};

bool has_free_vars(expr const & e) {
    has_free_var_functor f;
    return f.apply(e, 0);
}

}
