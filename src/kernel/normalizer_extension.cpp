/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/normalizer_extension.h"

namespace lean {
class id_normalizer_extension : public normalizer_extension {
public:
    virtual optional<pair<expr, constraint_seq>> operator()(expr const &, extension_context &) const {
        return optional<pair<expr, constraint_seq>>();
    }
    virtual optional<expr> is_stuck(expr const &, extension_context &) const { return none_expr(); }
    virtual bool supports(name const &) const { return false; }
};

std::unique_ptr<normalizer_extension> mk_id_normalizer_extension() {
    return std::unique_ptr<normalizer_extension>(new id_normalizer_extension());
}

class comp_normalizer_extension : public normalizer_extension {
    std::unique_ptr<normalizer_extension> m_ext1;
    std::unique_ptr<normalizer_extension> m_ext2;
public:
    comp_normalizer_extension(std::unique_ptr<normalizer_extension> && ext1, std::unique_ptr<normalizer_extension> && ext2):
        m_ext1(std::move(ext1)), m_ext2(std::move(ext2)) {}

    virtual optional<pair<expr, constraint_seq>> operator()(expr const & e, extension_context & ctx) const {
        if (auto r = (*m_ext1)(e, ctx))
            return r;
        else
            return (*m_ext2)(e, ctx);
    }

    virtual optional<expr> is_stuck(expr const & e, extension_context & ctx) const {
        if (auto r = m_ext1->is_stuck(e, ctx))
            return r;
        else
            return m_ext2->is_stuck(e, ctx);
    }

    virtual bool supports(name const & feature) const {
        return m_ext1->supports(feature) || m_ext2->supports(feature);
    }
};

std::unique_ptr<normalizer_extension> compose(std::unique_ptr<normalizer_extension> && ext1, std::unique_ptr<normalizer_extension> && ext2) {
    return std::unique_ptr<normalizer_extension>(new comp_normalizer_extension(std::move(ext1), std::move(ext2)));
}
}
