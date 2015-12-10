/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/blast/strategy.h"

namespace lean {
namespace blast {
/** \brief Base class for grinder-like strategies.
    The methods pre/post/next can be redefined to extend the set of actions
    applied by the grinder. This strategy applies the grinder intro/elim actions. */
class grinder_strategy_core_fn : public strategy_fn {
    virtual char const * get_name() const override { return "grinder"; }
    virtual action_result hypothesis_pre_activation(hypothesis_idx hidx) override;
    virtual action_result hypothesis_post_activation(hypothesis_idx hidx) override;
    virtual action_result next_action() override;
protected:
    virtual action_result pre(hypothesis_idx) { return action_result::failed(); }
    virtual action_result post(hypothesis_idx) { return action_result::failed(); }
    virtual action_result next() { return action_result::failed(); }
public:
};

class grinder_strategy_fn : public grinder_strategy_core_fn {
    std::function<action_result(hypothesis_idx)> m_pre;
    std::function<action_result(hypothesis_idx)> m_post;
    std::function<action_result()>               m_next;
    virtual action_result pre(hypothesis_idx hidx) override { return m_pre(hidx); }
    virtual action_result post(hypothesis_idx hidx) override { return m_post(hidx); }
    virtual action_result next() override { return m_next(); }
public:
    grinder_strategy_fn(std::function<action_result(hypothesis_idx)> const & pre,
                        std::function<action_result(hypothesis_idx)> const & post,
                        std::function<action_result()> const & next):
        m_pre(pre), m_post(post), m_next(next) {}
};

strategy grind_and_then(strategy const & S);
}}
