/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/blast/strategy.h"
#include "library/blast/actions/simple_actions.h"
#include "library/blast/actions/intros_action.h"

namespace lean {
namespace blast {
class action_strategy_core_fn : public strategy_fn {
    char const * m_name;

    virtual action_result pre(hypothesis_idx) { return action_result::failed(); }
    virtual action_result post(hypothesis_idx) { return action_result::failed(); }
    virtual action_result next() { return action_result::failed(); }

    virtual char const * get_name() const override { return m_name; }

    virtual action_result hypothesis_pre_activation(hypothesis_idx hidx) override {
        Try(assumption_contradiction_actions(hidx));
        Try(discard_action(hidx));
        Try(pre(hidx));
        return action_result::new_branch();
    }

    virtual action_result hypothesis_post_activation(hypothesis_idx hidx) override {
        Try(post(hidx));
        return action_result::new_branch();
    }

    virtual action_result next_action() override {
        Try(intros_action());
        Try(assumption_action());
        Try(activate_hypothesis());
        Try(trivial_action());
        Try(next());
        return action_result::failed();
    }
public:
    action_strategy_core_fn(char const * n):m_name(n) {}
};

class pre_action_strategy_fn : public action_strategy_core_fn {
    std::function<action_result(hypothesis_idx)> m_action;
    virtual action_result pre(hypothesis_idx hidx) { return m_action(hidx); }
public:
    pre_action_strategy_fn(char const * n, std::function<action_result(hypothesis_idx)> const & a):
        action_strategy_core_fn(n),
        m_action(a) {}
};

class post_action_strategy_fn : public action_strategy_core_fn {
    std::function<action_result(hypothesis_idx)> m_action;
    virtual action_result post(hypothesis_idx hidx) { return m_action(hidx); }
public:
    post_action_strategy_fn(char const * n, std::function<action_result(hypothesis_idx)> const & a):
        action_strategy_core_fn(n),
        m_action(a) {}
};

class action_strategy_fn : public action_strategy_core_fn {
    std::function<action_result()> m_action;
    virtual action_result next() { return m_action(); }
public:
    action_strategy_fn(char const * n, std::function<action_result()> const & a):
        action_strategy_core_fn(n),
        m_action(a) {}
};

class xaction_strategy_fn : public action_strategy_core_fn {
    std::function<action_result(hypothesis_idx)> m_pre;
    std::function<action_result(hypothesis_idx)> m_post;
    std::function<action_result()>               m_next;

    virtual action_result pre(hypothesis_idx hidx) { return m_pre(hidx); }
    virtual action_result post(hypothesis_idx hidx) { return m_post(hidx); }
    virtual action_result next() { return m_next(); }
public:
    xaction_strategy_fn(char const * n,
                        std::function<action_result(hypothesis_idx)> const & pre,
                        std::function<action_result(hypothesis_idx)> const & post,
                        std::function<action_result()> const & next):
        action_strategy_core_fn(n),
        m_pre(pre), m_post(post), m_next(next) {}
};

strategy mk_action_strategy(char const * n, std::function<action_result()> const & a) {
    return [=]() { return action_strategy_fn(n, a)(); }; // NOLINT
}

strategy mk_pre_action_strategy(char const * n, std::function<action_result(hypothesis_idx)> const & a) {
    return [=]() { return pre_action_strategy_fn(n, a)(); }; // NOLINT
}

strategy mk_post_action_strategy(char const * n, std::function<action_result(hypothesis_idx)> const & a) {
    return [=]() { return post_action_strategy_fn(n, a)(); }; // NOLINT
}

strategy mk_action_strategy(char const * n,
                            std::function<action_result(hypothesis_idx)> const & pre,
                            std::function<action_result(hypothesis_idx)> const & post,
                            std::function<action_result()> const & next) {
    return [=]() { return xaction_strategy_fn(n, pre, post, next)(); }; // NOLINT
}
}}
