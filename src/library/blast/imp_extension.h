/*
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#pragma once
#include "library/blast/state.h"

namespace lean {
namespace blast {

struct imp_extension : branch_extension {
    unsigned              m_state_id;
    imp_extension *       m_parent;
    list<hypothesis>      m_asserts;

    imp_extension(unsigned state_id);
    imp_extension(imp_extension * parent);
    ~imp_extension();

    unsigned get_state_id() { return m_state_id; }
    imp_extension * get_parent() { return m_parent; }
    list<hypothesis> const & get_asserts() { return m_asserts; }

    virtual imp_extension * clone() override;
    virtual void hypothesis_activated(hypothesis const & h, hypothesis_idx hidx) override;
};

struct imp_extension_state {
    virtual void push() =0;
    virtual void pop()  =0;
    virtual void assert(hypothesis const & h) =0;

    virtual ~imp_extension_state() {}

    void replay_actions(imp_extension * imp_ext);
    void undo_actions(imp_extension * imp_ext);
};

typedef std::function<imp_extension_state*()> ext_state_maker;

}}
