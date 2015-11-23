/*
Copyright (c) 2015 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam
*/
#pragma once
#include "library/blast/action_result.h"
#include "library/blast/gexpr.h"
#include "library/blast/blast.h"

namespace lean {
namespace blast {

struct forward_branch_extension : public branch_extension {
    head_map<expr> m_index;
    forward_branch_extension() {}
    forward_branch_extension(forward_branch_extension const & b): m_index(b.m_index) {}
    virtual ~forward_branch_extension() {}
    virtual branch_extension * clone() override { return new forward_branch_extension(*this); }
    virtual void initialized() override;
    virtual void hypothesis_activated(hypothesis const & h, hypothesis_idx hidx) override;
    virtual void hypothesis_deleted(hypothesis const & , hypothesis_idx ) override;
    void index_expr(expr const & e);
public:
    head_map<expr> const & get_index() { return m_index; }
};

forward_branch_extension & get_extension();

void initialize_forward_extension();
void finalize_forward_extension();
}}
