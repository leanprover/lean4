/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/elab_environment.h"
#include "library/compiler/util.h"

namespace lean {
elab_environment compile_ir(elab_environment const & env, options const & opts, comp_decls const & ds);

bool is_llnf_apply(expr const & e);
bool is_llnf_closure(expr const & e);
bool is_llnf_cnstr(expr const & e, name & I, unsigned & cidx, unsigned & nusize, unsigned & ssz);
inline bool is_llnf_cnstr(expr const & e, unsigned & cidx, unsigned & nusize, unsigned & ssz) {
    name I;
    return is_llnf_cnstr(e, I, cidx, nusize, ssz);
}
bool is_llnf_reuse(expr const & e, unsigned & cidx, unsigned & nusize, unsigned & ssz, bool & updt_cidx);
bool is_llnf_reset(expr const & e, unsigned & n);
bool is_llnf_proj(expr const & e, unsigned & idx);
bool is_llnf_sproj(expr const & e, unsigned & sz, unsigned & n, unsigned & offset);
bool is_llnf_fproj(expr const & e, unsigned & n, unsigned & offset);
bool is_llnf_uproj(expr const & e, unsigned & idx);
bool is_llnf_sset(expr const & e, unsigned & sz, unsigned & n, unsigned & offset);
bool is_llnf_fset(expr const & e, unsigned & n, unsigned & offset);
bool is_llnf_f32set(expr const & e, unsigned & n, unsigned & offset);
bool is_llnf_uset(expr const & e, unsigned & n);
bool is_llnf_jmp(expr const & e);
bool is_llnf_unbox(expr const & e, unsigned & n);
bool is_llnf_box(expr const & e, unsigned & n);
bool is_llnf_inc(expr const & e);
bool is_llnf_dec(expr const & e);

bool is_llnf_op(expr const & e);
inline bool is_llnf_cnstr(expr const & e) { unsigned d1, d2, d3; return is_llnf_cnstr(e, d1, d2, d3); }
inline bool is_llnf_reuse(expr const & e) { unsigned d1, d2, d3; bool u; return is_llnf_reuse(e, d1, d2, d3, u); }
inline bool is_llnf_reset(expr const & e) { unsigned i; return is_llnf_reset(e, i); }
inline bool is_llnf_proj(expr const & e) { unsigned d; return is_llnf_proj(e, d); }
inline bool is_llnf_sproj(expr const & e) { unsigned d1, d2, d3; return is_llnf_sproj(e, d1, d2, d3); }
inline bool is_llnf_fproj(expr const & e) { unsigned d1, d2; return is_llnf_fproj(e, d1, d2); }
inline bool is_llnf_uproj(expr const & e) { unsigned d; return is_llnf_uproj(e, d); }
inline bool is_llnf_sset(expr const & e) { unsigned d1, d2, d3; return is_llnf_sset(e, d1, d2, d3); }
inline bool is_llnf_fset(expr const & e) { unsigned d1, d2; return is_llnf_fset(e, d1, d2); }
inline bool is_llnf_f32set(expr const & e) { unsigned d1, d2; return is_llnf_f32set(e, d1, d2); }
inline bool is_llnf_uset(expr const & e) { unsigned d; return is_llnf_uset(e, d); }
inline bool is_llnf_box(expr const & e) { unsigned n; return is_llnf_box(e, n); }
inline bool is_llnf_unbox(expr const & e) { unsigned n; return is_llnf_unbox(e, n); }

expr get_constant_ll_type(elab_environment const & env, name const & c);
unsigned get_llnf_arity(elab_environment const & env, name const & c);

struct field_info {
    /* Remark: the position of a scalar value in
       a constructor object is: `sizeof(void*)*m_idx + m_offset` */
    enum kind { Irrelevant, Object, USize, Scalar };
    kind     m_kind;
    unsigned m_size;   // it is used only if `m_kind == Scalar`
    unsigned m_idx;
    unsigned m_offset; // it is used only if `m_kind == Scalar`
    expr     m_type;
    field_info():m_kind(Irrelevant), m_idx(0), m_type(mk_enf_neutral()) {}
    field_info(unsigned idx):m_kind(Object), m_idx(idx), m_type(mk_enf_object_type()) {}
    field_info(unsigned num, bool):m_kind(USize), m_idx(num), m_type(mk_constant(get_usize_name())) {}
    field_info(unsigned sz, unsigned num, unsigned offset, expr const & type):
        m_kind(Scalar), m_size(sz), m_idx(num), m_offset(offset), m_type(type) {}
    expr get_type() const { return m_type; }
    bool is_float() const { return is_constant(m_type, get_float_name()); }
    bool is_float32() const { return is_constant(m_type, get_float32_name()); }
    static field_info mk_irrelevant() { return field_info(); }
    static field_info mk_object(unsigned idx) { return field_info(idx); }
    static field_info mk_usize() { return field_info(0, true); }
    static field_info mk_scalar(unsigned sz, expr const & type) { return field_info(sz, 0, 0, type); }
};

struct cnstr_info {
    unsigned         m_cidx;
    list<field_info> m_field_info;
    unsigned         m_num_objs{0};
    unsigned         m_num_usizes{0};
    unsigned         m_scalar_sz{0};
    cnstr_info(unsigned cidx, list<field_info> const & finfo);
};

cnstr_info get_cnstr_info(type_checker::state & st, name const & n);

void initialize_llnf();
void finalize_llnf();
}
