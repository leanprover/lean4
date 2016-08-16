/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "util/sstream.h"
#include "library/kernel_serializer.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/tokens.h"

namespace lean {
static name * g_structure_instance_name          = nullptr;
static std::string * g_structure_instance_opcode = nullptr;

[[ noreturn ]] static void throw_se_ex() { throw exception("unexpected occurrence of 'structure instance' expression"); }

/*
  We encode a 'structure instance' expression using a macro.
  This is a trick to avoid creating a new kind of expression.
  'Structure instance' expressions are temporary objects used by the elaborator.
  Example: Given
     structure point (A B : Type) := (x : A) (y : B)
  the structure instance
     {| point, x := 10, y := 20 |}
  is compiled into
     point.mk 10 20
*/
class structure_instance_macro_cell : public macro_definition_cell {
    list<name> m_fields;
public:
    structure_instance_macro_cell(list<name> const & fs):m_fields(fs) {}
    virtual name get_name() const { return *g_structure_instance_name; }
    virtual expr check_type(expr const &, abstract_type_context &, bool) const { throw_se_ex(); }
    virtual optional<expr> expand(expr const &, abstract_type_context &) const { throw_se_ex(); }
    virtual void write(serializer & s) const {
        s << *g_structure_instance_opcode;
        write_list(s, m_fields);
    }
    list<name> const & get_field_names() const { return m_fields; }
};

static expr mk_structure_instance(list<name> const & fs, unsigned num, expr const * args) {
    lean_assert(num >= length(fs) + 1);
    macro_definition def(new structure_instance_macro_cell(fs));
    return mk_macro(def, num, args);
}

bool is_structure_instance(expr const & e) {
    return is_macro(e) && macro_def(e).get_name() == *g_structure_instance_name;
}

void destruct_structure_instance(expr const & e, expr & t, buffer<name> & field_names,
                                 buffer<expr> & field_values, buffer<expr> & using_exprs) {
    lean_assert(is_structure_instance(e));
    t = macro_arg(e, 0);
    list<name> const & fns = static_cast<structure_instance_macro_cell const*>(macro_def(e).raw())->get_field_names();
    unsigned num_fileds = length(fns);
    to_buffer(fns, field_names);
    for (unsigned i = 1; i < num_fileds+1; i++)
        field_values.push_back(macro_arg(e, i));
    for (unsigned i = num_fileds+1; i < macro_num_args(e); i++)
        using_exprs.push_back(macro_arg(e, i));
}

static expr parse_struct_expr_core(parser & p, pos_info const & pos, bool curly_bar) {
    expr t = p.parse_expr();
    buffer<name> field_names;
    buffer<expr> field_values;
    buffer<expr> using_exprs;
    while (p.curr_is_token(get_comma_tk())) {
        p.next();
        pair<optional<name>, expr> id_e = p.parse_optional_assignment();
        if (id_e.first) {
            field_names.push_back(*id_e.first);
            field_values.push_back(id_e.second);
        } else {
            using_exprs.push_back(id_e.second);
        }
    }
    if (curly_bar)
        p.check_token_next(get_rcurlybar_tk(), "invalid structure expression, '|}' expected");
    else
        p.check_token_next(get_rdcurly_tk(), "invalid structure expression, '⦄' expected");
    buffer<expr> args;
    args.push_back(t);
    args.append(field_values);
    args.append(using_exprs);
    return p.save_pos(mk_structure_instance(to_list(field_names), args.size(), args.data()), pos);
}

static expr parse_struct_curly_bar(parser & p, unsigned, expr const *, pos_info const & pos) {
    bool curly_bar = true;
    return parse_struct_expr_core(p, pos, curly_bar);
}

static expr parse_struct_dcurly(parser & p, unsigned, expr const *, pos_info const & pos) {
    bool curly_bar = false;
    return parse_struct_expr_core(p, pos, curly_bar);
}

void init_structure_instance_parsing_rules(parse_table & r) {
    expr x0 = mk_var(0);
    r = r.add({notation::transition("{|", notation::mk_ext_action(parse_struct_curly_bar))}, x0);
    r = r.add({notation::transition("⦃",  notation::mk_ext_action(parse_struct_dcurly))}, x0);
}

void initialize_structure_instance() {
    g_structure_instance_name   = new name("structure instance");
    g_structure_instance_opcode = new std::string("STI");
    register_macro_deserializer(*g_structure_instance_opcode,
                                [](deserializer & d, unsigned num, expr const * args) {
                                    list<name> fs;
                                    fs = read_list<name>(d);
                                    if (num < length(fs) + 1)
                                        throw corrupted_stream_exception();
                                    return mk_structure_instance(fs, num, args);
                                });
}

void finalize_structure_instance() {
    delete g_structure_instance_opcode;
    delete g_structure_instance_name;
}
}
