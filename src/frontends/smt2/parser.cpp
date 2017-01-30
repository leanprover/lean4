/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#include <string>
#include <stack>
#include <utility>
#include <vector>
#include "util/flet.h"
#include "util/name_map.h"
#include "util/exception.h"
#include "util/fresh_name.h"
#include "util/lean_path.h"
#include "kernel/environment.h"
#include "kernel/kernel_exception.h"
#include "kernel/abstract.h"
#include "kernel/instantiate.h"
#include "kernel/error_msgs.h"
#include "kernel/declaration.h"
#include "kernel/type_checker.h"
#include "kernel/expr_maps.h"
#include "kernel/pos_info_provider.h"
#include "library/message_builder.h"
#include "library/app_builder.h"
#include "library/constants.h"
#include "library/io_state.h"
#include "library/io_state_stream.h"
#include "library/local_context.h"
#include "library/pp_options.h"
#include "library/module.h"
#include "library/trace.h"
#include "library/mpq_macro.h"
#include "library/scope_pos_info_provider.h"
#include "library/tactic/tactic_state.h"
#include "frontends/smt2/scanner.h"
#include "frontends/smt2/elaborator.h"
#include "frontends/smt2/parser.h"

namespace lean {
namespace smt2 {

static name * g_smt2_unique_prefix;

// Reserved words
// (a) General
// static char const * g_token_as          = "as";
static char const * g_token_exists      = "exists";
static char const * g_token_forall      = "forall";
static char const * g_token_let         = "let";

// (b) Command names
static char const * g_token_assert                = "assert";
static char const * g_token_check_sat             = "check-sat";
static char const * g_token_check_sat_assuming    = "check-sat-assuming";
static char const * g_token_declare_const         = "declare-const";
static char const * g_token_declare_fun           = "declare-fun";
static char const * g_token_declare_sort          = "declare-sort";
static char const * g_token_define_fun            = "define-fun";
static char const * g_token_define_fun_rec        = "define-fun-rec";
static char const * g_token_define_funs_rec       = "define-fun-rec";
static char const * g_token_define_sort           = "define-sort";
static char const * g_token_echo                  = "echo";
static char const * g_token_exit                  = "exit";
static char const * g_token_get_assertions        = "get-assertions";
static char const * g_token_get_assignment        = "get-assignment";
static char const * g_token_get_info              = "get-info";
static char const * g_token_get_model             = "get-model";
static char const * g_token_get_option            = "get-option";
static char const * g_token_get_proof             = "get-proof";
static char const * g_token_get_unsat_assumptions = "get-unsat-assumptions";
static char const * g_token_get_unsat_core        = "get-unsat-core";
static char const * g_token_get_value             = "get-value";
static char const * g_token_pop                   = "pop";
static char const * g_token_push                  = "push";
static char const * g_token_reset                 = "reset";
static char const * g_token_reset_assertions      = "reset-assertions";
static char const * g_token_set_info              = "set-info";
static char const * g_token_set_logic             = "set-logic";
static char const * g_token_set_option            = "set-option";

// Making bindings
enum class binding_type { FORALL, EXISTS, LET };

expr mk_binding(local_context const & lctx, binding_type btype, unsigned num_locals, expr const * locals, expr const & e) {
    buffer<local_decl>     decls;
    buffer<expr>           types;
    buffer<optional<expr>> values;
    for (unsigned i = 0; i < num_locals; i++) {
        local_decl const & decl = *lctx.get_local_decl(locals[i]);
        decls.push_back(decl);
        types.push_back(::lean::abstract_locals(decl.get_type(), i, locals));
        if (auto v = decl.get_value())
            values.push_back(some_expr(::lean::abstract_locals(*v, i, locals)));
        else
            values.push_back(none_expr());
    }
    expr new_e = ::lean::abstract_locals(e, num_locals, locals);
    lean_assert(types.size() == values.size());
    unsigned i = types.size();
    while (i > 0) {
        --i;
        switch (btype) {
        case binding_type::FORALL:
            lean_assert(!values[i]);
            new_e = ::lean::mk_pi(decls[i].get_pp_name(), types[i], new_e, decls[i].get_info());
            break;
        case binding_type::EXISTS:
            lean_assert(!values[i]);
            // @Exists.{l_1} ?A (λ (x : ?A), @eq.{l_1} ?A x x) : Prop
            new_e = mk_app(mk_constant(get_Exists_name(), {mk_level_one()}),
                           types[i],
                           ::lean::mk_lambda(decls[i].get_pp_name(), types[i], new_e, decls[i].get_info()));
            break;
        case binding_type::LET:
            lean_assert(values[i]);
            new_e = mk_let(decls[i].get_pp_name(), types[i], *values[i], new_e);
            break;
        }
    }
    return new_e;
}

expr mk_binding(local_context const & lctx, binding_type btype, buffer<expr> const & locals, expr const & e) {
    return mk_binding(lctx, btype, locals.size(), locals.data(), e);
}

// Parser class
class parser : public pos_info_provider {
public:
    // pos_info_provider interface
    virtual optional<pos_info> get_pos_info(expr const &) const override { return optional<pos_info>(); }
    virtual char const * get_file_name() const override { return m_scanner.get_stream_name().c_str(); }
    virtual pos_info get_some_pos() const override { return m_scanner.get_pos_info(); }

private:
    struct exit_exception : public exception {};

    environment             m_env;
    io_state                m_ios;

    local_context           m_lctx;

    scanner                 m_scanner;
    scanner::token_kind     m_curr_kind{scanner::token_kind::BEGIN};

    bool                    m_use_locals{true};
    bool                    m_verbose{false};

    type_context *          m_tctx_ptr{nullptr};

    // Util
    std::string const & get_stream_name() const { return m_scanner.get_stream_name(); }

    [[ noreturn ]] void throw_parser_exception(char const * msg, pos_info p) {
        throw parser_exception(msg, get_stream_name().c_str(), p.first, p.second);
    }

    [[ noreturn ]] void throw_parser_exception(std::string const & msg) { throw_parser_exception(msg.c_str(), m_scanner.get_pos_info()); }
    [[ noreturn ]] void throw_parser_exception(char const * msg) { throw_parser_exception(msg, m_scanner.get_pos_info()); }

    // Only named constants that are going into the global environment need to
    // prefixed to avoid clashes
    void register_hypothesis(symbol const & sym, expr const & ty) {
        if (m_use_locals) {
            m_lctx.mk_local_decl(sym, ty);
        } else {
            declaration d = mk_axiom(mk_user_name(sym), list<name>(), ty);
            m_env = env().add(check(env(), d));
        }
    }

    void register_hypothesis(expr const & ty) {
        name n = mk_tagged_fresh_name(*g_smt2_unique_prefix);
        if (m_use_locals) {
            m_lctx.mk_local_decl(n, ty);
        } else {
            declaration d = mk_axiom(n, list<name>(), ty);
            m_env = env().add(check(env(), d));
        }
    }

    environment & env() { return m_env; }
    io_state & ios() { return m_ios; }
    local_context const & lctx() { return m_tctx_ptr ? m_tctx_ptr->lctx() : m_lctx; }

    scanner::token_kind curr_kind() const { return m_curr_kind; }
    std::string const & curr_string() const { return m_scanner.get_str_val(); }
    symbol const & curr_symbol() const { return m_scanner.get_symbol_val(); }
    mpq const & curr_numeral() const { return m_scanner.get_num_val(); }
    mpq curr_numeral_next() { mpq q = m_scanner.get_num_val(); next(); return q; }

    void scan() { m_curr_kind = m_scanner.scan(); }

    void next() { if (m_curr_kind != scanner::token_kind::END) scan(); }

    void check_curr_kind(scanner::token_kind kind, char const * msg) {
        if (curr_kind() != kind)
            throw_parser_exception(msg);
    }

    void check_curr_kind(scanner::token_kind kind, std::string const & msg) {
        if (curr_kind() != kind)
            throw_parser_exception(msg);
    }

    // Parser helpers
    // Parsing sorts
    void parse_sorted_var_list(buffer<expr> & bindings, char const * context) {
        lean_assert(m_tctx_ptr);
        check_curr_kind(scanner::token_kind::LEFT_PAREN, std::string(context) + ": sorted-var list expected");
        next();
        while (curr_kind() == scanner::token_kind::LEFT_PAREN) {
            next();
            check_curr_kind(scanner::token_kind::SYMBOL, std::string(context) + ": invalid sorted-val list");
            symbol sym = curr_symbol();
            next();
            expr ty = parse_expr(context);
            expr l = m_tctx_ptr->push_local(sym, ty);
            bindings.push_back(l);
            check_curr_kind(scanner::token_kind::RIGHT_PAREN, std::string(context) + ": invalid sorted-val list");
            next();
        }
        check_curr_kind(scanner::token_kind::RIGHT_PAREN, std::string(context) + ": invalid sorted-val list");
        next();
    }

    void parse_var_binding_list(buffer<expr> & bindings, char const * context) {
        lean_assert(m_tctx_ptr);
        check_curr_kind(scanner::token_kind::LEFT_PAREN, std::string(context) + ": var-binding list expected");
        next();
        while (curr_kind() == scanner::token_kind::LEFT_PAREN) {
            next();
            check_curr_kind(scanner::token_kind::SYMBOL, std::string(context) + ": invalid var-binding list");
            symbol sym = curr_symbol();
            next();
            expr val = parse_expr(context);
            expr ty = m_tctx_ptr->infer(val);
            expr l = m_tctx_ptr->push_let(sym, ty, val);
            bindings.push_back(l);
            check_curr_kind(scanner::token_kind::RIGHT_PAREN, std::string(context) + ": invalid var-binding list");
            next();
        }
        check_curr_kind(scanner::token_kind::RIGHT_PAREN, std::string(context) + ": invalid var-binding list");
        next();
    }

    void parse_attributes(char const * context) {
        // TODO(dhs): currently ignores all attributes
        check_curr_kind(scanner::token_kind::KEYWORD, std::string(context) + ": invalid attributes");
        while (curr_kind() == scanner::token_kind::KEYWORD) {
            next();
            bool still_in_attribute = true;
            int num_open_paren = 0;
            while (still_in_attribute) {
                switch (curr_kind()) {
                case scanner::token_kind::SYMBOL:
                case scanner::token_kind::STRING:
                case scanner::token_kind::INT:
                case scanner::token_kind::FLOAT:
                case scanner::token_kind::BV:
                    next();
                    break;
                case scanner::token_kind::LEFT_PAREN:
                    num_open_paren++;
                    next();
                    break;
                case scanner::token_kind::RIGHT_PAREN:
                    if (--num_open_paren < 1)
                        still_in_attribute = false;
                    if (num_open_paren >= 0)
                        next();
                    break;
                default:
                    still_in_attribute = false;
                    break;
                }
            }
        }
    }

    expr parse_expr(char const * context) {
        symbol sym;
        buffer<expr> args;
        optional<local_decl> l;

        switch (curr_kind()) {
        case scanner::token_kind::SYMBOL:
            sym = curr_symbol();
            next();
            l = lctx().get_local_decl_from_user_name(sym);
            if (l)
                return l->mk_ref();
            else
                return elaborate_constant(sym);
            lean_unreachable();
            break;
        case scanner::token_kind::STRING:
            // TODO(dhs): strings
            throw_parser_exception("string literals not accepted in expressions yet");
            lean_unreachable();
            break;
        case scanner::token_kind::INT:
            // TODO(dhs): Lean's bv may want a Nat instead of an Int
            return mk_mpq_macro(curr_numeral_next(), mk_constant(get_int_name()));
        case scanner::token_kind::FLOAT:
            return mk_mpq_macro(curr_numeral_next(), mk_constant(get_real_name()));
        case scanner::token_kind::BV:
            // TODO(dhs): bit vectors
            // (Already getting the value in the scanner, just don't have a good Lean target yet)
            throw_parser_exception("bit-vector literals not accepted in expressions yet");
            lean_unreachable();
            break;
        case scanner::token_kind::LEFT_PAREN:
            next();
            if (curr_kind() == scanner::token_kind::SYMBOL && curr_symbol() == "_") {
                // dependent types
                next();
                parse_exprs(args, context);
                // Note: there are no dependent applications that require elaboration on their own
                lean_assert(args.size() > 1);
                return mk_app(args);
            } else if (curr_kind() == scanner::token_kind::SYMBOL && curr_symbol() == "!") {
                // annotated terms
                next();
                expr e = parse_expr(context);
                parse_attributes(context);
                check_curr_kind(scanner::token_kind::RIGHT_PAREN, "invalid constant declaration, ')' expected");
                next();
                return e;
            } else if (curr_kind() == scanner::token_kind::SYMBOL && curr_symbol() == g_token_forall) {
                lean_assert(m_tctx_ptr);
                next();
                buffer<expr> bindings;
                parse_sorted_var_list(bindings, context);
                expr e = parse_expr(context);
                expr pi = mk_binding(m_tctx_ptr->lctx(), binding_type::FORALL, bindings, e);
                for (unsigned i = 0; i < bindings.size(); ++i)
                    m_tctx_ptr->pop_local();
                check_curr_kind(scanner::token_kind::RIGHT_PAREN, "invalid constant declaration, ')' expected");
                next();
                return pi;
            } else if (curr_kind() == scanner::token_kind::SYMBOL && curr_symbol() == g_token_exists) {
                lean_assert(m_tctx_ptr);
                next();
                buffer<expr> bindings;
                parse_sorted_var_list(bindings, context);
                expr e = parse_expr(context);
                expr exists = mk_binding(m_tctx_ptr->lctx(), binding_type::EXISTS, bindings, e);
                for (unsigned i = 0; i < bindings.size(); ++i)
                    m_tctx_ptr->pop_local();
                check_curr_kind(scanner::token_kind::RIGHT_PAREN, "invalid constant declaration, ')' expected");
                next();
                return exists;
            } else if (curr_kind() == scanner::token_kind::SYMBOL && curr_symbol() == g_token_let) {
                lean_assert(m_tctx_ptr);
                next();
                buffer<expr> bindings;
                parse_var_binding_list(bindings, context);
                expr e = parse_expr(context);
                expr let = mk_binding(m_tctx_ptr->lctx(), binding_type::LET, bindings, e);
                for (unsigned i = 0; i < bindings.size(); ++i)
                    m_tctx_ptr->pop_local();
                check_curr_kind(scanner::token_kind::RIGHT_PAREN, "invalid constant declaration, ')' expected");
                next();
                return let;
            } else {
                parse_exprs(args, context);
                // When parsing sorts, we don't bother elaborating applications
                if (m_tctx_ptr)
                    return elaborate_app(*m_tctx_ptr, args);
                else
                    return mk_app(args);
            }
        default:
            throw_parser_exception((std::string(context) + ", invalid sort").c_str());
            lean_unreachable();
            break;
        }
        lean_unreachable();
    }

    void parse_exprs(buffer<expr> & es, char const * context) {
        while (curr_kind() != scanner::token_kind::RIGHT_PAREN) {
            es.push_back(parse_expr(context));
        }
        next();
    }

    void parse_expr_list(buffer<expr> & es, char const * context) {
        check_curr_kind(scanner::token_kind::LEFT_PAREN, context);
        next();
        parse_exprs(es, context);
    }

    // Outer loop
    bool parse_commands() {
        scan();

        // TODO(dhs): for now we will not recover from any errors
        while (true) {
            switch (curr_kind()) {
            case scanner::token_kind::LEFT_PAREN:
                parse_command();
                break;
            case scanner::token_kind::END:
                return true;
            default:
                throw_parser_exception("invalid command, '(' expected");
                break;
            }
        }
    }

    void parse_command() {
        lean_assert(curr_kind() == scanner::token_kind::LEFT_PAREN);
        next();
        check_curr_kind(scanner::token_kind::SYMBOL, "invalid command, symbol expected");
        std::string const & s = m_scanner.get_str_val();
        if (s == g_token_assert)                     parse_assert();
        else if (s == g_token_check_sat)             parse_check_sat();
        else if (s == g_token_check_sat_assuming)    parse_check_sat_assuming();
        else if (s == g_token_declare_const)         parse_declare_const();
        else if (s == g_token_declare_fun)           parse_declare_fun();
        else if (s == g_token_declare_sort)          parse_declare_sort();
        else if (s == g_token_define_fun)            parse_define_fun();
        else if (s == g_token_define_fun_rec)        parse_define_fun_rec();
        else if (s == g_token_define_funs_rec)       parse_define_funs_rec();
        else if (s == g_token_define_sort)           parse_define_sort();
        else if (s == g_token_echo)                  parse_echo();
        else if (s == g_token_exit)                  parse_exit();
        else if (s == g_token_get_assertions)        parse_get_assertions();
        else if (s == g_token_get_assignment)        parse_get_assignment();
        else if (s == g_token_get_info)              parse_get_info();
        else if (s == g_token_get_model)             parse_get_model();
        else if (s == g_token_get_option)            parse_get_option();
        else if (s == g_token_get_proof)             parse_get_proof();
        else if (s == g_token_get_unsat_assumptions) parse_get_unsat_assumptions();
        else if (s == g_token_get_unsat_core)        parse_get_unsat_core();
        else if (s == g_token_get_value)             parse_get_value();
        else if (s == g_token_pop)                   parse_pop();
        else if (s == g_token_push)                  parse_push();
        else if (s == g_token_reset)                 parse_reset();
        else if (s == g_token_reset_assertions)      parse_reset_assertions();
        else if (s == g_token_set_info)              parse_set_info();
        else if (s == g_token_set_logic)             parse_set_logic();
        else if (s == g_token_set_option)            parse_set_option();
        else throw_parser_exception(std::string("unknown command: ") + s);
    }

    // Individual commands
    void parse_assert() {
        lean_assert(curr_kind() == scanner::token_kind::SYMBOL);
        lean_assert(curr_symbol() == g_token_assert);
        next();

        type_context aux_tctx(m_env, m_ios.get_options(), m_lctx);
        expr e;
        {
            flet<type_context *> parsing_a_term(m_tctx_ptr, &aux_tctx);
            e = parse_expr("invalid assert command");
        }

        if (m_verbose)
            ios().get_regular_stream() << "[assert] " << e << "\n";

        register_hypothesis(e);

        check_curr_kind(scanner::token_kind::RIGHT_PAREN, "invalid constant declaration, ')' expected");
        next();
    }

    void parse_check_sat() {
        lean_assert(curr_kind() == scanner::token_kind::SYMBOL);
        lean_assert(curr_symbol() == g_token_check_sat);
        next();

        metavar_context mctx;
        expr goal_mvar = mctx.mk_metavar_decl(lctx(), mk_constant(get_false_name()));
        vm_obj s = to_obj(mk_tactic_state_for_metavar(env(), ios().get_options(), "check-sat", mctx, goal_mvar));

        vm_state state(env(), ios().get_options());
        scope_vm_state scope(state);
        vm_obj result = state.invoke(get_smt_prove_name(), s);
        if (optional<tactic_state> s_new = is_tactic_success(result)) {
            mctx = s_new->mctx();
            expr proof = mctx.instantiate_mvars(goal_mvar);
            if (has_expr_metavar(proof)) {
                ios().get_regular_stream() << "<tactic succeeded but left metavars>\n";
            } else {
                ios().get_regular_stream() << "unsat\n";
            }
        } else {
            ios().get_regular_stream() << "<tactic failed>\n";
        }
        check_curr_kind(scanner::token_kind::RIGHT_PAREN, "invalid constant declaration, ')' expected");
        next();
    }

    void parse_check_sat_assuming() { throw_parser_exception("check-sat-assuming not yet supported"); }
    void parse_declare_const() {
        lean_assert(curr_kind() == scanner::token_kind::SYMBOL);
        lean_assert(curr_symbol() == g_token_declare_const);
        next();
        check_curr_kind(scanner::token_kind::SYMBOL, "invalid constant declaration, symbol expected");
        symbol sym = curr_symbol();
        next();
        expr ty = parse_expr("invalid constant declaration");

        if (m_verbose)
            ios().get_regular_stream() << "[declare_const] " << sym << " : " << ty << "\n";

        register_hypothesis(sym, ty);
        check_curr_kind(scanner::token_kind::RIGHT_PAREN, "invalid constant declaration, ')' expected");
        next();
    }

    void parse_declare_fun() {
        lean_assert(curr_kind() == scanner::token_kind::SYMBOL);
        lean_assert(curr_symbol() == g_token_declare_fun);
        next();
        check_curr_kind(scanner::token_kind::SYMBOL, "invalid function declaration, symbol expected");
        symbol sym = curr_symbol();
        next();

        buffer<expr> parameter_sorts;
        parse_expr_list(parameter_sorts, "invalid function declaration");
        expr ty = parse_expr("invalid function declaration");
        for (int i = parameter_sorts.size() - 1; i >= 0; --i) {
            ty = mk_arrow(parameter_sorts[i], ty);
        }

        if (m_verbose)
            ios().get_regular_stream() << "[declare_fun] " << sym << " : " << ty << "\n";

        register_hypothesis(sym, ty);
        check_curr_kind(scanner::token_kind::RIGHT_PAREN, "invalid function declaration, ')' expected");
        next();
    }

    void parse_declare_sort() {
        lean_assert(curr_kind() == scanner::token_kind::SYMBOL);
        lean_assert(curr_symbol() == g_token_declare_sort);
        next();

        check_curr_kind(scanner::token_kind::SYMBOL, "invalid sort declaration, symbol expected");
        symbol sym = curr_symbol();
        next();
        // Note: the official standard requires the arity, but it seems to be convention to have no arity mean 0
        mpq arity;
        if (curr_kind() == scanner::token_kind::RIGHT_PAREN) {
            // no arity means 0
        } else {
            check_curr_kind(scanner::token_kind::INT, "invalid sort declaration, arity (<numeral>) expected");
            arity = curr_numeral();
            // TODO(dhs): the standard does not put a limit on the arity, but a parametric sort that takes more than ten-thousand arguments is absurd
            // (arbitrary)
            if (arity > 10000) {
                throw_parser_exception("invalid sort declaration, arities greater than 10,000 not supported");
            }
            next();
        }

        expr ty = mk_Type();
        for (unsigned i = 0; i < arity; ++i) {
            ty = mk_arrow(mk_Type(), ty);
        }

        if (m_verbose)
            ios().get_regular_stream() << "[declare_sort] " << sym << " : " << ty << "\n";

        register_hypothesis(sym, ty);
        check_curr_kind(scanner::token_kind::RIGHT_PAREN, "invalid sort declaration, ')' expected");
        next();
    }

    void parse_define_fun() { throw_parser_exception("define-fun not yet supported"); }
    void parse_define_fun_rec() { throw_parser_exception("define-fun-rec not yet supported"); }
    void parse_define_funs_rec() { throw_parser_exception("define-funs-rec not yet supported"); }
    void parse_define_sort() { throw_parser_exception("define-sort not yet supported"); }
    void parse_echo() { throw_parser_exception("echo not yet supported"); }

    void parse_exit() {
        lean_assert(curr_kind() == scanner::token_kind::SYMBOL);
        lean_assert(curr_symbol() == g_token_exit);
        next();
        check_curr_kind(scanner::token_kind::RIGHT_PAREN, "invalid exit, ')' expected");
        next();
        throw exit_exception();
    }

    void parse_get_assertions() { throw_parser_exception("get-assertions not yet supported"); }
    void parse_get_assignment() { throw_parser_exception("get-assignment not yet supported"); }
    void parse_get_info() { throw_parser_exception("get-info not yet supported"); }
    void parse_get_model() { throw_parser_exception("get-model not yet supported"); }
    void parse_get_option() { throw_parser_exception("get-option not yet supported"); }
    void parse_get_proof() { throw_parser_exception("get-proof not yet supported"); }
    void parse_get_unsat_assumptions() { throw_parser_exception("get-unsat-assumptions not yet supported"); }
    void parse_get_unsat_core() { throw_parser_exception("get-unsat-core not yet supported"); }
    void parse_get_value() { throw_parser_exception("get-value not yet supported"); }
    void parse_pop() { throw_parser_exception("pop not yet supported"); }
    void parse_push() { throw_parser_exception("push not yet supported"); }
    void parse_reset() { throw_parser_exception("reset not yet supported"); }
    void parse_reset_assertions() { throw_parser_exception("reset-assertions not yet supported"); }
    void parse_set_info() {
        lean_assert(curr_kind() == scanner::token_kind::SYMBOL);
        lean_assert(curr_symbol() == g_token_set_info);
        next();
        parse_attributes("set-info"); // only one attribute is okay
        check_curr_kind(scanner::token_kind::RIGHT_PAREN, "invalid set-info, ')' expected");
        next();
    }

    void parse_set_logic() {
        // Currently ignored (we deduce the logic automatically)
        lean_assert(curr_kind() == scanner::token_kind::SYMBOL);
        lean_assert(curr_symbol() == g_token_set_logic);
        next();
        check_curr_kind(scanner::token_kind::SYMBOL, "invalid set-logic command, symbol expected");
        symbol sym = curr_symbol();
        next();
        check_curr_kind(scanner::token_kind::RIGHT_PAREN, "invalid set-logic, ')' expected");
        next();
    }

    void parse_set_option() {
        lean_assert(curr_kind() == scanner::token_kind::SYMBOL);
        lean_assert(curr_symbol() == g_token_set_option);
        next();
        check_curr_kind(scanner::token_kind::KEYWORD, "invalid set-option command, keyword expected");
        symbol sym = curr_symbol();
        next();
        if (sym == ":use_locals") {
            m_use_locals = true;
        } else if (sym == ":verbose") {
            check_curr_kind(scanner::token_kind::SYMBOL, "invalid set-option command, option ':verbose' requires argument 'true' or 'false'");
            symbol val = curr_symbol();
            next();
            if (val == "true")
                m_verbose = true;
            else if (val == "false")
                m_verbose = false;
            else
                throw_parser_exception("invalid set-option command, option ':verbose' requires argument 'true' or 'false'");
        } else if (sym == ":lbool") {
            check_curr_kind(scanner::token_kind::SYMBOL, "invalid set-option, 'true' or 'false' expected");
            symbol tf = curr_symbol();
            next();
            bool status;
            if (tf == "true")
                status = true;
            else if (tf == "false")
                status = false;
            else
                throw_parser_exception("invalid set-option command, option ':lbool' requires next argument 'true' or 'false'");
            name n;
            while (curr_kind() == scanner::token_kind::SYMBOL) {
                symbol sym = curr_symbol();
                next();
                n = name(n, sym.c_str());
            }
            lean_assert(!n.is_anonymous());
            m_ios.set_option(n, status);
        } else if (sym == ":lnat") {
            check_curr_kind(scanner::token_kind::INT,
                            "invalid set-option, option ':lnat` "
                            "requires next argument to be a numeral");
            unsigned val = curr_numeral().get_numerator().get_unsigned_int();
            next();
            name n;
            while (curr_kind() == scanner::token_kind::SYMBOL) {
                symbol sym = curr_symbol();
                next();
                n = name(n, sym.c_str());
            }
            lean_assert(!n.is_anonymous());
            m_ios.set_option(n, val);
        } else {
            // TODO(dhs): just a warning?
            throw_parser_exception(std::string("unsupported option: ") + sym);
        }
        check_curr_kind(scanner::token_kind::RIGHT_PAREN, "invalid set-option, ')' expected");
        next();
    }

public:
    // Constructor
    parser(environment const & env, io_state & ios, std::istream & strm, char const * strm_name):
        m_env(env), m_ios(ios), m_scanner(strm, strm_name) {}

    // Entry point
    bool operator()() {
        scoped_expr_caching disable(false);

        auto mod_ldr = mk_olean_loader();
        optional<unsigned> k;
        m_env = import_modules(m_env, get_stream_name(), {{"init", k}, {"smt", k}}, mod_ldr);

        bool ok = true;
        try {
            parse_commands();
        } catch (exit_exception const & ex) {
            return ok;
        } catch (throwable const & ex) {
            ok = false;
            ::lean::message_builder(this, std::make_shared<type_context>(m_env, m_ios.get_options(), m_lctx),
                                    m_env, m_ios, get_file_name(), get_some_pos(), ERROR)
                    .set_exception(ex).report();
        }
        return ok;
    }
};

// Setup and teardown

void initialize_parser() {
    g_smt2_unique_prefix = new name(name::mk_internal_unique_name());
}

void finalize_parser() {
    delete g_smt2_unique_prefix;
}

// Entry point
bool parse_commands(environment & env, io_state & ios, char const * fname) {
    std::ifstream in(fname);
    if (in.bad() || in.fail())
        throw exception(sstream() << "failed to open file '" << fname << "'");

    parser p(env, ios, in, fname);
    return p();
}

}}
