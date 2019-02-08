/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <iostream>
#include <limits>
#include <string>
#include "runtime/utf8.h"
#include "runtime/apply.h"
#include "kernel/instantiate.h"
#include "library/module.h"
#include "library/compiler/llnf.h"
#include "library/compiler/name_mangling.h"
#include "library/compiler/emit_cpp.h"
#include "library/compiler/builtin.h"
#include "library/compiler/extname.h"

namespace lean {
struct emit_cpp_ext : public environment_extension {
    comp_decls m_code;
};

struct emit_cpp_ext_reg {
    unsigned m_ext_id;
    emit_cpp_ext_reg() { m_ext_id = environment::register_extension(std::make_shared<emit_cpp_ext>()); }
};

static emit_cpp_ext_reg * g_ext = nullptr;
static emit_cpp_ext const & get_extension(environment const & env) {
    return static_cast<emit_cpp_ext const &>(env.get_extension(g_ext->m_ext_id));
}
static environment update(environment const & env, emit_cpp_ext const & ext) {
    return env.update(g_ext->m_ext_id, std::make_shared<emit_cpp_ext>(ext));
}

environment emit_cpp(environment const & env, comp_decls const & ds) {
    /* Remark: we don't generate C++ code here, but at `print_cpp_code`. In this function
       we simply save the LLNF expression in the emit_cpp_ext. */
    emit_cpp_ext ext = get_extension(env);
    ext.m_code = append(ext.m_code, ds);
    return update(env, ext);
}

static std::string to_cpp_type(expr const & e) {
    if (is_constant(e)) {
        if (e == mk_enf_object_type() || e == mk_enf_neutral_type()) {
            return "obj*";
        } else if (const_name(e) == get_uint8_name()) {
            return "uint8";
        } else if (const_name(e) == get_uint16_name()) {
            return "uint16";
        } else if (const_name(e) == get_uint32_name()) {
            return "uint32";
        } else if (const_name(e) == get_uint64_name()) {
            return "uint64";
        } else if (const_name(e) == get_usize_name()) {
            return "usize";
        }
    } else if (is_pi(e)) {
        return "obj*";
    }
    throw exception("unknown type");
}

static void open_namespaces_core(std::ostream & out, name const & p) {
    if (p.is_anonymous()) return;
    open_namespaces_core(out, p.get_prefix());
    lean_assert(p.is_string());
    out << "namespace " << p.get_string().to_std_string() << " {\n";
}

/* If `n` has the attribute [cppname], and the "cppname" is hierarchical, then
   we must put `n` code inside of a namespace. */
static void open_namespaces_for(std::ostream & out, environment const & env, name const & n) {
    optional<name> c = get_extname_for(env, n);
    if (!c || c->is_atomic()) return;
    open_namespaces_core(out, c->get_prefix());
}

static void close_namespaces_for(std::ostream & out, environment const & env, name const & n) {
    optional<name> c = get_extname_for(env, n);
    if (!c || c->is_atomic()) return;
    name p = c->get_prefix();
    while (!p.is_anonymous()) {
        out << "}";
        p = p.get_prefix();
    }
    out << "\n";
}

static char const * g_lean_main = "_lean_main";

static std::string to_base_cpp_name(environment const & env, name const & n) {
    if (optional<name> c = get_extname_for(env, n)) {
        lean_assert(c->is_string());
        if (*c == "main")
            return g_lean_main;
        else
            return c->get_string().to_std_string();
    } else if (n == "main") {
        return g_lean_main;
    } else {
        return mangle(n);
    }
}

static std::string to_cpp_name(environment const & env, name const & n) {
    if (optional<name> c = get_extname_for(env, n)) {
        lean_assert(c->is_string());
        if (*c == "main")
            return g_lean_main;
        else
            return c->to_string("::");
    } else if (n == "main") {
        return g_lean_main;
    } else {
        return mangle(n);
    }
}

static std::string to_cpp_init_name(environment const & env, name const & n) {
    if (optional<name> c = get_extname_for(env, n)) {
        name init_c(c->get_prefix(), (std::string("_init_") + c->get_string().to_std_string()).c_str());
        return init_c.to_string("::");
    } else {
        return std::string("_init_") + mangle(n);
    }
}

static expr get_result_type(expr type) {
    while (is_pi(type)) {
        type = binding_body(type);
    }
    return type;
}

static void emit_fn_decl(std::ostream & out, environment const & env, name const & n, bool mod_decl) {
    open_namespaces_for(out, env, n);
    expr type = get_constant_ll_type(env, n);
    if (!mod_decl && !is_pi(type)) {
        /* We should add extern for constants coming from other modules. */
        out << "extern ";
    }
    out << to_cpp_type(get_result_type(type)) << " " << to_base_cpp_name(env, n);
    if (is_pi(type)) {
        out << "(";
        bool first = true;
        while (is_pi(type)) {
            if (first) first = false; else out << ", ";
            out << to_cpp_type(binding_domain(type));
            type = binding_body(type);
        }
        out << ")";
    }
    out << ";\n";
    close_namespaces_for(out, env, n);
}

/* Auxiliary function for `collect_dependencies`. */
static void collect_constant(environment const &env, expr const & e, name_set & deps) {
    lean_assert(is_constant(e));
    if (!is_llnf_op(e) && !is_native_constant(env, const_name(e)) && !is_enf_neutral(e) && !is_enf_unreachable(e)) {
        deps.insert(const_name(e));
    }
}

/* Collect declarations used by `e` in `deps`. */
static void collect_dependencies(environment const & env, expr e, name_set & deps) {
    while (true) {
        switch (e.kind()) {
        case expr_kind::Lambda:
            e = binding_body(e);
            break;
        case expr_kind::Let:
            collect_dependencies(env, let_value(e), deps);
            e = let_body(e);
            break;
        case expr_kind::App:
            if (is_cases_on_app(env, e)) {
                buffer<expr> args;
                get_app_args(e, args);
                for (expr const & arg : args)
                    collect_dependencies(env, arg, deps);
            } else if (is_llnf_closure(get_app_fn(e))) {
                buffer<expr> args;
                get_app_args(e, args);
                collect_constant(env, args[0], deps);
            } else {
                collect_constant(env, get_app_fn(e), deps);
            }
            return;
        case expr_kind::Const:
            collect_constant(env, e, deps);
            return;
        default:
            return;
        }
    }
}

/* Emit C++ function declaration for all functions/constants declared in the current module,
   and their direct dependencies. */
static void emit_fn_decls(std::ostream & out, environment const & env) {
    comp_decls ds = get_extension(env).m_code;
    name_set mod_decls;
    name_set all_decls;
    for (comp_decl const & d : ds) {
        mod_decls.insert(d.fst());
        all_decls.insert(d.fst());
        collect_dependencies(env, d.snd(), all_decls);
    }
    for_each_native_constant(env, [&](const name &n) {
        if (!is_builtin_constant(n))
            mod_decls.insert(n);
            all_decls.insert(n);
    });
    all_decls.for_each([&](name const & n) {
            emit_fn_decl(out, env, n, mod_decls.contains(n));
    });
}

static optional<comp_decl> has_main_fn(environment const & env) {
    comp_decls ds = get_extension(env).m_code;
    for (comp_decl const & d : ds) {
        name const & n    = d.fst();
        if (n == "main") return optional<comp_decl>(d);
        if (optional<name> e = get_extname_for(env, n)) {
            if (*e == "main") return optional<comp_decl>(d);
        }
    }
    return optional<comp_decl>();
}

static void emit_file_header(std::ostream & out, environment const & env, module_name const & m, list<module_name> const & deps) {
    out << "// Lean compiler output\n";
    out << "// Module: " << m << "\n";
    out << "// Imports:"; for (module_name const & d : deps) out << " " << d; out << "\n";
    out << "#include \"runtime/object.h\"\n";
    out << "#include \"runtime/apply.h\"\n";
    out << "#include \"runtime/io.h\"\n";
    if (has_main_fn(env))
        out << "#include \"runtime/init_module.h\"\n";
    out << "#include \"kernel/builtin.h\"\n";
    out << "typedef lean::object obj;    typedef lean::usize  usize;\n";
    out << "typedef lean::uint8  uint8;  typedef lean::uint16 uint16;\n";
    out << "typedef lean::uint32 uint32; typedef lean::uint64 uint64;\n";
    out << "#if defined(__clang__)\n";
    out << "#pragma clang diagnostic ignored \"-Wunused-parameter\"\n";
    out << "#pragma clang diagnostic ignored \"-Wunused-label\"\n";
    out << "#elif defined(__GNUC__) && !defined(__CLANG__)\n";
    out << "#pragma GCC diagnostic ignored \"-Wunused-parameter\"\n";
    out << "#pragma GCC diagnostic ignored \"-Wunused-label\"\n";
    out << "#pragma GCC diagnostic ignored \"-Wunused-but-set-variable\"\n";
    out << "#endif\n";
}

static void emit_hexdigit(std::ostream & out, unsigned char c) {
    lean_assert(c < 16);
    if (c < 10) {
        out << static_cast<char>('0' + c);
    } else {
        out << static_cast<char>('a' + (c - 10));
    }
}

static void emit_quoted_string(std::ostream & out, std::string const & s) {
    for (unsigned i = 0; i < s.size(); i++) {
        unsigned char c = s[i];
        if (c == '\n') {
            out << "\\n";
        } else if (c ==  '\t') {
            out << "\\t";
        } else if (c == '\\') {
            out << "\\\\";
        } else if (c == '\"') {
            out << "\\\"";
        } else if (c <= 31 || c >= 0x7f) {
            out << "\\x"; emit_hexdigit(out, c / 16); emit_hexdigit(out, c % 16);
        } else {
            out << c;
        }
    }
}

static char const * get_scalar_type_from_size(unsigned i) {
    switch (i) {
    case 1: return "uint8";
    case 2: return "uint16";
    case 4: return "uint32";
    case 8: return "uint64";
    default: throw exception("C++ code generation failed, invalid scalar size");
    }
}

struct emit_fn_fn {
    std::ostream &  m_out;
    name_generator  m_ngen;
    environment     m_env;
    local_ctx       m_lctx;
    name_map<exprs> m_jp_vars;
    name            m_fn_name;
    buffer<expr>    m_fn_args;

    static bool is_jmp(expr const & e) {
        return is_llnf_jmp(get_app_fn(e));
    }

    bool is_obj(expr const & x) {
        lean_assert(is_fvar(x));
        return m_lctx.get_local_decl(x).get_type() == mk_enf_object_type();
    }

    void emit_unit() {
        m_out << "lean::box(0)";
    }

    void emit_constant(expr const & c) {
        lean_assert(is_constant(c));
        lean_assert(!is_enf_unreachable(c));
        if (optional<name> n = get_native_constant_cname(m_env, const_name(c)))
            m_out << *n;
        else if (is_enf_neutral(c))
            emit_unit();
        else
            m_out << to_cpp_name(m_env, const_name(c));
    }

    void emit_fvar(expr const & x) {
        lean_assert(is_fvar(x));
        name const & id = fvar_name(x);
        lean_assert(id.is_numeral());
        m_out << "x_" << id.get_numeral();
    }

    void emit_lbl(expr const & jp) {
        lean_assert(is_fvar(jp));
        name const & id = fvar_name(jp);
        lean_assert(id.is_numeral());
        m_out << "lbl_" << id.get_numeral();
    }

    /* Emit instructions that return void. */
    void emit_instr(expr const & e) {
        expr const & f = get_app_fn(e);
        lean_assert(is_llnf_inc(f) || is_llnf_dec(f));
        if (is_llnf_inc(f)) {
            m_out << "lean::inc(";
        } else {
            m_out << "lean::dec(";
        }
        emit_fvar(app_arg(e));
        m_out << ");\n";
    }

    void emit_lhs(expr const & x) {
        emit_fvar(x); m_out << " = ";
    }

    void emit_lit(expr const & x, expr const & v) {
        lean_assert(is_lit(v));
        emit_lhs(x);
        literal const & l = lit_value(v);
        switch (l.kind()) {
        case literal_kind::Nat:
            if (is_obj(x)) {
                if (l.get_nat() < std::numeric_limits<unsigned>::max()) {
                    m_out << "lean::mk_nat_obj(" << l.get_nat() << "u)";
                } else {
                    m_out << "lean::mk_nat_obj(lean::mpz(\"" << l.get_nat() << "\"))";
                }
            } else {
                m_out << l.get_nat();
            }
            break;
        case literal_kind::String:
            m_out << "lean::mk_string(\"";
            emit_quoted_string(m_out, l.get_string().to_std_string());
            m_out << "\")";
            break;
        }
        m_out << ";\n";
    }

    void emit_arg(expr const & arg) {
        if (is_fvar(arg))
            emit_fvar(arg);
        else
            emit_unit();
    }

    void emit_args(unsigned sz, expr const * args) {
        for (unsigned i = 0; i < sz; i++) {
            if (i > 0) m_out << ", ";
            emit_arg(args[i]);
        }
    }

    void emit_apply(expr const & x, buffer<expr> const & args) {
        lean_assert(args.size() > 0);
        expr const & f = args[0];
        unsigned nargs = args.size() - 1;
        if (nargs > LEAN_CLOSURE_MAX_ARGS) {
            m_out << "{ obj* _aargs[] = {";
            emit_args(nargs, args.data()+1);
            m_out << "}; ";
            emit_lhs(x);
            m_out << "lean::apply_m("; emit_fvar(f); m_out << ", " << nargs << ", _aargs); }\n";
        } else {
            emit_lhs(x);
            m_out << "lean::apply_" << nargs << "(";
            emit_fvar(f);
            m_out << ", ";
            emit_args(nargs, args.data()+1);
            m_out << ");\n";
        }
    }

    void emit_closure(expr const & x, buffer<expr> const & args) {
        lean_assert(!args.empty());
        expr const & fn = args[0];
        lean_assert(is_constant(fn));
        unsigned arity = get_llnf_arity(m_env, const_name(fn));
        emit_lhs(x);
        m_out << "lean::alloc_closure(reinterpret_cast<void*>("; emit_constant(fn); m_out << "), " << arity << ", " << (args.size()-1) << ");\n";
        for (unsigned i = 1; i < args.size(); i++) {
            m_out << "lean::closure_set("; emit_fvar(x); m_out << ", " << (i-1) << ", "; emit_arg(args[i]); m_out << ");\n";
        }
    }

    void emit_cnstr_scalar_size(unsigned num_usizes, unsigned num_bytes) {
        if (num_usizes == 0)
            m_out << num_bytes;
        else if (num_bytes == 0)
            m_out << "sizeof(size_t)*" << num_usizes;
        else
            m_out << "sizeof(size_t)*" << num_usizes << " + " << num_bytes;
    }

    void emit_alloc_cnstr(expr const & x, unsigned cidx, unsigned num_objs, unsigned num_usizes, unsigned num_bytes) {
        emit_lhs(x);
        m_out << "lean::alloc_cnstr(" << cidx << ", " << num_objs << ", ";
        emit_cnstr_scalar_size(num_usizes, num_bytes); m_out << ");\n";
    }

    void emit_cnstr_sets(expr const & x, unsigned sz, expr const * args) {
        for (unsigned i = 0; i < sz; i++) {
            m_out << "lean::cnstr_set("; emit_fvar(x); m_out << ", " << i << ", "; emit_arg(args[i]); m_out << ");\n";
        }
    }

    void emit_cnstr(expr const & x, expr const & fn, buffer<expr> const & args) {
        unsigned cidx, num_usizes, num_bytes;
        lean_verify(is_llnf_cnstr(fn, cidx, num_usizes, num_bytes));
        if (num_usizes == 0 && num_bytes == 0 && args.size() == 0) {
            emit_lhs(x); m_out << "lean::box(" << cidx << ");\n";
        } else {
            emit_alloc_cnstr(x, cidx, args.size(), num_usizes, num_bytes);
            emit_cnstr_sets(x, args.size(), args.data());
        }
    }

    void emit_reset(expr const & x, expr const & fn, expr const & o) {
        unsigned n;
        lean_verify(is_llnf_reset(fn, n));
        m_out << "if (lean::is_shared("; emit_fvar(o); m_out <<")) {\n";
        m_out << " lean::dec("; emit_fvar(o); m_out << ");\n ";
        emit_lhs(x); emit_unit(); m_out << ";\n";
        m_out << "} else {\n";
        for (unsigned i = 0; i < n; i++) {
            m_out << " lean::cnstr_release("; emit_fvar(o); m_out << ", " << i << ");\n";
        }
        m_out << " "; emit_lhs(x); emit_fvar(o); m_out << ";\n";
        m_out << "}\n";
    }

    void emit_reuse(expr const & x, expr const & fn, buffer<expr> const & args) {
        lean_assert(!args.empty());
        unsigned cidx, num_usizes, num_bytes;
        bool updt_cidx;
        lean_verify(is_llnf_reuse(fn, cidx, num_usizes, num_bytes, updt_cidx));
        expr const & o = args[0];
        m_out << "if (lean::is_scalar("; emit_fvar(o); m_out <<")) {\n";
        m_out << " "; emit_alloc_cnstr(x, cidx, args.size()-1, num_usizes, num_bytes);
        m_out << "} else {\n";
        m_out << " "; emit_lhs(x); emit_fvar(o); m_out << ";\n";
        if (updt_cidx) {
            m_out << " lean::cnstr_set_tag("; emit_fvar(o); m_out << ", " << cidx << ");\n";
        }
        m_out << "}\n";
        emit_cnstr_sets(x, args.size()-1, args.data()+1);
    }

    void emit_offset(unsigned n, unsigned offset) {
        if (n > 0) {
            m_out << "sizeof(void*)*" << n;
            if (offset > 0)
                m_out << " + " << offset;
        } else {
            m_out << offset;
        }
    }

    void emit_sset(expr const & x, expr const & fn, buffer<expr> const & args) {
        lean_assert(args.size() == 2);
        unsigned sz, n, offset;
        lean_verify(is_llnf_sset(fn, sz, n, offset));
        m_out << "lean::cnstr_set_scalar("; emit_fvar(args[0]); m_out << ", "; emit_offset(n, offset); m_out << ", "; emit_fvar(args[1]); m_out << ");\n";
        emit_lhs(x); emit_fvar(args[0]); m_out << ";\n";
    }

    void emit_uset(expr const & x, expr const & fn, buffer<expr> const & args) {
        unsigned n;
        lean_verify(is_llnf_uset(fn, n));
        m_out << "lean::cnstr_set_scalar("; emit_fvar(args[0]); m_out << ", "; emit_offset(n, 0); m_out << ", "; emit_fvar(args[1]); m_out << ");\n";
        emit_lhs(x); emit_fvar(args[0]); m_out << ";\n";
    }

    void emit_proj(expr const & x, expr const & fn, expr const & o) {
        unsigned i;
        lean_verify(is_llnf_proj(fn, i));
        emit_lhs(x);
        m_out << "lean::cnstr_get("; emit_fvar(o); m_out << ", " << i << ");\n";
    }

    void emit_sproj(expr const & x, expr const & fn, expr const & o) {
        unsigned sz, n, offset;
        lean_verify(is_llnf_sproj(fn, sz, n, offset));
        emit_lhs(x);
        m_out << "lean::cnstr_get_scalar<" << get_scalar_type_from_size(sz) << ">("; emit_fvar(o); m_out << ", "; emit_offset(n, offset); m_out << ");\n";
    }

    void emit_uproj(expr const & x, expr const & fn, expr const & o) {
        unsigned n;
        lean_verify(is_llnf_uproj(fn, n));
        emit_lhs(x);
        m_out << "lean::cnstr_get_scalar<usize>("; emit_fvar(o); m_out << ", sizeof(void*)*" << n << ");\n";
    }

    void emit_unbox(expr const & x, expr const & fn, expr const & arg) {
        unsigned n;
        lean_verify(is_llnf_unbox(fn, n));
        emit_lhs(x);
        switch (n) {
        case 0:  m_out << "lean::unbox_size_t("; break;
        case 4:  m_out << "lean::unbox_uint32("; break;
        case 8:  m_out << "lean::unbox_uint64("; break;
        default: m_out << "lean::unbox(";        break; // default case for scalars that fit in tagged pointers in all platforms
        }
        emit_fvar(arg);
        m_out << ");\n";
    }

    void emit_box(expr const & x, expr const & fn, expr const & arg) {
        unsigned n;
        lean_verify(is_llnf_box(fn, n));
        emit_lhs(x);
        switch (n) {
        case 0:  m_out << "lean::box_size_t("; break;
        case 4:  m_out << "lean::box_uint32("; break;
        case 8:  m_out << "lean::box_uint64("; break;
        default: m_out << "lean::box(";        break; // default case for scalars that fit in tagged pointers in all platforms
        }
        emit_fvar(arg);
        m_out << ");\n";
    }

    void emit_native_constant(expr const &x, expr const &fn, buffer<expr> const &args) {
        buffer<bool> used_args;
        lean_verify(get_native_used_args(m_env, const_name(fn), used_args));
        lean_assert(used_args.size() == args.size());
        emit_lhs(x);
        emit_constant(fn);
        m_out << "(";
        bool first = true;
        for (unsigned i = 0; i < args.size(); i++) {
            if (used_args[i]) {
                if (first) first = false; else m_out << ", ";
                emit_arg(args[i]);
            }
        }
        m_out << ");\n";
    }

    void emit_instr(local_decl const & d) {
        expr x = d.mk_ref();
        expr val = *d.get_value();
        if (is_lit(val)) {
            emit_lit(x, val);
        } else if (is_constant(val)) {
            if (is_llnf_cnstr(val)) {
                buffer<expr> args;
                emit_cnstr(x, val, args);
            } else if (is_enf_unreachable(val)) {
                m_out << "lean_unreachable();\n";
                emit_lhs(x); emit_unit(); m_out << ";\n";
            } else {
                emit_lhs(x); emit_constant(val); m_out << ";\n";
            }
        } else if (is_app(val)) {
            buffer<expr> args;
            expr const & fn = get_app_args(val, args);
            lean_assert(is_constant(fn));
            if (is_llnf_cnstr(fn)) {
                emit_cnstr(x, fn, args);
            } else if (is_llnf_apply(fn)) {
                emit_apply(x, args);
            } else if (is_llnf_closure(fn)) {
                emit_closure(x, args);
            } else if (is_llnf_reuse(fn)) {
                emit_reuse(x, fn, args);
            } else if (is_llnf_reset(fn)) {
                emit_reset(x, fn, args[0]);
            } else if (is_llnf_sset(fn)) {
                emit_sset(x, fn, args);
            } else if (is_llnf_uset(fn)) {
                emit_uset(x, fn, args);
            } else if (is_llnf_proj(fn)) {
                emit_proj(x, fn, args[0]);
            } else if (is_llnf_sproj(fn)) {
                emit_sproj(x, fn, args[0]);
            } else if (is_llnf_uproj(fn)) {
                emit_uproj(x, fn, args[0]);
            } else if (is_llnf_unbox(fn)) {
                emit_unbox(x, fn, args[0]);
            } else if (is_llnf_box(fn)) {
                emit_box(x, fn, args[0]);
            } else if (is_native_constant(m_env, const_name(fn))) {
                emit_native_constant(x, fn, args);
            } else {
                /* Regular function application. */
                emit_lhs(x);
                emit_constant(fn);
                m_out << "(";
                emit_args(args.size(), args.data());
                m_out << ");\n";
            }
        } else {
            lean_assert(!is_fvar(val));
            lean_unreachable();
        }
    }

    void emit_cases(expr const & e) {
        lean_assert(is_cases_on_app(m_env, e));
        buffer<expr> args;
        get_app_args(e, args);
        expr const & x = args[0];
        if (args.size() == 3) {
            // use if-statement
            if (is_obj(x)) {
                m_out << "if (lean::obj_tag("; emit_fvar(x); m_out << ") == 0)\n";
            } else {
                m_out << "if ("; emit_fvar(x); m_out << " == 0)\n";
            }
            emit(args[1]);
            m_out << "else\n";
            emit(args[2]);
        } else {
            if (is_obj(x)) {
                m_out << "switch (lean::obj_tag("; emit_fvar(x); m_out << ")) {\n";
            } else {
                m_out << "switch ("; emit_fvar(x); m_out << ") {\n";
            }
            for (unsigned i = 1; i < args.size(); i++) {
                if (i == args.size() - 1)
                    m_out << "default:\n";
                else
                    m_out << "case " << (i-1) << ":\n";
                emit(args[i]);
            }
            m_out << "}\n";
        }
    }

    void emit_jmp(expr const & e) {
        lean_assert(is_jmp(e));
        buffer<expr> args;
        get_app_args(e, args);
        expr const & jp = args[0];
        lean_assert(is_fvar(jp));
        lean_assert(m_jp_vars.contains(fvar_name(jp)));
        exprs params = *m_jp_vars.find(fvar_name(jp));
        lean_assert(length(params) == args.size() - 1);
        for (unsigned i = 1; i < args.size(); i++) {
            emit_fvar(head(params)); m_out << " = "; emit_fvar(args[i]); m_out << ";\n";
            params = tail(params);
        }
        m_out << "goto "; emit_lbl(jp); m_out << ";\n";
    }

    optional<expr> is_self_call(expr const & val) {
        expr fn  = get_app_fn(val);
        if (is_constant(fn) && const_name(fn) == m_fn_name)
            return some_expr(val);
        else
            return none_expr();
    }

    void emit_tail_call(expr const & e) {
        buffer<expr> args;
        expr fn = get_app_args(e, args);
        lean_assert(is_constant(fn) && const_name(fn) == m_fn_name);
        lean_assert(args.size() == m_fn_args.size());
        for (unsigned i = 0; i < args.size(); i++) {
            if (args[i] != m_fn_args[i]) {
                emit_fvar(m_fn_args[i]); m_out << " = "; emit_fvar(args[i]); m_out << ";\n";
            }
        }
        m_out << "goto _start;\n";
    }

    void emit_terminal(expr const & e, bool tail_call) {
        if (is_cases_on_app(m_env, e)) {
            emit_cases(e);
        } else if (is_jmp(e)) {
            emit_jmp(e);
        } else if (tail_call) {
            emit_tail_call(*m_lctx.get_local_decl(e).get_value());
        } else if (is_fvar(e)) {
            m_out << "return "; emit_fvar(e); m_out << ";\n";
        } else {
            lean_unreachable();
        }
    }

    void emit(expr e) {
        m_out << "{\n";
        buffer<expr> jps;
        buffer<expr> locals;
        buffer<expr> instrs;
        bool declared_vars = false;
        bool tail_call = false;
        while (is_let(e)) {
            expr v = instantiate_rev(let_value(e), locals.size(), locals.data());
            if (is_join_point_name(let_name(e))) {
                buffer<expr> jp_vars;
                while (is_lambda(v)) {
                    expr y = m_lctx.mk_local_decl(m_ngen, binding_name(v), binding_domain(v));
                    jp_vars.push_back(y);
                    /* Declare join point parameter, we need them to implement join point calls in this block. */
                    m_out << to_cpp_type(binding_domain(v)) << " "; emit_fvar(y); m_out << "; ";
                    declared_vars = true;
                    v = binding_body(v);
                }
                v = instantiate_rev(v, jp_vars.size(), jp_vars.data());
                expr x = m_lctx.mk_local_decl(m_ngen, let_name(e), let_type(e), v);
                locals.push_back(x);
                jps.push_back(x);
                m_jp_vars.insert(fvar_name(x), to_list_ref(jp_vars));
            } else {
                expr x = m_lctx.mk_local_decl(m_ngen, let_name(e), let_type(e), v);
                locals.push_back(x);
                if (is_bvar(let_body(e), 0) && is_self_call(v)) {
                    /* Ignore tail call, we will emit it at emit_terminal as a `goto`. */
                    tail_call = true;
                } else {
                    if (!is_llnf_void_type(let_type(e))) {
                        /* Declare local variable.
                           Remark: variables of type `_void` are used to store instructions that do
                           not return any value.  */
                        m_out << to_cpp_type(let_type(e)) << " "; emit_fvar(x); m_out << "; ";
                        declared_vars = true;
                    }
                    instrs.push_back(x);
                }
            }
            e = let_body(e);
        }
        e = instantiate_rev(e, locals.size(), locals.data());
        if (declared_vars)
            m_out << "\n";
        /* emit instructions */
        for (expr const & x : instrs) {
            local_decl d = m_lctx.get_local_decl(x);
            if (is_llnf_void_type(d.get_type())) {
                emit_instr(*d.get_value());
            } else {
                emit_instr(d);
            }
        }
        emit_terminal(e, tail_call);
        for (expr const & jp : jps) {
            emit_lbl(jp); m_out << ":\n";
            emit(*m_lctx.get_local_decl(jp).get_value());
        }
        m_out << "}\n";
    }

public:
    emit_fn_fn(std::ostream & out, environment const & env):
        m_out(out), m_env(env) {
    }

    void operator()(comp_decl const & d) {
        name n    = d.fst();
        expr e    = d.snd();
        m_fn_name = n;
        expr type = get_constant_ll_type(m_env, n);
        m_out << to_cpp_type(get_result_type(type)) << " ";
        if (is_lambda(e)) {
            m_out << to_base_cpp_name(m_env, n);
            m_out << "(";
            bool first = true;
            while (is_lambda(e)) {
                if (first) first = false; else m_out << ", ";
                expr x = m_lctx.mk_local_decl(m_ngen, binding_name(e), binding_domain(e));
                m_fn_args.push_back(x);
                m_out << to_cpp_type(binding_domain(e));
                m_out << " ";
                emit_fvar(x);
                e = binding_body(e);
            }
            m_out << ")";
            e = instantiate_rev(e, m_fn_args.size(), m_fn_args.data());
        } else {
            m_out << "_init_" << to_base_cpp_name(m_env, n) << "()";
        }
        m_out << " {\n";
        m_out << "_start:\n";
        emit(e);
        m_out << "}\n";
    }
};

static void emit_fn(std::ostream & out, environment const & env, comp_decl const & d) {
    name const & n = d.fst();
    expr code = d.snd();
    open_namespaces_for(out, env, n);
    emit_fn_fn(out, env)(d);
    close_namespaces_for(out, env, n);
}

static void emit_fns(std::ostream & out, environment const & env) {
    comp_decls ds = get_extension(env).m_code;
    for (comp_decl const & d : ds) {
        emit_fn(out, env, d);
    }
}

static void emit_initialize(std::ostream & out, environment const & env, module_name const & m, list<module_name> const & deps) {
    for (module_name const & d : deps) {
        out << "void initialize_" << mangle(d, false) << "();\n";
    }
    out << "static bool _G_initialized = false;\n";
    out << "void initialize_" << mangle(m, false) << "() {\n";
    out << " if (_G_initialized) return;\n";
    out << " _G_initialized = true;\n";
    for (module_name const & d : deps) {
        out << " initialize_" << mangle(d, false) << "();\n";
    }
    comp_decls ds = get_extension(env).m_code;
    for (comp_decl const & d : ds) {
        name const & n    = d.fst();
        expr const & code = d.snd();
        if (!is_lambda(code)) {
            out << " " << to_cpp_name(env, n) << " = " << to_cpp_init_name(env, n) << "();\n";
        }
    }
    out << "}\n";
}

static void emit_main_fn(std::ostream & out, module_name const & m, comp_decl const & d) {
    if (get_num_nested_lambdas(d.snd()) != 2) {
        throw exception("invalid main function, incorrect arity when generating code");
    }
    out << "int main(int argc, char ** argv) {\n";
    out << "lean::initialize_runtime_module();\n";
    out << "initialize_" << mangle(m, false) << "();\n";
    out << "obj* in = lean::box(0);\n";
    out << "int i = argc;\n";
    out << "while (i > 1) {\n i--;\n";
    out << " obj* n = lean::alloc_cnstr(1,2,0); lean::cnstr_set(n, 0, lean::mk_string(argv[i])); lean::cnstr_set(n, 1, in);\n";
    out << " in = n;\n";
    out << "}\n";
    out << "obj * r = " << g_lean_main << "(in, lean::box(0));\n";
    out << "int ret = lean::unbox(lean::cnstr_get(r, 0));\n";
    out << "lean::dec(r);\n";
    out << "return ret;\n";
    out << "}\n";
}

void print_cpp_code(std::ostream & out, environment const & env, module_name const & m, list<module_name> const & deps) {
    emit_file_header(out, env, m, deps);
    emit_fn_decls(out, env);
    emit_fns(out, env);
    emit_initialize(out, env, m, deps);
    if (optional<comp_decl> d = has_main_fn(env)) emit_main_fn(out, m, *d);
}

void initialize_emit_cpp() {
    g_ext = new emit_cpp_ext_reg();
}

void finalize_emit_cpp() {
    delete g_ext;
}
}
