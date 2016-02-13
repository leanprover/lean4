/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <limits>
#include <utility>
#include "util/pair.h"
#include "library/attribute_manager.h"
#include "frontends/lean/token_table.h"

namespace lean {
static unsigned g_arrow_prec      = 25;
static unsigned g_decreasing_prec = 100;
static unsigned g_max_prec        = 1024;
static unsigned g_Max_prec        = 1024*1024;
static unsigned g_plus_prec       = 65;
static unsigned g_cup_prec        = 60;
unsigned get_max_prec() { return g_max_prec; }
unsigned get_Max_prec() { return g_Max_prec; }
unsigned get_arrow_prec() { return g_arrow_prec; }
unsigned get_decreasing_prec() { return g_decreasing_prec; }
static token_table update(token_table const & s, char const * token, char const * val,
                          optional<unsigned> expr_prec, optional<unsigned> tac_prec) {
    lean_assert(expr_prec || tac_prec);
    token_info info(token, val, 0, 0);
    if (token_info const * old_info = find(s, token)) {
        info = info.update_expr_precedence(old_info->expr_precedence());
        info = info.update_tactic_precedence(old_info->tactic_precedence());
    }
    if (expr_prec)
        info = info.update_expr_precedence(*expr_prec);
    if (tac_prec)
        info = info.update_tactic_precedence(*tac_prec);
    return insert(s, token, info);
}
token_table add_command_token(token_table const & s, char const * token) {
    return insert(s, token, token_info(token));
}
token_table add_command_token(token_table const & s, char const * token, char const * val) {
    return insert(s, token, token_info(token, val));
}
token_table add_token(token_table const & s, char const * token, unsigned prec) {
    return update(s, token, token, optional<unsigned>(prec), optional<unsigned>());
}
token_table add_token(token_table const & s, char const * token, char const * val, unsigned prec) {
    return update(s, token, val, optional<unsigned>(prec), optional<unsigned>());
}
token_table add_tactic_token(token_table const & s, char const * token, unsigned prec) {
    return update(s, token, token, optional<unsigned>(), optional<unsigned>(prec));
}
token_table add_tactic_token(token_table const & s, char const * token, char const * val, unsigned prec) {
    return update(s, token, val, optional<unsigned>(), optional<unsigned>(prec));
}
token_table const * find(token_table const & s, char c) {
    return s.find(c);
}
token_info const * value_of(token_table const & s) {
    return s.value();
}
optional<unsigned> get_expr_precedence(token_table const & s, char const * token) {
    auto it = find(s, token);
    return it ? optional<unsigned>(it->expr_precedence()) : optional<unsigned>();
}
optional<unsigned> get_tactic_precedence(token_table const & s, char const * token) {
    auto it = find(s, token);
    return it ? optional<unsigned>(it->tactic_precedence()) : optional<unsigned>();
}
bool is_token(token_table const & s, char const * token) {
    return static_cast<bool>(find(s, token));
}
void for_each(token_table const & s, std::function<void(char const *, token_info const &)> const & fn) {
    s.for_each([&](unsigned num, char const * keys, token_info const & info) {
            buffer<char> str;
            str.append(num, keys);
            str.push_back(0);
            fn(str.data(), info);
        });
}

static char const * g_lambda_unicode     = "\u03BB";
static char const * g_pi_unicode         = "\u03A0";
static char const * g_forall_unicode     = "\u2200";
static char const * g_arrow_unicode      = "\u2192";
static char const * g_cup                = "\u2294";
static char const * g_qed_unicode        = "∎";
static char const * g_decreasing_unicode = "↓";

void init_token_table(token_table & t) {
    pair<char const *, unsigned> builtin[] =
        {{"fun", 0}, {"Pi", 0}, {"let", 0}, {"in", 0}, {"at", 0}, {"have", 0}, {"assert", 0}, {"suppose", 0}, {"show", 0}, {"suffices", 0}, {"obtain", 0},
         {"if", 0}, {"then", 0}, {"else", 0}, {"by", 0}, {"by+", 0}, {"hiding", 0}, {"replacing", 0}, {"renaming", 0},
         {"from", 0}, {"(", g_max_prec}, {")", 0}, {"{", g_max_prec}, {"}", 0}, {"_", g_max_prec},
         {"[", g_max_prec}, {"]", 0}, {"⦃", g_max_prec}, {"⦄", 0}, {".{", 0}, {"Type", g_max_prec},
         {"{|", g_max_prec}, {"|}", 0}, {"(:", g_max_prec}, {":)", 0},
         {"⊢", 0}, {"⟨", g_max_prec}, {"⟩", 0}, {"^", 0}, {"↑", 0}, {"▸", 0},
         {"using", 0}, {"|", 0}, {"!", g_max_prec}, {"?", 0},  {"with", 0}, {"...", 0}, {",", 0},
         {".", 0}, {":", 0}, {"::", 0}, {"calc", 0}, {"rewrite", 0}, {"xrewrite", 0}, {"krewrite", 0},
         {"esimp", 0}, {"fold", 0}, {"unfold", 0}, {"note", 0}, {"with_options", 0}, {"with_attributes", 0}, {"with_attrs", 0},
         {"generalize", 0}, {"as", 0}, {":=", 0}, {"--", 0}, {"#", 0}, {"#tactic", 0},
         {"(*", 0}, {"/-", 0}, {"begin", g_max_prec}, {"begin+", g_max_prec}, {"abstract", g_max_prec},
         {"proof", g_max_prec}, {"qed", 0}, {"@@", g_max_prec}, {"@", g_max_prec},
         {"sorry", g_max_prec}, {"+", g_plus_prec}, {g_cup, g_cup_prec}, {"->", g_arrow_prec},
         {"?(", g_max_prec}, {"⌞", g_max_prec}, {"⌟", 0}, {"match", 0},
         {"<d", g_decreasing_prec}, {"renaming", 0}, {"extends", 0}, {nullptr, 0}};

    char const * commands[] =
        {"theorem", "axiom", "axioms", "variable", "protected", "private", "reveal",
         "definition", "example", "coercion", "abbreviation", "noncomputable",
         "variables", "parameter", "parameters", "constant", "constants",
         "[visible]", "[none]", "[parsing_only]",
         "evaluate", "check", "eval", "[wf]", "[whnf]", "[priority", "[unfold_hints]",
         "print", "end", "namespace", "section", "prelude", "help",
         "import", "inductive", "record", "structure", "module", "universe", "universes", "local",
         "precedence", "reserve", "infixl", "infixr", "infix", "postfix", "prefix", "notation",
         "tactic_infixl", "tactic_infixr", "tactic_infix", "tactic_postfix", "tactic_prefix", "tactic_notation",
         "exit", "set_option", "open", "export", "override", "tactic_hint",
         "add_begin_end_tactic", "set_begin_end_tactic", "instance", "class",
         "multiple_instances", "find_decl", "attribute", "persistent",
         "include", "omit", "migrate", "init_quotient", "init_hits", "#erase_cache", "#projections", "#telescope_eq",
         "#compile", "#accessible", "#decl_stats", "#relevant_thms", "#simplify", "#app_builder", "#refl", "#symm",
         "#trans", "#congr", "#hcongr", "#congr_simp", "#congr_rel", "#normalizer", "#abstract_expr", "#unify",
         "#defeq_simplify", nullptr};

    pair<char const *, char const *> aliases[] =
        {{g_lambda_unicode, "fun"}, {"forall", "Pi"}, {g_forall_unicode, "Pi"}, {g_pi_unicode, "Pi"},
         {g_qed_unicode, "qed"}, {nullptr, nullptr}};

    pair<char const *, char const *> cmd_aliases[] =
        {{"lemma", "theorem"}, {"proposition", "theorem"}, {"premise", "variable"}, {"premises", "variables"},
         {"corollary", "theorem"}, {"hypothesis", "parameter"}, {"conjecture", "parameter"},
         {"record", "structure"}, {nullptr, nullptr}};

    auto it = builtin;
    while (it->first) {
        t = add_token(t, it->first, it->second);
        it++;
    }

    auto it2 = commands;
    while (*it2) {
        t = add_command_token(t, *it2);
        ++it2;
    }

    buffer<char const *> attrs;
    get_attribute_tokens(attrs);
    for (char const * attr : attrs)
        t = add_command_token(t, attr);

    auto it3 = aliases;
    while (it3->first) {
        t = add_token(t, it3->first, it3->second, 0);
        it3++;
    }
    t = add_token(t, g_arrow_unicode, "->", get_arrow_prec());
    t = add_token(t, g_decreasing_unicode, "<d", get_decreasing_prec());

    auto it4 = cmd_aliases;
    while (it4->first) {
        t = add_command_token(t, it4->first, it4->second);
        ++it4;
    }
}

static token_table * g_default_token_table = nullptr;

token_table mk_default_token_table() {
    return *g_default_token_table;
}

void initialize_token_table() {
    g_default_token_table = new token_table();
    init_token_table(*g_default_token_table);
}

void finalize_token_table() {
    delete g_default_token_table;
}

token_table mk_token_table() { return token_table(); }
}
