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
static unsigned g_max_prec        = 1024;
static unsigned g_Max_prec        = 1024*1024;
static unsigned g_plus_prec       = 65;
unsigned get_max_prec() { return g_max_prec; }
unsigned get_Max_prec() { return g_Max_prec; }
unsigned get_arrow_prec() { return g_arrow_prec; }
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

void init_token_table(token_table & t) {
    pair<char const *, unsigned> builtin[] =
        {{"fun", 0}, {"Pi", 0}, {"let", 0}, {"in", 0}, {"at", 0},
         {"have", 0}, {"assume", 0}, {"show", 0}, {"suffices", 0},
         {"do", 0}, {"if", 0}, {"then", 0}, {"else", 0}, {"by", 0},
         {"hiding", 0}, {"replacing", 0}, {"renaming", 0},
         {"from", 0}, {"(", g_max_prec}, {"`(", g_max_prec}, {"``(", g_max_prec},
         {"```(", g_max_prec}, {"`[", g_max_prec}, {"`", g_max_prec},
         {"%%", g_max_prec}, {"()", g_max_prec}, {"(::)", g_max_prec}, {")", 0}, {"'", 0},
         {"{", g_max_prec}, {"}", 0}, {"_", g_max_prec},
         {"[", g_max_prec}, {"#[", g_max_prec}, {"]", 0}, {"⦃", g_max_prec}, {"⦄", 0}, {".{", 0},
         {"{!", g_max_prec}, {"!}", 0},
         {"Type", g_max_prec}, {"Type*", g_max_prec}, {"Sort", g_max_prec}, {"Sort*", g_max_prec},
         {"(:", g_max_prec}, {":)", 0}, {".(", g_max_prec}, {"._", g_max_prec},
         {"⟨", g_max_prec}, {"⟩", 0}, {"^", 0},
         {"//", 0}, {"|", 0}, {"with", 0}, {"without", 0}, {"..", 0}, {"...", 0}, {",", 0},
         {".", 0}, {":", 0}, {"!", 0}, {"calc", 0}, {":=", 0}, {"--", 0}, {"#", g_max_prec},
         {"/-", 0}, {"/--", 0}, {"/-!", 0}, {"begin", g_max_prec}, {"using", 0},
         {"@@", g_max_prec}, {"@", g_max_prec},
         {"sorry", g_max_prec}, {"+", g_plus_prec}, {"->", g_arrow_prec}, {"<-", 0},
         {"match", 0}, {"^.", g_max_prec+1},
         {"renaming", 0}, {"extends", 0}, {nullptr, 0}};

    char const * commands[] =
        {"theorem", "axiom", "axioms", "variable", "protected", "private", "hide",
         "definition", "meta", "mutual", "example", "noncomputable", "abbreviation",
         "variables", "parameter", "parameters", "constant", "constants",
         "using_well_founded", "[whnf]",
         "end", "namespace", "section", "prelude",
         "import", "inductive", "coinductive", "structure", "class", "universe", "universes", "local",
         "precedence", "reserve", "infixl", "infixr", "infix", "postfix", "prefix", "notation",
         "set_option", "open", "export", "@[",
         "attribute", "instance", "include", "omit", "init_quotient",
         "declare_trace", "add_key_equivalence",
         "run_cmd", "#check", "#reduce", "#eval", "#print", "#help", "#exit",
         "#compile", "#unify", nullptr};

    pair<char const *, char const *> aliases[] =
        {{"λ", "fun"}, {"forall", "Pi"},
         {"∀", "Pi"}, {"Π", "Pi"}, {"(|", "⟨"}, {"|)", "⟩"}, {nullptr, nullptr}};

    pair<char const *, char const *> cmd_aliases[] =
        {{"lemma", "theorem"}, {"def", "definition"},
         {nullptr, nullptr}};

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

    auto it3 = aliases;
    while (it3->first) {
        t = add_token(t, it3->first, it3->second, 0);
        it3++;
    }
    t = add_token(t, "→", "->", get_arrow_prec());
    t = add_token(t, "←", "<-", 0);

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
