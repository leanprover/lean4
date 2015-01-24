/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "util/sstream.h"
#include "kernel/type_checker.h"
#include "library/constants.h"
#include "library/string.h"
#include "library/tactic/tactic.h"
#include "library/tactic/expr_to_tactic.h"

namespace lean {

tactic trace_tactic(std::string const & msg) {
    return tactic1([=](environment const &, io_state const & ios, proof_state const & s) -> proof_state {
            ios.get_diagnostic_channel() << msg << "\n";
            ios.get_diagnostic_channel().get_stream().flush();
            return s;
        });
}

tactic trace_tactic(sstream const & msg) {
    return trace_tactic(msg.str());
}

tactic trace_tactic(char const * msg) {
    return trace_tactic(std::string(msg));
}

tactic trace_state_tactic(std::string const & fname, pair<unsigned, unsigned> const & pos) {
    return tactic1([=](environment const & env, io_state const & ios, proof_state const & s) -> proof_state {
            diagnostic(env, ios) << fname << ":" << pos.first << ":" << pos.second << ": proof state\n"
                                 << s.pp(env, ios) << endl;
            ios.get_diagnostic_channel().get_stream().flush();
            return s;
        });
}

tactic trace_state_tactic() {
    return tactic1([=](environment const & env, io_state const & ios, proof_state const & s) -> proof_state {
            diagnostic(env, ios) << "proof state\n" << s.pp(env, ios) << endl;
            ios.get_diagnostic_channel().get_stream().flush();
            return s;
        });
}

tactic suppress_trace(tactic const & t) {
    return tactic([=](environment const & env, io_state const & ios, proof_state const & s) -> proof_state_seq {
            io_state new_ios(ios);
            std::shared_ptr<output_channel> out(std::make_shared<string_output_channel>());
            new_ios.set_diagnostic_channel(out);
            return t(env, new_ios, s);
        });
}

void initialize_trace_tactic() {
    register_tac(get_tactic_state_name(),
                 [](type_checker &, elaborate_fn const &, expr const & e, pos_info_provider const * p) {
                     if (p)
                         if (auto it = p->get_pos_info(e))
                             return trace_state_tactic(std::string(p->get_file_name()), *it);
                     return trace_state_tactic();
                 });

    register_tac(get_tactic_trace_name(),
                 [](type_checker & tc, elaborate_fn const &, expr const & e, pos_info_provider const *) {
                     buffer<expr> args;
                     get_app_args(e, args);
                     if (args.size() != 1)
                         throw expr_to_tactic_exception(e, "invalid trace tactic, argument expected");
                     if (auto str = to_string(args[0]))
                         return trace_tactic(*str);
                     else if (auto str = to_string(tc.whnf(args[0]).first))
                         return trace_tactic(*str);
                     else
                         throw expr_to_tactic_exception(e, "invalid trace tactic, string value expected");
                 });
}

void finalize_trace_tactic() {
}
}
