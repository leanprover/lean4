/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Henrik Böving

Bindings to the CaDiCaL SAT solver linked into the Lean libraries. The Lean declarations live in
`Lean.Cadical.Internal`; they only pass borrowed solver references, so no function here takes
ownership of the solver object.
*/
#include <lean/lean.h>
#include "runtime/cadical.h"

#ifdef LEAN_CADICAL
#include <vector>
#include <cadical.hpp>
#endif

namespace lean {

/* Lean.Cadical.Internal.getSignature (u : Unit) : String */
extern "C" LEAN_EXPORT lean_obj_res lean_cadical_signature(lean_obj_arg /* u */) {
#ifdef LEAN_CADICAL
    return lean_mk_string(CaDiCaL::Solver::signature());
#else
    return lean_mk_string("");
#endif
}

#ifdef LEAN_CADICAL

static lean_external_class * g_cadical_solver_external_class = nullptr;

static void cadical_solver_finalizer(void * ptr) {
    delete static_cast<CaDiCaL::Solver *>(ptr);
}

static void cadical_solver_foreach(void *, b_lean_obj_arg) {}

extern "C" void initialize_cadical() {
    g_cadical_solver_external_class =
        lean_register_external_class(cadical_solver_finalizer, cadical_solver_foreach);
}

static inline CaDiCaL::Solver * to_solver(b_lean_obj_arg o) {
    return static_cast<CaDiCaL::Solver *>(lean_get_external_data(o));
}

static inline int to_lit(uint32_t lit) {
    return static_cast<int32_t>(lit);
}

/* Constructor indices of `Lean.Cadical.Internal.Status`. */
static inline uint8_t to_status(int r) {
    switch (r) {
    case 10: return 0;  // satisfiable
    case 20: return 1;  // unsatisfiable
    default: return 2;  // unknown
    }
}

static inline lean_obj_res unit() { return lean_box(0); }
static inline uint32_t to_int32(int v) { return static_cast<uint32_t>(v); }
static inline uint64_t to_int64(int64_t v) { return static_cast<uint64_t>(v); }
static inline lean_obj_res io_unit() { return lean_io_result_mk_ok(lean_box(0)); }

/* Solver.new : BaseIO Solver */
extern "C" LEAN_EXPORT lean_obj_res lean_cadical_solver_new() {
    return lean_alloc_external(g_cadical_solver_external_class, new CaDiCaL::Solver());
}

/* Solver.add (s : @& Solver) (lit : Int32) : BaseIO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_cadical_solver_add(b_lean_obj_arg s, uint32_t lit) {
    to_solver(s)->add(to_lit(lit));
    return unit();
}

/* Solver.clause (s : @& Solver) (lits : @& Array Int32) : BaseIO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_cadical_solver_clause(b_lean_obj_arg s, b_lean_obj_arg lits) {
    size_t n = lean_array_size(lits);
    std::vector<int> buf;
    buf.reserve(n);
    for (size_t i = 0; i < n; i++) {
        buf.push_back(to_lit(lean_unbox_uint32(lean_array_get_core(lits, i))));
    }
    to_solver(s)->clause(buf.data(), n);
    return unit();
}

/* Solver.inconsistent (s : @& Solver) : BaseIO Bool */
extern "C" LEAN_EXPORT uint8_t lean_cadical_solver_inconsistent(b_lean_obj_arg s) {
    return to_solver(s)->inconsistent();
}

/* Solver.assume (s : @& Solver) (lit : Int32) : BaseIO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_cadical_solver_assume(b_lean_obj_arg s, uint32_t lit) {
    to_solver(s)->assume(to_lit(lit));
    return unit();
}

/* Solver.solve (s : @& Solver) : BaseIO Status */
extern "C" LEAN_EXPORT uint8_t lean_cadical_solver_solve(b_lean_obj_arg s) {
    return to_status(to_solver(s)->solve());
}

/* Solver.val (s : @& Solver) (lit : Int32) : BaseIO Int32 */
extern "C" LEAN_EXPORT uint32_t lean_cadical_solver_val(b_lean_obj_arg s, uint32_t lit) {
    return to_int32(to_solver(s)->val(to_lit(lit)));
}

/* Solver.flip (s : @& Solver) (lit : Int32) : BaseIO Bool */
extern "C" LEAN_EXPORT uint8_t lean_cadical_solver_flip(b_lean_obj_arg s, uint32_t lit) {
    return to_solver(s)->flip(to_lit(lit));
}

/* Solver.flippable (s : @& Solver) (lit : Int32) : BaseIO Bool */
extern "C" LEAN_EXPORT uint8_t lean_cadical_solver_flippable(b_lean_obj_arg s, uint32_t lit) {
    return to_solver(s)->flippable(to_lit(lit));
}

/* Solver.failed (s : @& Solver) (lit : Int32) : BaseIO Bool */
extern "C" LEAN_EXPORT uint8_t lean_cadical_solver_failed(b_lean_obj_arg s, uint32_t lit) {
    return to_solver(s)->failed(to_lit(lit));
}

/* Solver.constrain (s : @& Solver) (lit : Int32) : BaseIO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_cadical_solver_constrain(b_lean_obj_arg s, uint32_t lit) {
    to_solver(s)->constrain(to_lit(lit));
    return unit();
}

/* Solver.constraintFailed (s : @& Solver) : BaseIO Bool */
extern "C" LEAN_EXPORT uint8_t lean_cadical_solver_constraint_failed(b_lean_obj_arg s) {
    return to_solver(s)->constraint_failed();
}

/* Solver.lookahead (s : @& Solver) : BaseIO Int32 */
extern "C" LEAN_EXPORT uint32_t lean_cadical_solver_lookahead(b_lean_obj_arg s) {
    return to_int32(to_solver(s)->lookahead());
}

/* Solver.resetAssumptions (s : @& Solver) : BaseIO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_cadical_solver_reset_assumptions(b_lean_obj_arg s) {
    to_solver(s)->reset_assumptions();
    return unit();
}

/* Solver.resetConstraint (s : @& Solver) : BaseIO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_cadical_solver_reset_constraint(b_lean_obj_arg s) {
    to_solver(s)->reset_constraint();
    return unit();
}

/* Solver.state (s : @& Solver) : BaseIO UInt16 */
extern "C" LEAN_EXPORT uint16_t lean_cadical_solver_state(b_lean_obj_arg s) {
    return static_cast<uint16_t>(to_solver(s)->state());
}

/* Solver.status (s : @& Solver) : BaseIO Status */
extern "C" LEAN_EXPORT uint8_t lean_cadical_solver_status(b_lean_obj_arg s) {
    return to_status(to_solver(s)->status());
}

/* Solver.vars (s : @& Solver) : BaseIO Int32 */
extern "C" LEAN_EXPORT uint32_t lean_cadical_solver_vars(b_lean_obj_arg s) {
    return to_int32(to_solver(s)->vars());
}

/* Solver.resize (s : @& Solver) (minMaxVar : Int32) : BaseIO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_cadical_solver_resize(b_lean_obj_arg s, uint32_t min_max_var) {
    // `reserve` was renamed to `resize` (with unchanged semantics) in CaDiCaL 2.2.
    to_solver(s)->reserve(to_lit(min_max_var));
    return unit();
}

/* Solver.isValidOption (opt : @& String) : Bool */
extern "C" LEAN_EXPORT uint8_t lean_cadical_solver_is_valid_option(b_lean_obj_arg opt) {
    return CaDiCaL::Solver::is_valid_option(lean_string_cstr(opt));
}

/* Solver.isPreprocessingOption (opt : @& String) : Bool */
extern "C" LEAN_EXPORT uint8_t lean_cadical_solver_is_preprocessing_option(b_lean_obj_arg opt) {
    return CaDiCaL::Solver::is_preprocessing_option(lean_string_cstr(opt));
}

/* Solver.isValidLongOption (opt : @& String) : Bool */
extern "C" LEAN_EXPORT uint8_t lean_cadical_solver_is_valid_long_option(b_lean_obj_arg opt) {
    return CaDiCaL::Solver::is_valid_long_option(lean_string_cstr(opt));
}

/* Solver.get (s : @& Solver) (opt : @& String) : BaseIO Int32 */
extern "C" LEAN_EXPORT uint32_t lean_cadical_solver_get(b_lean_obj_arg s, b_lean_obj_arg opt) {
    return to_int32(to_solver(s)->get(lean_string_cstr(opt)));
}

/* Solver.set (s : @& Solver) (opt : @& String) (val : Int32) : BaseIO Bool */
extern "C" LEAN_EXPORT uint8_t lean_cadical_solver_set(b_lean_obj_arg s, b_lean_obj_arg opt, uint32_t val) {
    return to_solver(s)->set(lean_string_cstr(opt), to_lit(val));
}

/* Solver.setLongOption (s : @& Solver) (opt : @& String) : BaseIO Bool */
extern "C" LEAN_EXPORT uint8_t lean_cadical_solver_set_long_option(b_lean_obj_arg s, b_lean_obj_arg opt) {
    return to_solver(s)->set_long_option(lean_string_cstr(opt));
}

/* Solver.isValidConfiguration (opt : @& String) : Bool */
extern "C" LEAN_EXPORT uint8_t lean_cadical_solver_is_valid_configuration(b_lean_obj_arg opt) {
    return CaDiCaL::Solver::is_valid_configuration(lean_string_cstr(opt));
}

/* Solver.configure (s : @& Solver) (opt : @& String) : BaseIO Bool */
extern "C" LEAN_EXPORT uint8_t lean_cadical_solver_configure(b_lean_obj_arg s, b_lean_obj_arg opt) {
    return to_solver(s)->configure(lean_string_cstr(opt));
}

/* Solver.optimize (s : @& Solver) (val : Int32) : BaseIO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_cadical_solver_optimize(b_lean_obj_arg s, uint32_t val) {
    to_solver(s)->optimize(to_lit(val));
    return unit();
}

/* Solver.limit (s : @& Solver) (limit : @& String) (val : Int32) : BaseIO Bool */
extern "C" LEAN_EXPORT uint8_t lean_cadical_solver_limit(b_lean_obj_arg s, b_lean_obj_arg limit, uint32_t val) {
    return to_solver(s)->limit(lean_string_cstr(limit), to_lit(val));
}

/* Solver.isValidLimit (s : @& Solver) (limit : @& String) : BaseIO Bool */
extern "C" LEAN_EXPORT uint8_t lean_cadical_solver_is_valid_limit(b_lean_obj_arg s, b_lean_obj_arg limit) {
    return to_solver(s)->is_valid_limit(lean_string_cstr(limit));
}

/* Solver.active (s : @& Solver) : BaseIO Int32 */
extern "C" LEAN_EXPORT uint32_t lean_cadical_solver_active(b_lean_obj_arg s) {
    return to_int32(to_solver(s)->active());
}

/* Solver.redundant (s : @& Solver) : BaseIO Int64 */
extern "C" LEAN_EXPORT uint64_t lean_cadical_solver_redundant(b_lean_obj_arg s) {
    return to_int64(to_solver(s)->redundant());
}

/* Solver.irredundant (s : @& Solver) : BaseIO Int64 */
extern "C" LEAN_EXPORT uint64_t lean_cadical_solver_irredundant(b_lean_obj_arg s) {
    return to_int64(to_solver(s)->irredundant());
}

/* Solver.simplify (s : @& Solver) (rounds : Int32) : BaseIO Status */
extern "C" LEAN_EXPORT uint8_t lean_cadical_solver_simplify(b_lean_obj_arg s, uint32_t rounds) {
    return to_status(to_solver(s)->simplify(to_lit(rounds)));
}

/* Solver.terminate (s : @& Solver) : BaseIO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_cadical_solver_terminate(b_lean_obj_arg s) {
    to_solver(s)->terminate();
    return unit();
}

/* Solver.frozen (s : @& Solver) (lit : Int32) : BaseIO Bool */
extern "C" LEAN_EXPORT uint8_t lean_cadical_solver_frozen(b_lean_obj_arg s, uint32_t lit) {
    return to_solver(s)->frozen(to_lit(lit));
}

/* Solver.freeze (s : @& Solver) (lit : Int32) : BaseIO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_cadical_solver_freeze(b_lean_obj_arg s, uint32_t lit) {
    to_solver(s)->freeze(to_lit(lit));
    return unit();
}

/* Solver.melt (s : @& Solver) (lit : Int32) : BaseIO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_cadical_solver_melt(b_lean_obj_arg s, uint32_t lit) {
    to_solver(s)->melt(to_lit(lit));
    return unit();
}

/* Solver.fixed (s : @& Solver) (lit : Int32) : BaseIO Int32 */
extern "C" LEAN_EXPORT uint32_t lean_cadical_solver_fixed(b_lean_obj_arg s, uint32_t lit) {
    return to_int32(to_solver(s)->fixed(to_lit(lit)));
}

/* Solver.phase (s : @& Solver) (lit : Int32) : BaseIO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_cadical_solver_phase(b_lean_obj_arg s, uint32_t lit) {
    to_solver(s)->phase(to_lit(lit));
    return unit();
}

/* Solver.unphase (s : @& Solver) (lit : Int32) : BaseIO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_cadical_solver_unphase(b_lean_obj_arg s, uint32_t lit) {
    to_solver(s)->unphase(to_lit(lit));
    return unit();
}

/* Solver.conclude (s : @& Solver) : BaseIO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_cadical_solver_conclude(b_lean_obj_arg s) {
    to_solver(s)->conclude();
    return unit();
}

/* Solver.usage : IO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_cadical_solver_usage() {
    CaDiCaL::Solver::usage();
    return io_unit();
}

/* Solver.configurations : IO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_cadical_solver_configurations() {
    CaDiCaL::Solver::configurations();
    return io_unit();
}

/* Solver.statistics (s : @& Solver) : IO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_cadical_solver_statistics(b_lean_obj_arg s) {
    to_solver(s)->statistics();
    return io_unit();
}

/* Solver.resources (s : @& Solver) : IO Unit */
extern "C" LEAN_EXPORT lean_obj_res lean_cadical_solver_resources(b_lean_obj_arg s) {
    to_solver(s)->resources();
    return io_unit();
}

#else

static const char * g_cadical_unavailable_msg = "CaDiCaL is not available in this build of Lean";

extern "C" void initialize_cadical() {}

/* Solver.new : BaseIO Solver */
extern "C" LEAN_EXPORT lean_obj_res lean_cadical_solver_new() {
    lean_internal_panic(g_cadical_unavailable_msg);
}

/*
Every other solver operation needs a `Solver`, which `new` never produces without CaDiCaL, so these
are unreachable but must still exist for linking. The static option queries are pure and just
answer `false`, the printing functions are in `IO` and report a proper error.
*/
#define LEAN_CADICAL_UNREACHABLE(ret, name, ...) \
    extern "C" LEAN_EXPORT ret name(__VA_ARGS__) { lean_internal_panic(g_cadical_unavailable_msg); }
#define LEAN_CADICAL_FALSE(name) \
    extern "C" LEAN_EXPORT uint8_t name(b_lean_obj_arg) { return false; }
#define LEAN_CADICAL_IO_ERROR(name, ...) \
    extern "C" LEAN_EXPORT lean_obj_res name(__VA_ARGS__) { \
        return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(g_cadical_unavailable_msg))); \
    }

LEAN_CADICAL_UNREACHABLE(lean_obj_res, lean_cadical_solver_add, b_lean_obj_arg, uint32_t)
LEAN_CADICAL_UNREACHABLE(lean_obj_res, lean_cadical_solver_clause, b_lean_obj_arg, b_lean_obj_arg)
LEAN_CADICAL_UNREACHABLE(uint8_t, lean_cadical_solver_inconsistent, b_lean_obj_arg)
LEAN_CADICAL_UNREACHABLE(lean_obj_res, lean_cadical_solver_assume, b_lean_obj_arg, uint32_t)
LEAN_CADICAL_UNREACHABLE(uint8_t, lean_cadical_solver_solve, b_lean_obj_arg)
LEAN_CADICAL_UNREACHABLE(uint32_t, lean_cadical_solver_val, b_lean_obj_arg, uint32_t)
LEAN_CADICAL_UNREACHABLE(uint8_t, lean_cadical_solver_flip, b_lean_obj_arg, uint32_t)
LEAN_CADICAL_UNREACHABLE(uint8_t, lean_cadical_solver_flippable, b_lean_obj_arg, uint32_t)
LEAN_CADICAL_UNREACHABLE(uint8_t, lean_cadical_solver_failed, b_lean_obj_arg, uint32_t)
LEAN_CADICAL_UNREACHABLE(lean_obj_res, lean_cadical_solver_constrain, b_lean_obj_arg, uint32_t)
LEAN_CADICAL_UNREACHABLE(uint8_t, lean_cadical_solver_constraint_failed, b_lean_obj_arg)
LEAN_CADICAL_UNREACHABLE(uint32_t, lean_cadical_solver_lookahead, b_lean_obj_arg)
LEAN_CADICAL_UNREACHABLE(lean_obj_res, lean_cadical_solver_reset_assumptions, b_lean_obj_arg)
LEAN_CADICAL_UNREACHABLE(lean_obj_res, lean_cadical_solver_reset_constraint, b_lean_obj_arg)
LEAN_CADICAL_UNREACHABLE(uint16_t, lean_cadical_solver_state, b_lean_obj_arg)
LEAN_CADICAL_UNREACHABLE(uint8_t, lean_cadical_solver_status, b_lean_obj_arg)
LEAN_CADICAL_UNREACHABLE(uint32_t, lean_cadical_solver_vars, b_lean_obj_arg)
LEAN_CADICAL_UNREACHABLE(lean_obj_res, lean_cadical_solver_resize, b_lean_obj_arg, uint32_t)
LEAN_CADICAL_FALSE(lean_cadical_solver_is_valid_option)
LEAN_CADICAL_FALSE(lean_cadical_solver_is_preprocessing_option)
LEAN_CADICAL_FALSE(lean_cadical_solver_is_valid_long_option)
LEAN_CADICAL_UNREACHABLE(uint32_t, lean_cadical_solver_get, b_lean_obj_arg, b_lean_obj_arg)
LEAN_CADICAL_UNREACHABLE(uint8_t, lean_cadical_solver_set, b_lean_obj_arg, b_lean_obj_arg, uint32_t)
LEAN_CADICAL_UNREACHABLE(uint8_t, lean_cadical_solver_set_long_option, b_lean_obj_arg, b_lean_obj_arg)
LEAN_CADICAL_FALSE(lean_cadical_solver_is_valid_configuration)
LEAN_CADICAL_UNREACHABLE(uint8_t, lean_cadical_solver_configure, b_lean_obj_arg, b_lean_obj_arg)
LEAN_CADICAL_UNREACHABLE(lean_obj_res, lean_cadical_solver_optimize, b_lean_obj_arg, uint32_t)
LEAN_CADICAL_UNREACHABLE(uint8_t, lean_cadical_solver_limit, b_lean_obj_arg, b_lean_obj_arg, uint32_t)
LEAN_CADICAL_UNREACHABLE(uint8_t, lean_cadical_solver_is_valid_limit, b_lean_obj_arg, b_lean_obj_arg)
LEAN_CADICAL_UNREACHABLE(uint32_t, lean_cadical_solver_active, b_lean_obj_arg)
LEAN_CADICAL_UNREACHABLE(uint64_t, lean_cadical_solver_redundant, b_lean_obj_arg)
LEAN_CADICAL_UNREACHABLE(uint64_t, lean_cadical_solver_irredundant, b_lean_obj_arg)
LEAN_CADICAL_UNREACHABLE(uint8_t, lean_cadical_solver_simplify, b_lean_obj_arg, uint32_t)
LEAN_CADICAL_UNREACHABLE(lean_obj_res, lean_cadical_solver_terminate, b_lean_obj_arg)
LEAN_CADICAL_UNREACHABLE(uint8_t, lean_cadical_solver_frozen, b_lean_obj_arg, uint32_t)
LEAN_CADICAL_UNREACHABLE(lean_obj_res, lean_cadical_solver_freeze, b_lean_obj_arg, uint32_t)
LEAN_CADICAL_UNREACHABLE(lean_obj_res, lean_cadical_solver_melt, b_lean_obj_arg, uint32_t)
LEAN_CADICAL_UNREACHABLE(uint32_t, lean_cadical_solver_fixed, b_lean_obj_arg, uint32_t)
LEAN_CADICAL_UNREACHABLE(lean_obj_res, lean_cadical_solver_phase, b_lean_obj_arg, uint32_t)
LEAN_CADICAL_UNREACHABLE(lean_obj_res, lean_cadical_solver_unphase, b_lean_obj_arg, uint32_t)
LEAN_CADICAL_UNREACHABLE(lean_obj_res, lean_cadical_solver_conclude, b_lean_obj_arg)
LEAN_CADICAL_IO_ERROR(lean_cadical_solver_usage)
LEAN_CADICAL_IO_ERROR(lean_cadical_solver_configurations)
LEAN_CADICAL_IO_ERROR(lean_cadical_solver_statistics, b_lean_obj_arg)
LEAN_CADICAL_IO_ERROR(lean_cadical_solver_resources, b_lean_obj_arg)

#undef LEAN_CADICAL_UNREACHABLE
#undef LEAN_CADICAL_FALSE
#undef LEAN_CADICAL_IO_ERROR

#endif

}
