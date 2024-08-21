// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Eq
// Imports: Std.Sat.AIG.CachedGatesLemmas Std.Sat.AIG.LawfulVecOperator Std.Sat.AIG.RefVecOperator
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_instLawfulOperatorBinaryRefVecMkEq(lean_object*);
lean_object* l_Std_Sat_AIG_RefVec_fold___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_RefVec_zip___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_mkBEqCached___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_instLawfulOperatorBinaryInputMkAndCached___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_mkEq___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_instLawfulOperatorBinaryRefVecMkEq___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_instLawfulOperatorBinaryRefVecMkEq___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_mkEq(lean_object*);
lean_object* l_Std_Sat_AIG_instLawfulOperatorBinaryInputMkBEqCached___rarg(lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_mkAndCached___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_mkEq___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_inc(x_2);
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_Std_Sat_AIG_mkBEqCached___rarg), 4, 2);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_2);
x_7 = l_Std_Sat_AIG_instLawfulOperatorBinaryInputMkBEqCached___rarg(x_1, x_2);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_6);
lean_ctor_set(x_8, 2, x_7);
x_9 = l_Std_Sat_AIG_RefVec_zip___rarg(x_1, x_2, x_3, x_4, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_2);
lean_inc(x_1);
x_12 = lean_alloc_closure((void*)(l_Std_Sat_AIG_mkAndCached___rarg), 4, 2);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_2);
x_13 = l_Std_Sat_AIG_instLawfulOperatorBinaryInputMkAndCached___rarg(x_1, x_2);
x_14 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_14, 0, x_3);
lean_ctor_set(x_14, 1, x_11);
lean_ctor_set(x_14, 2, x_12);
lean_ctor_set(x_14, 3, x_13);
x_15 = l_Std_Sat_AIG_RefVec_fold___rarg(x_1, x_2, x_10, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_mkEq(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_BVPred_mkEq___rarg), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_instLawfulOperatorBinaryRefVecMkEq___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_instLawfulOperatorBinaryRefVecMkEq(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_BVPred_instLawfulOperatorBinaryRefVecMkEq___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_instLawfulOperatorBinaryRefVecMkEq___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_BVPred_instLawfulOperatorBinaryRefVecMkEq___rarg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* initialize_Std_Sat_AIG_CachedGatesLemmas(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Sat_AIG_LawfulVecOperator(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Sat_AIG_RefVecOperator(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Eq(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Sat_AIG_CachedGatesLemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sat_AIG_LawfulVecOperator(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sat_AIG_RefVecOperator(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
