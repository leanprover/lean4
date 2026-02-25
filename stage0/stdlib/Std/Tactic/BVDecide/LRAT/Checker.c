// Lean compiler output
// Module: Std.Tactic.BVDecide.LRAT.Checker
// Imports: public import Std.Tactic.BVDecide.LRAT.Internal.Convert public import Std.Tactic.BVDecide.LRAT.Internal.LRATCheckerSound public import Std.Tactic.BVDecide.LRAT.Internal.CompactLRATChecker import Std.Tactic.BVDecide.LRAT.Internal.CompactLRATCheckerSound
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
lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT(lean_object*);
lean_object* l_Std_Sat_CNF_numLiterals(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker(lean_object*, lean_object*, lean_object*);
uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_instDecidableEqResult(uint8_t, uint8_t);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_check(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_check___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_check(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; 
lean_inc_ref(x_2);
x_3 = l_Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT(x_2);
x_4 = l_Std_Sat_CNF_numLiterals(x_2);
lean_dec_ref(x_2);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_add(x_4, x_5);
lean_dec(x_4);
x_7 = l_Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker(x_6, x_3, x_1);
x_8 = 0;
x_9 = l_Std_Tactic_BVDecide_LRAT_Internal_instDecidableEqResult(x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_check___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_Tactic_BVDecide_LRAT_check(x_1, x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* initialize_Std_Tactic_BVDecide_LRAT_Internal_Convert(uint8_t builtin);
lean_object* initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATCheckerSound(uint8_t builtin);
lean_object* initialize_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker(uint8_t builtin);
lean_object* initialize_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATCheckerSound(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_LRAT_Checker(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Tactic_BVDecide_LRAT_Internal_Convert(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATCheckerSound(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATCheckerSound(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
