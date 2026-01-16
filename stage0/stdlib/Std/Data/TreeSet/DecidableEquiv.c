// Lean compiler output
// Module: Std.Data.TreeSet.DecidableEquiv
// Imports: public import Std.Data.TreeMap.DecidableEquiv public import Std.Data.TreeSet.Basic
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
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_instDecidableEquivOfTransCmpOfLawfulEqCmp___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_TreeSet_instDecidableEquivOfTransCmpOfLawfulEqCmp___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_TreeSet_instDecidableEquivOfTransCmpOfLawfulEqCmp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_TreeSet_instDecidableEquivOfTransCmpOfLawfulEqCmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_TreeSet_instDecidableEquivOfTransCmpOfLawfulEqCmp___redArg___closed__0;
lean_object* l_instDecidableEqPUnit___boxed(lean_object*, lean_object*);
uint8_t l_Std_TreeMap_instDecidableEquivOfTransCmpOfLawfulEqCmpOfLawfulBEq___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Std_TreeSet_instDecidableEquivOfTransCmpOfLawfulEqCmp___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_instDecidableEqPUnit___boxed), 2, 0);
x_2 = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_instDecidableEquivOfTransCmpOfLawfulEqCmp___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Std_TreeSet_instDecidableEquivOfTransCmpOfLawfulEqCmp___redArg___closed__0;
x_5 = l_Std_TreeMap_instDecidableEquivOfTransCmpOfLawfulEqCmpOfLawfulBEq___redArg(x_1, x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instDecidableEquivOfTransCmpOfLawfulEqCmp___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_TreeSet_instDecidableEquivOfTransCmpOfLawfulEqCmp___redArg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Std_TreeSet_instDecidableEquivOfTransCmpOfLawfulEqCmp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_Std_TreeSet_instDecidableEquivOfTransCmpOfLawfulEqCmp___redArg(x_2, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_TreeSet_instDecidableEquivOfTransCmpOfLawfulEqCmp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Std_TreeSet_instDecidableEquivOfTransCmpOfLawfulEqCmp(x_1, x_2, x_3, x_4, x_5, x_6);
x_8 = lean_box(x_7);
return x_8;
}
}
lean_object* initialize_Std_Data_TreeMap_DecidableEquiv(uint8_t builtin);
lean_object* initialize_Std_Data_TreeSet_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_TreeSet_DecidableEquiv(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_TreeMap_DecidableEquiv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_TreeSet_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_TreeSet_instDecidableEquivOfTransCmpOfLawfulEqCmp___redArg___closed__0 = _init_l_Std_TreeSet_instDecidableEquivOfTransCmpOfLawfulEqCmp___redArg___closed__0();
lean_mark_persistent(l_Std_TreeSet_instDecidableEquivOfTransCmpOfLawfulEqCmp___redArg___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
