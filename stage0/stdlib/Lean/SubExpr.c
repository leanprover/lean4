// Lean compiler output
// Module: Lean.SubExpr
// Imports: Init Lean.Meta.Basic Std.Data.RBMap
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
uint64_t lean_uint64_of_nat(lean_object*);
static lean_object* l_Lean_instInhabitedSubExpr___closed__2;
static uint64_t l_Lean_instInhabitedSubExpr___closed__1;
LEAN_EXPORT lean_object* l_Lean_SubExpr_maxChildren;
LEAN_EXPORT lean_object* l_Lean_SubExpr_mkRoot(lean_object*);
static lean_object* l_Lean_instInhabitedSubExpr___closed__3;
LEAN_EXPORT lean_object* l_Lean_instInhabitedSubExpr;
static uint64_t _init_l_Lean_instInhabitedSubExpr___closed__1() {
_start:
{
lean_object* x_1; uint64_t x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_uint64_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_instInhabitedSubExpr___closed__2() {
_start:
{
lean_object* x_1; uint64_t x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_instInhabitedSubExpr___closed__1;
x_3 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint64(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instInhabitedSubExpr___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_instInhabitedSubExpr___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instInhabitedSubExpr() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instInhabitedSubExpr___closed__3;
return x_1;
}
}
static lean_object* _init_l_Lean_SubExpr_maxChildren() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(4u);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_SubExpr_mkRoot(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Data_RBMap(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_SubExpr(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_RBMap(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_instInhabitedSubExpr___closed__1 = _init_l_Lean_instInhabitedSubExpr___closed__1();
l_Lean_instInhabitedSubExpr___closed__2 = _init_l_Lean_instInhabitedSubExpr___closed__2();
lean_mark_persistent(l_Lean_instInhabitedSubExpr___closed__2);
l_Lean_instInhabitedSubExpr___closed__3 = _init_l_Lean_instInhabitedSubExpr___closed__3();
lean_mark_persistent(l_Lean_instInhabitedSubExpr___closed__3);
l_Lean_instInhabitedSubExpr = _init_l_Lean_instInhabitedSubExpr();
lean_mark_persistent(l_Lean_instInhabitedSubExpr);
l_Lean_SubExpr_maxChildren = _init_l_Lean_SubExpr_maxChildren();
lean_mark_persistent(l_Lean_SubExpr_maxChildren);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
