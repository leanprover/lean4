// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Types
// Imports: Lean.Meta.Tactic.Grind.Arith.Offset.Types Lean.Meta.Tactic.Grind.Arith.Cutsat.Types Lean.Meta.Tactic.Grind.Arith.CommRing.Types Lean.Meta.Tactic.Grind.Arith.Linear.Types
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_instInhabitedState_default;
extern lean_object* l_Lean_Meta_Grind_Arith_CommRing_instInhabitedState_default;
static lean_object* l_Lean_Meta_Grind_Arith_instInhabitedState_default___closed__1;
static lean_object* l_Lean_Meta_Grind_Arith_instInhabitedState_default___closed__2;
static lean_object* l_Lean_Meta_Grind_Arith_instInhabitedState_default___closed__0;
extern lean_object* l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_State_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_instInhabitedState;
extern lean_object* l_Lean_Meta_Grind_Arith_Offset_instInhabitedState_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_State_ctorIdx___boxed(lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default;
static lean_object* l_Lean_Meta_Grind_Arith_instInhabitedState_default___closed__4;
static lean_object* l_Lean_Meta_Grind_Arith_instInhabitedState_default___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_State_ctorIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_State_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Grind_Arith_State_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_instInhabitedState_default___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_Arith_Offset_instInhabitedState_default;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_instInhabitedState_default___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_instInhabitedState_default___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_Arith_CommRing_instInhabitedState_default;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_instInhabitedState_default___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_instInhabitedState_default___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Grind_Arith_instInhabitedState_default___closed__3;
x_2 = l_Lean_Meta_Grind_Arith_instInhabitedState_default___closed__2;
x_3 = l_Lean_Meta_Grind_Arith_instInhabitedState_default___closed__1;
x_4 = l_Lean_Meta_Grind_Arith_instInhabitedState_default___closed__0;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_instInhabitedState_default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_Arith_instInhabitedState_default___closed__4;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_instInhabitedState() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_Arith_instInhabitedState_default;
return x_1;
}
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Offset_Types(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Types(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Types(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Types(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Arith_Offset_Types(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Types(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Types(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_Arith_instInhabitedState_default___closed__0 = _init_l_Lean_Meta_Grind_Arith_instInhabitedState_default___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_instInhabitedState_default___closed__0);
l_Lean_Meta_Grind_Arith_instInhabitedState_default___closed__1 = _init_l_Lean_Meta_Grind_Arith_instInhabitedState_default___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_instInhabitedState_default___closed__1);
l_Lean_Meta_Grind_Arith_instInhabitedState_default___closed__2 = _init_l_Lean_Meta_Grind_Arith_instInhabitedState_default___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_instInhabitedState_default___closed__2);
l_Lean_Meta_Grind_Arith_instInhabitedState_default___closed__3 = _init_l_Lean_Meta_Grind_Arith_instInhabitedState_default___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_instInhabitedState_default___closed__3);
l_Lean_Meta_Grind_Arith_instInhabitedState_default___closed__4 = _init_l_Lean_Meta_Grind_Arith_instInhabitedState_default___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_instInhabitedState_default___closed__4);
l_Lean_Meta_Grind_Arith_instInhabitedState_default = _init_l_Lean_Meta_Grind_Arith_instInhabitedState_default();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_instInhabitedState_default);
l_Lean_Meta_Grind_Arith_instInhabitedState = _init_l_Lean_Meta_Grind_Arith_instInhabitedState();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_instInhabitedState);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
