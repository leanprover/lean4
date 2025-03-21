// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.Arith
// Imports: Lean.Meta.Tactic.Simp.Arith.Nat Lean.Meta.Tactic.Simp.Arith.Int
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
uint8_t l_Lean_Meta_Simp_Arith_isDvdCnstr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_parentIsTarget___boxed(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Simp_Arith_isLinearCnstr(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_Arith_parentIsTarget(lean_object*, uint8_t);
uint8_t l_Lean_Meta_Simp_Arith_isLinearTerm(lean_object*, uint8_t);
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_Arith_parentIsTarget(lean_object* x_1, uint8_t x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_Lean_Meta_Simp_Arith_isLinearTerm(x_4, x_2);
if (x_5 == 0)
{
uint8_t x_6; 
lean_inc(x_4);
x_6 = l_Lean_Meta_Simp_Arith_isLinearCnstr(x_4);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = l_Lean_Meta_Simp_Arith_isDvdCnstr(x_4);
lean_dec(x_4);
return x_7;
}
else
{
uint8_t x_8; 
lean_dec(x_4);
x_8 = 1;
return x_8;
}
}
else
{
uint8_t x_9; 
lean_dec(x_4);
x_9 = 1;
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_parentIsTarget___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l_Lean_Meta_Simp_Arith_parentIsTarget(x_1, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* initialize_Lean_Meta_Tactic_Simp_Arith_Nat(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_Arith_Int(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Simp_Arith(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Simp_Arith_Nat(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Arith_Int(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
