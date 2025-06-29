// Lean compiler output
// Module: Init.Data.BitVec.Folds
// Imports: Init.Data.BitVec.Basic Init.Data.BitVec.Lemmas Init.Data.Nat.Lemmas Init.Data.Fin.Iterate
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
LEAN_EXPORT lean_object* l_BitVec_iunfoldr___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_iunfoldr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Fin_hIterate___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_iunfoldr___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_BitVec_ofNat(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_iunfoldr(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_BitVec_cons(lean_object*, uint8_t, lean_object*);
static lean_object* l_BitVec_iunfoldr___redArg___closed__0;
LEAN_EXPORT lean_object* l_BitVec_iunfoldr___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BitVec_iunfoldr___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
lean_inc(x_2);
x_6 = lean_apply_2(x_1, x_2, x_4);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_6, 1);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
x_10 = l_BitVec_cons(x_2, x_9, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_ctor_set(x_6, 1, x_10);
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_6, 0);
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_6);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
x_14 = l_BitVec_cons(x_2, x_13, x_5);
lean_dec(x_5);
lean_dec(x_2);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
static lean_object* _init_l_BitVec_iunfoldr___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_BitVec_ofNat(x_1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_BitVec_iunfoldr___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_alloc_closure((void*)(l_BitVec_iunfoldr___redArg___lam__0), 3, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = l_BitVec_iunfoldr___redArg___closed__0;
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
x_7 = l_Fin_hIterate___redArg(x_1, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_BitVec_iunfoldr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_BitVec_iunfoldr___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_BitVec_iunfoldr___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_BitVec_iunfoldr___redArg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_BitVec_iunfoldr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_BitVec_iunfoldr(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* initialize_Init_Data_BitVec_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_BitVec_Lemmas(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Nat_Lemmas(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Fin_Iterate(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_BitVec_Folds(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_BitVec_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_BitVec_Lemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Lemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Fin_Iterate(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_BitVec_iunfoldr___redArg___closed__0 = _init_l_BitVec_iunfoldr___redArg___closed__0();
lean_mark_persistent(l_BitVec_iunfoldr___redArg___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
