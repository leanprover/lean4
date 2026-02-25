// Lean compiler output
// Module: Init.Data.List.OfFn
// Imports: public import Init.Data.Fin.Fold public import Init.NotationExtra import Init.Data.Fin.Lemmas import Init.Data.List.Lemmas import Init.Data.Nat.Lemmas import Init.Data.Option.Lemmas
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_foldr_loop___at___00List_ofFn_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_ofFn___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_ofFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_foldr_loop___at___00List_ofFn_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_foldr_loop___at___00List_ofFn_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_ofFnM___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_ofFnM___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse(lean_object*, lean_object*);
static const lean_closure_object l_List_ofFnM___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_List_reverse, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_List_ofFnM___redArg___closed__0 = (const lean_object*)&l_List_ofFnM___redArg___closed__0_value;
lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_ofFnM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_ofFnM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_foldr_loop___at___00List_ofFn_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_2, x_4);
if (x_5 == 1)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_2, x_6);
lean_dec(x_2);
lean_inc(x_1);
lean_inc(x_7);
x_8 = lean_apply_1(x_1, x_7);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
x_2 = x_7;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_ofFn___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = l_Fin_foldr_loop___at___00List_ofFn_spec__0___redArg(x_2, x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_ofFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_ofFn___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Fin_foldr_loop___at___00List_ofFn_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Fin_foldr_loop___at___00List_ofFn_spec__0___redArg(x_2, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Fin_foldr_loop___at___00List_ofFn_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Fin_foldr_loop___at___00List_ofFn_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_ofFnM___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_ofFnM___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_alloc_closure((void*)(l_List_ofFnM___redArg___lam__0), 2, 1);
lean_closure_set(x_5, 0, x_3);
x_6 = lean_apply_1(x_1, x_4);
x_7 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_ofFnM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_inc(x_6);
x_7 = lean_alloc_closure((void*)(l_List_ofFnM___redArg___lam__1), 4, 2);
lean_closure_set(x_7, 0, x_3);
lean_closure_set(x_7, 1, x_6);
x_8 = ((lean_object*)(l_List_ofFnM___redArg___closed__0));
x_9 = lean_box(0);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop(lean_box(0), lean_box(0), x_2, x_1, x_7, x_9, x_10);
x_12 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_8, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_List_ofFnM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_ofFnM___redArg(x_3, x_4, x_5);
return x_6;
}
}
lean_object* initialize_Init_Data_Fin_Fold(uint8_t builtin);
lean_object* initialize_Init_NotationExtra(uint8_t builtin);
lean_object* initialize_Init_Data_Fin_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_List_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Option_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_List_OfFn(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Fin_Fold(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_NotationExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Fin_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
