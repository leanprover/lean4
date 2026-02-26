// Lean compiler output
// Module: Init.Data.Range.Polymorphic.Int
// Imports: public import Init.Data.Range.Polymorphic.Instances import Init.Omega
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
lean_object* lean_nat_to_int(lean_object*);
static lean_once_cell_t l_Std_PRange_instUpwardEnumerableInt___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_PRange_instUpwardEnumerableInt___lam__0___closed__0;
lean_object* lean_int_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_instUpwardEnumerableInt___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_instUpwardEnumerableInt___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_instUpwardEnumerableInt___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_instUpwardEnumerableInt___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_PRange_instUpwardEnumerableInt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_PRange_instUpwardEnumerableInt___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_PRange_instUpwardEnumerableInt___closed__0 = (const lean_object*)&l_Std_PRange_instUpwardEnumerableInt___closed__0_value;
static const lean_closure_object l_Std_PRange_instUpwardEnumerableInt___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_PRange_instUpwardEnumerableInt___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_PRange_instUpwardEnumerableInt___closed__1 = (const lean_object*)&l_Std_PRange_instUpwardEnumerableInt___closed__1_value;
static const lean_ctor_object l_Std_PRange_instUpwardEnumerableInt___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_PRange_instUpwardEnumerableInt___closed__0_value),((lean_object*)&l_Std_PRange_instUpwardEnumerableInt___closed__1_value)}};
static const lean_object* l_Std_PRange_instUpwardEnumerableInt___closed__2 = (const lean_object*)&l_Std_PRange_instUpwardEnumerableInt___closed__2_value;
LEAN_EXPORT const lean_object* l_Std_PRange_instUpwardEnumerableInt = (const lean_object*)&l_Std_PRange_instUpwardEnumerableInt___closed__2_value;
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* l_Int_toNat(lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_instHasSizeInt___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_instHasSizeInt___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_PRange_instHasSizeInt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_PRange_instHasSizeInt___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_PRange_instHasSizeInt___closed__0 = (const lean_object*)&l_Std_PRange_instHasSizeInt___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_PRange_instHasSizeInt = (const lean_object*)&l_Std_PRange_instHasSizeInt___closed__0_value;
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_instHasSizeInt__1___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_instHasSizeInt__1___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_PRange_instHasSizeInt__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_PRange_instHasSizeInt__1___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_PRange_instHasSizeInt__1___closed__0 = (const lean_object*)&l_Std_PRange_instHasSizeInt__1___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_PRange_instHasSizeInt__1 = (const lean_object*)&l_Std_PRange_instHasSizeInt__1___closed__0_value;
static lean_object* _init_l_Std_PRange_instUpwardEnumerableInt___lam__0___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_instUpwardEnumerableInt___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_obj_once(&l_Std_PRange_instUpwardEnumerableInt___lam__0___closed__0, &l_Std_PRange_instUpwardEnumerableInt___lam__0___closed__0_once, _init_l_Std_PRange_instUpwardEnumerableInt___lam__0___closed__0);
x_3 = lean_int_add(x_1, x_2);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_instUpwardEnumerableInt___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_PRange_instUpwardEnumerableInt___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_instUpwardEnumerableInt___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_nat_to_int(x_1);
x_4 = lean_int_add(x_2, x_3);
lean_dec(x_3);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_instUpwardEnumerableInt___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_PRange_instUpwardEnumerableInt___lam__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_instHasSizeInt___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_obj_once(&l_Std_PRange_instUpwardEnumerableInt___lam__0___closed__0, &l_Std_PRange_instUpwardEnumerableInt___lam__0___closed__0_once, _init_l_Std_PRange_instUpwardEnumerableInt___lam__0___closed__0);
x_4 = lean_int_add(x_2, x_3);
x_5 = lean_int_sub(x_4, x_1);
lean_dec(x_4);
x_6 = l_Int_toNat(x_5);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_instHasSizeInt___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_PRange_instHasSizeInt___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_instHasSizeInt__1___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_obj_once(&l_Std_PRange_instUpwardEnumerableInt___lam__0___closed__0, &l_Std_PRange_instUpwardEnumerableInt___lam__0___closed__0_once, _init_l_Std_PRange_instUpwardEnumerableInt___lam__0___closed__0);
x_5 = lean_int_add(x_2, x_4);
x_6 = lean_int_sub(x_5, x_1);
lean_dec(x_5);
x_7 = l_Int_toNat(x_6);
lean_dec(x_6);
x_8 = lean_nat_sub(x_7, x_3);
lean_dec(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_instHasSizeInt__1___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_PRange_instHasSizeInt__1___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* initialize_Init_Data_Range_Polymorphic_Instances(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Range_Polymorphic_Int(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Range_Polymorphic_Instances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
