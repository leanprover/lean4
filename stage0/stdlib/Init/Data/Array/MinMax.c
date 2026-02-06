// Lean compiler output
// Module: Init.Data.Array.MinMax
// Imports: public import Init.Data.Array.Lemmas import Init.Data.List.MinMax public import Init.Data.Order.Classes import Init.Data.Array.Bootstrap import Init.Data.Array.DecidableEq import Init.Data.List.TakeDrop import Init.Data.Order.Lemmas
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
LEAN_EXPORT lean_object* l_Array_min___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Array_min___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_min___redArg___closed__0 = (const lean_object*)&l_Array_min___redArg___closed__0_value;
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Array_min___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_min___redArg___closed__1 = (const lean_object*)&l_Array_min___redArg___closed__1_value;
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Array_min___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_min___redArg___closed__2 = (const lean_object*)&l_Array_min___redArg___closed__2_value;
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Array_min___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_min___redArg___closed__3 = (const lean_object*)&l_Array_min___redArg___closed__3_value;
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Array_min___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_min___redArg___closed__4 = (const lean_object*)&l_Array_min___redArg___closed__4_value;
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Array_min___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_min___redArg___closed__5 = (const lean_object*)&l_Array_min___redArg___closed__5_value;
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Array_min___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_min___redArg___closed__6 = (const lean_object*)&l_Array_min___redArg___closed__6_value;
static const lean_ctor_object l_Array_min___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Array_min___redArg___closed__0_value),((lean_object*)&l_Array_min___redArg___closed__1_value)}};
static const lean_object* l_Array_min___redArg___closed__7 = (const lean_object*)&l_Array_min___redArg___closed__7_value;
static const lean_ctor_object l_Array_min___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Array_min___redArg___closed__7_value),((lean_object*)&l_Array_min___redArg___closed__2_value),((lean_object*)&l_Array_min___redArg___closed__3_value),((lean_object*)&l_Array_min___redArg___closed__4_value),((lean_object*)&l_Array_min___redArg___closed__5_value)}};
static const lean_object* l_Array_min___redArg___closed__8 = (const lean_object*)&l_Array_min___redArg___closed__8_value;
static const lean_ctor_object l_Array_min___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Array_min___redArg___closed__8_value),((lean_object*)&l_Array_min___redArg___closed__6_value)}};
static const lean_object* l_Array_min___redArg___closed__9 = (const lean_object*)&l_Array_min___redArg___closed__9_value;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_min___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_min(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_min_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_min_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_max___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_max(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_max_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_max_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_min___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_min___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_fget(x_2, x_3);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_array_get_size(x_2);
x_7 = ((lean_object*)(l_Array_min___redArg___closed__9));
x_8 = lean_nat_dec_lt(x_5, x_6);
if (x_8 == 0)
{
lean_dec_ref(x_2);
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_alloc_closure((void*)(l_Array_min___redArg___lam__0), 3, 1);
lean_closure_set(x_9, 0, x_1);
x_10 = lean_nat_dec_le(x_6, x_6);
if (x_10 == 0)
{
if (x_8 == 0)
{
lean_dec_ref(x_9);
lean_dec_ref(x_2);
return x_4;
}
else
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = 1;
x_12 = lean_usize_of_nat(x_6);
x_13 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_7, x_9, x_2, x_11, x_12, x_4);
return x_13;
}
}
else
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = 1;
x_15 = lean_usize_of_nat(x_6);
x_16 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_7, x_9, x_2, x_14, x_15, x_4);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_min(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_min___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_min_x3f___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Array_isEmpty___redArg(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Array_min___redArg(x_1, x_2);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
else
{
lean_object* x_6; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_6 = lean_box(0);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Array_min_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_min_x3f___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_max___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_fget(x_2, x_3);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_array_get_size(x_2);
x_7 = ((lean_object*)(l_Array_min___redArg___closed__9));
x_8 = lean_nat_dec_lt(x_5, x_6);
if (x_8 == 0)
{
lean_dec_ref(x_2);
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_alloc_closure((void*)(l_Array_min___redArg___lam__0), 3, 1);
lean_closure_set(x_9, 0, x_1);
x_10 = lean_nat_dec_le(x_6, x_6);
if (x_10 == 0)
{
if (x_8 == 0)
{
lean_dec_ref(x_9);
lean_dec_ref(x_2);
return x_4;
}
else
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = 1;
x_12 = lean_usize_of_nat(x_6);
x_13 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_7, x_9, x_2, x_11, x_12, x_4);
return x_13;
}
}
else
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = 1;
x_15 = lean_usize_of_nat(x_6);
x_16 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_7, x_9, x_2, x_14, x_15, x_4);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_max(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_max___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_max_x3f___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Array_isEmpty___redArg(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Array_max___redArg(x_1, x_2);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
else
{
lean_object* x_6; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_6 = lean_box(0);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Array_max_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_max_x3f___redArg(x_2, x_3);
return x_4;
}
}
lean_object* initialize_Init_Data_Array_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_List_MinMax(uint8_t builtin);
lean_object* initialize_Init_Data_Order_Classes(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Bootstrap(uint8_t builtin);
lean_object* initialize_Init_Data_Array_DecidableEq(uint8_t builtin);
lean_object* initialize_Init_Data_List_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_Order_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Array_MinMax(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Array_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_MinMax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Order_Classes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_DecidableEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Order_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
