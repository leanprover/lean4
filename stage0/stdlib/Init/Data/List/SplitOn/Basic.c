// Lean compiler output
// Module: Init.Data.List.SplitOn.Basic
// Imports: public import Init.Data.List.Basic public import Init.NotationExtra import Init.Data.Array.Bootstrap import Init.Data.List.Lemmas
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
LEAN_EXPORT lean_object* l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___lam__0(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__0_value;
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__1_value;
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__2 = (const lean_object*)&l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__2_value;
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__3 = (const lean_object*)&l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__3_value;
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__4 = (const lean_object*)&l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__4_value;
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__5 = (const lean_object*)&l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__5_value;
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__6 = (const lean_object*)&l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__6_value;
static const lean_ctor_object l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__0_value),((lean_object*)&l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__1_value)}};
static const lean_object* l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__7 = (const lean_object*)&l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__7_value;
static const lean_ctor_object l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__7_value),((lean_object*)&l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__2_value),((lean_object*)&l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__3_value),((lean_object*)&l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__4_value),((lean_object*)&l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__5_value)}};
static const lean_object* l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__8 = (const lean_object*)&l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__8_value;
static const lean_ctor_object l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__8_value),((lean_object*)&l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__6_value)}};
static const lean_object* l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__9 = (const lean_object*)&l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__9_value;
static const lean_closure_object l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__10 = (const lean_object*)&l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__10_value;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static const lean_array_object l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__11 = (const lean_object*)&l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__11_value;
lean_object* lean_array_to_list(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_splitOnPTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_splitOnPTR(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPPrepend_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPPrepend_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_splitOn___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_splitOn___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_splitOn___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_splitOn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
lean_dec_ref(x_1);
x_5 = lean_array_to_list(x_3);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_array_get_size(x_4);
x_9 = lean_unsigned_to_nat(0u);
x_10 = ((lean_object*)(l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__9));
x_11 = lean_nat_dec_lt(x_9, x_8);
if (x_11 == 0)
{
lean_dec_ref(x_4);
return x_7;
}
else
{
lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_12 = ((lean_object*)(l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__10));
x_13 = lean_usize_of_nat(x_8);
x_14 = 0;
x_15 = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_10, x_12, x_4, x_13, x_14, x_7);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_2, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_2, 1);
lean_inc(x_17);
lean_dec_ref(x_2);
lean_inc_ref(x_1);
lean_inc(x_16);
x_18 = lean_apply_1(x_1, x_16);
x_19 = lean_unbox(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_array_push(x_3, x_16);
x_2 = x_17;
x_3 = x_20;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_16);
x_22 = ((lean_object*)(l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__11));
x_23 = lean_array_to_list(x_3);
x_24 = lean_array_push(x_4, x_23);
x_2 = x_17;
x_3 = x_22;
x_4 = x_24;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_splitOnPTR___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = ((lean_object*)(l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__11));
x_4 = l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg(x_1, x_2, x_3, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_splitOnPTR(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = ((lean_object*)(l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__11));
x_5 = l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg(x_2, x_3, x_4, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPPrepend_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; 
lean_dec(x_4);
x_5 = lean_apply_1(x_3, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = lean_apply_3(x_4, x_6, x_7, x_2);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPPrepend_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPPrepend_match__1_splitter___redArg(x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; 
lean_dec(x_5);
x_6 = lean_apply_2(x_4, x_2, x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec_ref(x_1);
x_9 = lean_apply_4(x_5, x_7, x_8, x_2, x_3);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go_match__1_splitter___redArg(x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT uint8_t l_List_splitOn___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_apply_2(x_1, x_3, x_2);
x_5 = lean_unbox(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_splitOn___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_List_splitOn___redArg___lam__0(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_splitOn___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_alloc_closure((void*)(l_List_splitOn___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
x_5 = ((lean_object*)(l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__11));
x_6 = l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg(x_4, x_3, x_5, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_splitOn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_alloc_closure((void*)(l_List_splitOn___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_5, 0, x_2);
lean_closure_set(x_5, 1, x_3);
x_6 = ((lean_object*)(l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg___closed__11));
x_7 = l___private_Init_Data_List_SplitOn_Basic_0__List_splitOnPTR_go___redArg(x_5, x_4, x_6, x_6);
return x_7;
}
}
lean_object* runtime_initialize_Init_Data_List_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_NotationExtra(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Bootstrap(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Lemmas(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_List_SplitOn_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_List_Basic(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_NotationExtra(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Bootstrap(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Lemmas(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_List_SplitOn_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_List_Basic(uint8_t builtin);
lean_object* initialize_Init_NotationExtra(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Bootstrap(uint8_t builtin);
lean_object* initialize_Init_Data_List_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_List_SplitOn_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_List_Basic(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_NotationExtra(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Bootstrap(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Lemmas(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_SplitOn_Basic(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_List_SplitOn_Basic(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_List_SplitOn_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
