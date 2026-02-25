// Lean compiler output
// Module: Init.Data.Array.BasicAux
// Imports: import all Init.Data.Array.Basic public import Init.Data.Array.Set public import Init.Util import Init.Data.Nat.Linear
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__List_toArrayAux_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__List_toArrayAux_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapM_x27___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapM_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMono___redArg___lam__0(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Array_mapMono___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_mapMono___redArg___closed__0 = (const lean_object*)&l_Array_mapMono___redArg___closed__0_value;
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Array_mapMono___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_mapMono___redArg___closed__1 = (const lean_object*)&l_Array_mapMono___redArg___closed__1_value;
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Array_mapMono___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_mapMono___redArg___closed__2 = (const lean_object*)&l_Array_mapMono___redArg___closed__2_value;
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Array_mapMono___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_mapMono___redArg___closed__3 = (const lean_object*)&l_Array_mapMono___redArg___closed__3_value;
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Array_mapMono___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_mapMono___redArg___closed__4 = (const lean_object*)&l_Array_mapMono___redArg___closed__4_value;
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Array_mapMono___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_mapMono___redArg___closed__5 = (const lean_object*)&l_Array_mapMono___redArg___closed__5_value;
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Array_mapMono___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Array_mapMono___redArg___closed__6 = (const lean_object*)&l_Array_mapMono___redArg___closed__6_value;
static const lean_ctor_object l_Array_mapMono___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Array_mapMono___redArg___closed__0_value),((lean_object*)&l_Array_mapMono___redArg___closed__1_value)}};
static const lean_object* l_Array_mapMono___redArg___closed__7 = (const lean_object*)&l_Array_mapMono___redArg___closed__7_value;
static const lean_ctor_object l_Array_mapMono___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Array_mapMono___redArg___closed__7_value),((lean_object*)&l_Array_mapMono___redArg___closed__2_value),((lean_object*)&l_Array_mapMono___redArg___closed__3_value),((lean_object*)&l_Array_mapMono___redArg___closed__4_value),((lean_object*)&l_Array_mapMono___redArg___closed__5_value)}};
static const lean_object* l_Array_mapMono___redArg___closed__8 = (const lean_object*)&l_Array_mapMono___redArg___closed__8_value;
static const lean_ctor_object l_Array_mapMono___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Array_mapMono___redArg___closed__8_value),((lean_object*)&l_Array_mapMono___redArg___closed__6_value)}};
static const lean_object* l_Array_mapMono___redArg___closed__9 = (const lean_object*)&l_Array_mapMono___redArg___closed__9_value;
LEAN_EXPORT lean_object* l_Array_mapMono___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMono(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__List_toArrayAux_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__List_toArrayAux_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_Array_BasicAux_0__List_toArrayAux_match__1_splitter___redArg(x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_eq(x_4, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_inc_ref(x_3);
lean_inc(x_2);
lean_inc(x_4);
x_9 = lean_alloc_closure((void*)(l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___redArg___lam__0___boxed), 6, 5);
lean_closure_set(x_9, 0, x_4);
lean_closure_set(x_9, 1, x_5);
lean_closure_set(x_9, 2, x_1);
lean_closure_set(x_9, 3, x_2);
lean_closure_set(x_9, 4, x_3);
x_10 = lean_array_fget(x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
x_11 = lean_apply_1(x_2, x_10);
x_12 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_11, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_13 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_13);
lean_dec_ref(x_1);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = lean_apply_2(x_14, lean_box(0), x_5);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_add(x_1, x_7);
x_9 = lean_array_push(x_2, x_6);
x_10 = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___redArg(x_3, x_4, x_5, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___redArg(x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_array_get_size(x_3);
x_6 = lean_mk_empty_array_with_capacity(x_5);
x_7 = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___redArg(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapM_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_mapM_x27___redArg(x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_4);
x_6 = lean_nat_dec_lt(x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_7);
lean_dec_ref(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec_ref(x_7);
x_9 = lean_apply_2(x_8, lean_box(0), x_4);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_array_fget(x_4, x_3);
lean_inc(x_2);
lean_inc(x_11);
x_12 = lean_alloc_closure((void*)(l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___redArg___lam__0___boxed), 6, 5);
lean_closure_set(x_12, 0, x_11);
lean_closure_set(x_12, 1, x_3);
lean_closure_set(x_12, 2, x_4);
lean_closure_set(x_12, 3, x_1);
lean_closure_set(x_12, 4, x_2);
x_13 = lean_apply_1(x_2, x_11);
x_14 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_13, x_12);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; uint8_t x_9; 
x_7 = lean_ptr_addr(x_1);
x_8 = lean_ptr_addr(x_6);
x_9 = lean_usize_dec_eq(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_2, x_10);
x_12 = lean_array_fset(x_3, x_2, x_6);
x_13 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___redArg(x_4, x_5, x_11, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_6);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_2, x_14);
x_16 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___redArg(x_4, x_5, x_15, x_3);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___redArg(x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___redArg(x_1, x_3, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___redArg(x_3, x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapMono___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMono___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_alloc_closure((void*)(l_Array_mapMono___redArg___lam__0), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = ((lean_object*)(l_Array_mapMono___redArg___closed__9));
x_5 = lean_unsigned_to_nat(0u);
x_6 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___redArg(x_4, x_3, x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMono(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_alloc_closure((void*)(l_Array_mapMono___redArg___lam__0), 2, 1);
lean_closure_set(x_4, 0, x_3);
x_5 = ((lean_object*)(l_Array_mapMono___redArg___closed__9));
x_6 = lean_unsigned_to_nat(0u);
x_7 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___redArg(x_5, x_4, x_6, x_2);
return x_7;
}
}
lean_object* initialize_Init_Data_Array_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Set(uint8_t builtin);
lean_object* initialize_Init_Util(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Linear(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Array_BasicAux(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Set(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
