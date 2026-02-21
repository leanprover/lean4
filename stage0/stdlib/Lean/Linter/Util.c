// Lean compiler output
// Module: Lean.Linter.Util
// Imports: public import Lean.Server.InfoUtils public import Lean.Linter.Basic
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
LEAN_EXPORT lean_object* l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___closed__0_value;
lean_object* l_id___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_id___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___closed__1 = (const lean_object*)&l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___closed__1_value;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_once_cell_t l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___closed__2;
lean_object* l_List_filterMapTR_go___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_Info_contains(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_collectMacroExpansions_x3f___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_collectMacroExpansions_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_collectMacroExpansions_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; 
x_5 = 1;
x_6 = lean_box(x_5);
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = ((lean_object*)(l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___closed__1));
x_24 = lean_obj_once(&l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___closed__2, &l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___closed__2_once, _init_l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___closed__2);
x_25 = l_List_filterMapTR_go___redArg(x_23, x_6, x_24);
x_26 = l_List_filterMapTR_go___redArg(x_23, x_25, x_24);
if (lean_obj_tag(x_26) == 1)
{
if (lean_obj_tag(x_4) == 4)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_ctor_get(x_26, 1);
lean_dec(x_29);
x_30 = !lean_is_exclusive(x_4);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_4, 0);
lean_ctor_set(x_26, 1, x_28);
lean_ctor_set(x_26, 0, x_31);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_26);
x_32 = lean_apply_2(x_1, lean_box(0), x_4);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_4, 0);
lean_inc(x_33);
lean_dec(x_4);
lean_ctor_set(x_26, 1, x_28);
lean_ctor_set(x_26, 0, x_33);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_26);
x_35 = lean_apply_2(x_1, lean_box(0), x_34);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_26, 0);
lean_inc(x_36);
lean_dec(x_26);
x_37 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_37);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 x_38 = x_4;
} else {
 lean_dec_ref(x_4);
 x_38 = lean_box(0);
}
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_36);
if (lean_is_scalar(x_38)) {
 x_40 = lean_alloc_ctor(1, 1, 0);
} else {
 x_40 = x_38;
 lean_ctor_set_tag(x_40, 1);
}
lean_ctor_set(x_40, 0, x_39);
x_41 = lean_apply_2(x_1, lean_box(0), x_40);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec_ref(x_4);
x_42 = lean_ctor_get(x_26, 0);
lean_inc(x_42);
lean_dec_ref(x_26);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_44 = lean_apply_2(x_1, lean_box(0), x_43);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_48; 
lean_dec(x_26);
x_45 = lean_ctor_get(x_2, 0);
x_46 = lean_ctor_get(x_2, 1);
x_47 = 0;
x_48 = l_Lean_Elab_Info_contains(x_4, x_45, x_47);
if (x_48 == 0)
{
x_7 = x_48;
goto block_22;
}
else
{
uint8_t x_49; 
x_49 = l_Lean_Elab_Info_contains(x_4, x_46, x_48);
x_7 = x_49;
goto block_22;
}
}
block_22:
{
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec_ref(x_4);
x_8 = lean_box(0);
x_9 = lean_apply_2(x_1, lean_box(0), x_8);
return x_9;
}
else
{
if (lean_obj_tag(x_4) == 4)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_4);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_4, 0);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_13);
x_14 = lean_apply_2(x_1, lean_box(0), x_4);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_4, 0);
lean_inc(x_15);
lean_dec(x_4);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_apply_2(x_1, lean_box(0), x_18);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec_ref(x_4);
x_20 = ((lean_object*)(l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___closed__0));
x_21 = lean_apply_2(x_1, lean_box(0), x_20);
return x_21;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
x_6 = lean_alloc_closure((void*)(l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__0___boxed), 4, 1);
lean_closure_set(x_6, 0, x_5);
lean_inc(x_5);
x_7 = lean_alloc_closure((void*)(l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___boxed), 6, 2);
lean_closure_set(x_7, 0, x_5);
lean_closure_set(x_7, 1, x_2);
x_8 = lean_box(0);
x_9 = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go(lean_box(0), lean_box(0), x_1, x_6, x_7, x_8, x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_collectMacroExpansions_x3f___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec_ref(x_2);
if (lean_obj_tag(x_6) == 1)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = l_List_reverse___redArg(x_8);
lean_ctor_set(x_6, 0, x_9);
x_10 = lean_apply_2(x_1, lean_box(0), x_6);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_6, 0);
lean_inc(x_11);
lean_dec(x_6);
x_12 = l_List_reverse___redArg(x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_apply_2(x_1, lean_box(0), x_13);
return x_14;
}
}
else
{
lean_dec(x_6);
goto block_5;
}
}
else
{
lean_dec(x_2);
goto block_5;
}
block_5:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_collectMacroExpansions_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
x_7 = l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___redArg(x_1, x_2, x_3);
x_8 = lean_alloc_closure((void*)(l_Lean_Linter_collectMacroExpansions_x3f___redArg___lam__0), 2, 1);
lean_closure_set(x_8, 0, x_6);
x_9 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_collectMacroExpansions_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Linter_collectMacroExpansions_x3f___redArg(x_2, x_3, x_4);
return x_5;
}
}
lean_object* initialize_Lean_Server_InfoUtils(uint8_t builtin);
lean_object* initialize_Lean_Linter_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Linter_Util(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Server_InfoUtils(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Linter_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
