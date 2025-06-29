// Lean compiler output
// Module: Lean.Linter.Util
// Imports: Lean.Data.Options Lean.Server.InfoUtils Lean.Linter.Basic
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_collectMacroExpansions_x3f___redArg___lam__0(lean_object*, lean_object*);
static lean_object* l_Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Linter_collectMacroExpansions_x3f_go(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_collectMacroExpansions_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___closed__2;
lean_object* l_List_filterMapTR_go___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_collectMacroExpansions_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___closed__0;
LEAN_EXPORT lean_object* l_Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_InfoTree_visitM_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_collectMacroExpansions_x3f_go___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_Info_contains(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(1);
x_6 = lean_apply_2(x_1, lean_box(0), x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_id___boxed), 2, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = l_Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___closed__1;
x_24 = l_Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___closed__2;
x_25 = l_List_filterMapTR_go___redArg(x_23, x_6, x_24);
x_26 = l_List_filterMapTR_go___redArg(x_23, x_25, x_24);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_31; 
x_27 = lean_ctor_get(x_1, 0);
x_28 = lean_ctor_get(x_1, 1);
x_29 = lean_box(0);
x_30 = lean_unbox(x_29);
x_31 = l_Lean_Elab_Info_contains(x_4, x_27, x_30);
if (x_31 == 0)
{
x_7 = x_31;
goto block_22;
}
else
{
uint8_t x_32; 
x_32 = l_Lean_Elab_Info_contains(x_4, x_28, x_31);
x_7 = x_32;
goto block_22;
}
}
else
{
if (lean_obj_tag(x_4) == 4)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_26);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = lean_ctor_get(x_26, 0);
x_35 = lean_ctor_get(x_26, 1);
lean_dec(x_35);
x_36 = !lean_is_exclusive(x_4);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_4, 0);
lean_ctor_set(x_26, 1, x_34);
lean_ctor_set(x_26, 0, x_37);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_26);
x_38 = lean_apply_2(x_2, lean_box(0), x_4);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_4, 0);
lean_inc(x_39);
lean_dec(x_4);
lean_ctor_set(x_26, 1, x_34);
lean_ctor_set(x_26, 0, x_39);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_26);
x_41 = lean_apply_2(x_2, lean_box(0), x_40);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_42 = lean_ctor_get(x_26, 0);
lean_inc(x_42);
lean_dec(x_26);
x_43 = lean_ctor_get(x_4, 0);
lean_inc(x_43);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 x_44 = x_4;
} else {
 lean_dec_ref(x_4);
 x_44 = lean_box(0);
}
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_42);
if (lean_is_scalar(x_44)) {
 x_46 = lean_alloc_ctor(1, 1, 0);
} else {
 x_46 = x_44;
 lean_ctor_set_tag(x_46, 1);
}
lean_ctor_set(x_46, 0, x_45);
x_47 = lean_apply_2(x_2, lean_box(0), x_46);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_4);
x_48 = lean_ctor_get(x_26, 0);
lean_inc(x_48);
lean_dec(x_26);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_50 = lean_apply_2(x_2, lean_box(0), x_49);
return x_50;
}
}
block_22:
{
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
x_8 = lean_box(0);
x_9 = lean_apply_2(x_2, lean_box(0), x_8);
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
x_14 = lean_apply_2(x_2, lean_box(0), x_4);
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
x_19 = lean_apply_2(x_2, lean_box(0), x_18);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_4);
x_20 = l_Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___closed__0;
x_21 = lean_apply_2(x_2, lean_box(0), x_20);
return x_21;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_collectMacroExpansions_x3f_go___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
lean_inc(x_5);
x_6 = lean_alloc_closure((void*)(l_Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__0___boxed), 4, 1);
lean_closure_set(x_6, 0, x_5);
x_7 = lean_alloc_closure((void*)(l_Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___boxed), 6, 2);
lean_closure_set(x_7, 0, x_2);
lean_closure_set(x_7, 1, x_5);
x_8 = lean_box(0);
x_9 = l_Lean_Elab_InfoTree_visitM_go___redArg(x_1, x_6, x_7, x_8, x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_collectMacroExpansions_x3f_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Linter_collectMacroExpansions_x3f_go___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_collectMacroExpansions_x3f___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
goto block_5;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
if (lean_obj_tag(x_6) == 0)
{
goto block_5;
}
else
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
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_Lean_Linter_collectMacroExpansions_x3f_go___redArg(x_1, x_2, x_3);
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
lean_object* initialize_Lean_Data_Options(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Server_InfoUtils(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Linter_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Linter_Util(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Options(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_InfoUtils(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Linter_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___closed__0 = _init_l_Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___closed__0();
lean_mark_persistent(l_Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___closed__0);
l_Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___closed__1 = _init_l_Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___closed__1();
lean_mark_persistent(l_Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___closed__1);
l_Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___closed__2 = _init_l_Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___closed__2();
lean_mark_persistent(l_Lean_Linter_collectMacroExpansions_x3f_go___redArg___lam__1___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
