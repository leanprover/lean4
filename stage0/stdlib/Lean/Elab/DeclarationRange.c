// Lean compiler output
// Module: Lean.Elab.DeclarationRange
// Imports: Init Lean.DeclarationRange Lean.Elab.Log Lean.Data.Lsp.Utf16
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
lean_object* l_Lean_addDeclarationRanges___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_nullKind;
static lean_object* l_Lean_Elab_getDeclarationSelectionRef___closed__8;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRanges___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_getDeclarationSelectionRef___closed__9;
static lean_object* l_Lean_Elab_getDeclarationSelectionRef___closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRanges___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_getDeclarationSelectionRef___closed__10;
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addAuxDeclarationRanges___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_getDeclarationSelectionRef___closed__6;
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addAuxDeclarationRanges(lean_object*);
static lean_object* l_Lean_Elab_addDeclarationRanges___rarg___closed__1;
static lean_object* l_Lean_Elab_addDeclarationRanges___rarg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRanges___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_setArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRanges(lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_getDeclarationSelectionRef___closed__4;
static lean_object* l_Lean_Elab_getDeclarationSelectionRef___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addAuxDeclarationRanges___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
static lean_object* l_Lean_Elab_getDeclarationSelectionRef___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_getDeclarationSelectionRef___closed__3;
lean_object* l_Lean_FileMap_leanPosToLspPos(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_getDeclarationSelectionRef___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationSelectionRef(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_4 = 0;
x_5 = l_Lean_Syntax_getPos_x3f(x_1, x_4);
x_6 = l_Lean_Syntax_getTailPos_x3f(x_1, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Lean_FileMap_toPosition(x_3, x_9);
lean_inc(x_10);
x_11 = l_Lean_FileMap_leanPosToLspPos(x_3, x_10);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
lean_inc(x_12);
lean_inc(x_10);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
lean_ctor_set(x_13, 2, x_10);
lean_ctor_set(x_13, 3, x_12);
x_14 = lean_apply_2(x_8, lean_box(0), x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_ctor_get(x_6, 0);
lean_inc(x_16);
lean_dec(x_6);
x_17 = l_Lean_FileMap_toPosition(x_3, x_16);
lean_dec(x_16);
lean_inc(x_17);
x_18 = l_Lean_FileMap_leanPosToLspPos(x_3, x_17);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_20, 0, x_10);
lean_ctor_set(x_20, 1, x_15);
lean_ctor_set(x_20, 2, x_17);
lean_ctor_set(x_20, 3, x_19);
x_21 = lean_apply_2(x_8, lean_box(0), x_20);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_2, 0);
lean_inc(x_22);
lean_dec(x_2);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_ctor_get(x_5, 0);
lean_inc(x_24);
lean_dec(x_5);
x_25 = l_Lean_FileMap_toPosition(x_3, x_24);
lean_dec(x_24);
lean_inc(x_25);
x_26 = l_Lean_FileMap_leanPosToLspPos(x_3, x_25);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
lean_inc(x_27);
lean_inc(x_25);
x_28 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set(x_28, 2, x_25);
lean_ctor_set(x_28, 3, x_27);
x_29 = lean_apply_2(x_23, lean_box(0), x_28);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_30 = lean_ctor_get(x_26, 1);
lean_inc(x_30);
lean_dec(x_26);
x_31 = lean_ctor_get(x_6, 0);
lean_inc(x_31);
lean_dec(x_6);
x_32 = l_Lean_FileMap_toPosition(x_3, x_31);
lean_dec(x_31);
lean_inc(x_32);
x_33 = l_Lean_FileMap_leanPosToLspPos(x_3, x_32);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_35, 0, x_25);
lean_ctor_set(x_35, 1, x_30);
lean_ctor_set(x_35, 2, x_32);
lean_ctor_set(x_35, 3, x_34);
x_36 = lean_apply_2(x_23, lean_box(0), x_35);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_getDeclarationRange___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_5, 0, x_3);
lean_closure_set(x_5, 1, x_1);
x_6 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_getDeclarationRange___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_getDeclarationRange___rarg___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_getDeclarationSelectionRef___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_getDeclarationSelectionRef___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_getDeclarationSelectionRef___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_getDeclarationSelectionRef___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Parser");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_getDeclarationSelectionRef___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_getDeclarationSelectionRef___closed__2;
x_2 = l_Lean_Elab_getDeclarationSelectionRef___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_getDeclarationSelectionRef___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Command");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_getDeclarationSelectionRef___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_getDeclarationSelectionRef___closed__4;
x_2 = l_Lean_Elab_getDeclarationSelectionRef___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_getDeclarationSelectionRef___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("instance");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_getDeclarationSelectionRef___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_getDeclarationSelectionRef___closed__6;
x_2 = l_Lean_Elab_getDeclarationSelectionRef___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_getDeclarationSelectionRef___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_getDeclarationSelectionRef___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_nullKind;
x_2 = l_Lean_Elab_getDeclarationSelectionRef___closed__9;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationSelectionRef(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
lean_inc(x_1);
x_2 = l_Lean_Syntax_getKind(x_1);
x_3 = l_Lean_Elab_getDeclarationSelectionRef___closed__8;
x_4 = lean_name_eq(x_2, x_3);
lean_dec(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
lean_dec(x_1);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_unsigned_to_nat(5u);
x_8 = l_Lean_Elab_getDeclarationSelectionRef___closed__10;
x_9 = l_Lean_Syntax_setArg(x_1, x_7, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRanges___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
x_6 = l_Lean_addDeclarationRanges___rarg(x_2, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRanges___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = l_Lean_Elab_getDeclarationSelectionRef(x_1);
x_9 = l_Lean_Elab_getDeclarationRange___rarg(x_2, x_3, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Elab_addDeclarationRanges___rarg___lambda__1), 4, 3);
lean_closure_set(x_10, 0, x_7);
lean_closure_set(x_10, 1, x_4);
lean_closure_set(x_10, 2, x_5);
x_11 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_9, x_10);
return x_11;
}
}
static lean_object* _init_l_Lean_Elab_addDeclarationRanges___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("example");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_addDeclarationRanges___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_getDeclarationSelectionRef___closed__6;
x_2 = l_Lean_Elab_addDeclarationRanges___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRanges___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
lean_inc(x_5);
x_6 = l_Lean_Syntax_getKind(x_5);
x_7 = l_Lean_Elab_addDeclarationRanges___rarg___closed__2;
x_8 = lean_name_eq(x_6, x_7);
lean_dec(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_1);
x_10 = l_Lean_Elab_getDeclarationRange___rarg(x_1, x_3, x_5);
lean_inc(x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_addDeclarationRanges___rarg___lambda__2), 7, 6);
lean_closure_set(x_11, 0, x_5);
lean_closure_set(x_11, 1, x_1);
lean_closure_set(x_11, 2, x_3);
lean_closure_set(x_11, 3, x_2);
lean_closure_set(x_11, 4, x_4);
lean_closure_set(x_11, 5, x_9);
x_12 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_10, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = lean_apply_2(x_14, lean_box(0), x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRanges(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_addDeclarationRanges___rarg), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addAuxDeclarationRanges___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lean_Elab_getDeclarationRange___rarg(x_1, x_2, x_3);
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_addDeclarationRanges___rarg___lambda__1), 4, 3);
lean_closure_set(x_9, 0, x_7);
lean_closure_set(x_9, 1, x_4);
lean_closure_set(x_9, 2, x_5);
x_10 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addAuxDeclarationRanges___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_inc(x_3);
lean_inc(x_1);
x_8 = l_Lean_Elab_getDeclarationRange___rarg(x_1, x_3, x_5);
lean_inc(x_7);
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_addAuxDeclarationRanges___rarg___lambda__1), 7, 6);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_3);
lean_closure_set(x_9, 2, x_6);
lean_closure_set(x_9, 3, x_2);
lean_closure_set(x_9, 4, x_4);
lean_closure_set(x_9, 5, x_7);
x_10 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addAuxDeclarationRanges(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_addAuxDeclarationRanges___rarg), 6, 0);
return x_2;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_DeclarationRange(lean_object*);
lean_object* initialize_Lean_Elab_Log(lean_object*);
lean_object* initialize_Lean_Data_Lsp_Utf16(lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_DeclarationRange(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_DeclarationRange(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Log(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp_Utf16(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_getDeclarationSelectionRef___closed__1 = _init_l_Lean_Elab_getDeclarationSelectionRef___closed__1();
lean_mark_persistent(l_Lean_Elab_getDeclarationSelectionRef___closed__1);
l_Lean_Elab_getDeclarationSelectionRef___closed__2 = _init_l_Lean_Elab_getDeclarationSelectionRef___closed__2();
lean_mark_persistent(l_Lean_Elab_getDeclarationSelectionRef___closed__2);
l_Lean_Elab_getDeclarationSelectionRef___closed__3 = _init_l_Lean_Elab_getDeclarationSelectionRef___closed__3();
lean_mark_persistent(l_Lean_Elab_getDeclarationSelectionRef___closed__3);
l_Lean_Elab_getDeclarationSelectionRef___closed__4 = _init_l_Lean_Elab_getDeclarationSelectionRef___closed__4();
lean_mark_persistent(l_Lean_Elab_getDeclarationSelectionRef___closed__4);
l_Lean_Elab_getDeclarationSelectionRef___closed__5 = _init_l_Lean_Elab_getDeclarationSelectionRef___closed__5();
lean_mark_persistent(l_Lean_Elab_getDeclarationSelectionRef___closed__5);
l_Lean_Elab_getDeclarationSelectionRef___closed__6 = _init_l_Lean_Elab_getDeclarationSelectionRef___closed__6();
lean_mark_persistent(l_Lean_Elab_getDeclarationSelectionRef___closed__6);
l_Lean_Elab_getDeclarationSelectionRef___closed__7 = _init_l_Lean_Elab_getDeclarationSelectionRef___closed__7();
lean_mark_persistent(l_Lean_Elab_getDeclarationSelectionRef___closed__7);
l_Lean_Elab_getDeclarationSelectionRef___closed__8 = _init_l_Lean_Elab_getDeclarationSelectionRef___closed__8();
lean_mark_persistent(l_Lean_Elab_getDeclarationSelectionRef___closed__8);
l_Lean_Elab_getDeclarationSelectionRef___closed__9 = _init_l_Lean_Elab_getDeclarationSelectionRef___closed__9();
lean_mark_persistent(l_Lean_Elab_getDeclarationSelectionRef___closed__9);
l_Lean_Elab_getDeclarationSelectionRef___closed__10 = _init_l_Lean_Elab_getDeclarationSelectionRef___closed__10();
lean_mark_persistent(l_Lean_Elab_getDeclarationSelectionRef___closed__10);
l_Lean_Elab_addDeclarationRanges___rarg___closed__1 = _init_l_Lean_Elab_addDeclarationRanges___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_addDeclarationRanges___rarg___closed__1);
l_Lean_Elab_addDeclarationRanges___rarg___closed__2 = _init_l_Lean_Elab_addDeclarationRanges___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_addDeclarationRanges___rarg___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
