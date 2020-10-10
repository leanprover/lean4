// Lean compiler output
// Module: Init.System.Macros
// Imports: Init.LeanInit Init.System.IO Init.Data.ToString
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
lean_object* l___kind_term____x40_Init_System_Macros___hyg_2____closed__9;
lean_object* l___kind_term____x40_Init_System_Macros___hyg_2____closed__2;
lean_object* l_myMacro____x40_Init_System_Macros___hyg_39____closed__9;
lean_object* l_myMacro____x40_Init_System_Macros___hyg_39____closed__4;
lean_object* l___kind_term____x40_Init_System_Macros___hyg_2____closed__1;
lean_object* l_myMacro____x40_Init_System_Macros___hyg_39____closed__8;
extern lean_object* l_Array_empty___closed__1;
lean_object* l___kind_term____x40_Init_System_Macros___hyg_2____closed__5;
lean_object* l_myMacro____x40_Init_System_Macros___hyg_39____closed__6;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_myMacro____x40_Init_System_Macros___hyg_39____closed__11;
lean_object* l___kind_term____x40_Init_System_Macros___hyg_2____closed__8;
extern lean_object* l_myMacro____x40_Init_Data_ToString_Macro___hyg_39____closed__6;
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l___kind_term____x40_Init_System_Macros___hyg_2____closed__4;
extern lean_object* l_Lean_mkAppStx___closed__8;
lean_object* l_myMacro____x40_Init_System_Macros___hyg_39____closed__1;
lean_object* l_myMacro____x40_Init_System_Macros___hyg_39____closed__2;
lean_object* l_myMacro____x40_Init_System_Macros___hyg_39_(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l___kind_term____x40_Init_System_Macros___hyg_2____closed__3;
lean_object* l___kind_term____x40_Init_System_Macros___hyg_2____closed__6;
lean_object* l_myMacro____x40_Init_System_Macros___hyg_39____closed__7;
extern lean_object* l_myMacro____x40_Init_Data_ToString_Macro___hyg_39____closed__15;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l___kind_term____x40_Init_System_Macros___hyg_2____closed__10;
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_nullKind___closed__2;
lean_object* l___kind_term____x40_Init_System_Macros___hyg_2____closed__7;
lean_object* l___kind_term____x40_Init_System_Macros___hyg_2_;
extern lean_object* l_Lean_SourceInfo_inhabited___closed__1;
lean_object* l_myMacro____x40_Init_System_Macros___hyg_39____closed__5;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_myMacro____x40_Init_System_Macros___hyg_39____closed__3;
extern lean_object* l___kind_term____x40_Init_Data_ToString_Macro___hyg_2____closed__15;
lean_object* l_myMacro____x40_Init_System_Macros___hyg_39____closed__10;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_myMacro____x40_Init_System_Macros___hyg_39____closed__12;
extern lean_object* l_myMacro____x40_Init_Data_ToString_Macro___hyg_39____closed__4;
extern lean_object* l___kind_term____x40_Init_Data_ToString_Macro___hyg_2____closed__7;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Name_hasMacroScopes___main___closed__1;
extern lean_object* l___kind_term____x40_Init_Data_ToString_Macro___hyg_2____closed__20;
lean_object* lean_name_mk_numeral(lean_object*, lean_object*);
extern lean_object* l___kind_term____x40_Init_Data_ToString_Macro___hyg_2____closed__16;
lean_object* _init_l___kind_term____x40_Init_System_Macros___hyg_2____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("System");
return x_1;
}
}
lean_object* _init_l___kind_term____x40_Init_System_Macros___hyg_2____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___kind_term____x40_Init_Data_ToString_Macro___hyg_2____closed__7;
x_2 = l___kind_term____x40_Init_System_Macros___hyg_2____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___kind_term____x40_Init_System_Macros___hyg_2____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Macros");
return x_1;
}
}
lean_object* _init_l___kind_term____x40_Init_System_Macros___hyg_2____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___kind_term____x40_Init_System_Macros___hyg_2____closed__2;
x_2 = l___kind_term____x40_Init_System_Macros___hyg_2____closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___kind_term____x40_Init_System_Macros___hyg_2____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___kind_term____x40_Init_System_Macros___hyg_2____closed__4;
x_2 = l_Lean_Name_hasMacroScopes___main___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___kind_term____x40_Init_System_Macros___hyg_2____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___kind_term____x40_Init_System_Macros___hyg_2____closed__5;
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_name_mk_numeral(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___kind_term____x40_Init_System_Macros___hyg_2____closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("println!");
return x_1;
}
}
lean_object* _init_l___kind_term____x40_Init_System_Macros___hyg_2____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___kind_term____x40_Init_System_Macros___hyg_2____closed__7;
x_2 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___kind_term____x40_Init_System_Macros___hyg_2____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___kind_term____x40_Init_System_Macros___hyg_2____closed__8;
x_2 = l___kind_term____x40_Init_Data_ToString_Macro___hyg_2____closed__20;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___kind_term____x40_Init_System_Macros___hyg_2____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___kind_term____x40_Init_System_Macros___hyg_2____closed__6;
x_2 = lean_unsigned_to_nat(1023u);
x_3 = l___kind_term____x40_Init_System_Macros___hyg_2____closed__9;
x_4 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l___kind_term____x40_Init_System_Macros___hyg_2_() {
_start:
{
lean_object* x_1; 
x_1 = l___kind_term____x40_Init_System_Macros___hyg_2____closed__10;
return x_1;
}
}
lean_object* _init_l_myMacro____x40_Init_System_Macros___hyg_39____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("IO.println");
return x_1;
}
}
lean_object* _init_l_myMacro____x40_Init_System_Macros___hyg_39____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_myMacro____x40_Init_System_Macros___hyg_39____closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
lean_object* _init_l_myMacro____x40_Init_System_Macros___hyg_39____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_myMacro____x40_Init_System_Macros___hyg_39____closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_myMacro____x40_Init_System_Macros___hyg_39____closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l_myMacro____x40_Init_System_Macros___hyg_39____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("IO");
return x_1;
}
}
lean_object* _init_l_myMacro____x40_Init_System_Macros___hyg_39____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_myMacro____x40_Init_System_Macros___hyg_39____closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_myMacro____x40_Init_System_Macros___hyg_39____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("println");
return x_1;
}
}
lean_object* _init_l_myMacro____x40_Init_System_Macros___hyg_39____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_myMacro____x40_Init_System_Macros___hyg_39____closed__5;
x_2 = l_myMacro____x40_Init_System_Macros___hyg_39____closed__6;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_myMacro____x40_Init_System_Macros___hyg_39____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_myMacro____x40_Init_System_Macros___hyg_39____closed__7;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* _init_l_myMacro____x40_Init_System_Macros___hyg_39____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_myMacro____x40_Init_System_Macros___hyg_39____closed__8;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* _init_l_myMacro____x40_Init_System_Macros___hyg_39____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SourceInfo_inhabited___closed__1;
x_2 = l___kind_term____x40_Init_Data_ToString_Macro___hyg_2____closed__16;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_myMacro____x40_Init_System_Macros___hyg_39____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_myMacro____x40_Init_System_Macros___hyg_39____closed__10;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_myMacro____x40_Init_System_Macros___hyg_39____closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_nullKind___closed__2;
x_2 = l_Array_empty___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_myMacro____x40_Init_System_Macros___hyg_39_(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l___kind_term____x40_Init_System_Macros___hyg_2____closed__6;
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = l_Lean_Syntax_getArgs(x_1);
x_9 = lean_array_get_size(x_8);
lean_dec(x_8);
x_10 = lean_unsigned_to_nat(2u);
x_11 = lean_nat_dec_eq(x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_box(1);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
lean_dec(x_1);
x_16 = lean_ctor_get(x_2, 2);
lean_inc(x_16);
x_17 = lean_ctor_get(x_2, 1);
lean_inc(x_17);
lean_dec(x_2);
x_18 = l_myMacro____x40_Init_System_Macros___hyg_39____closed__7;
x_19 = l_Lean_addMacroScope(x_17, x_18, x_16);
x_20 = l_Lean_SourceInfo_inhabited___closed__1;
x_21 = l_myMacro____x40_Init_System_Macros___hyg_39____closed__3;
x_22 = l_myMacro____x40_Init_System_Macros___hyg_39____closed__9;
x_23 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_21);
lean_ctor_set(x_23, 2, x_19);
lean_ctor_set(x_23, 3, x_22);
x_24 = l_Array_empty___closed__1;
x_25 = lean_array_push(x_24, x_23);
x_26 = l_myMacro____x40_Init_System_Macros___hyg_39____closed__11;
x_27 = lean_array_push(x_26, x_15);
x_28 = l___kind_term____x40_Init_Data_ToString_Macro___hyg_2____closed__15;
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = lean_array_push(x_24, x_29);
x_31 = l_myMacro____x40_Init_System_Macros___hyg_39____closed__12;
x_32 = lean_array_push(x_30, x_31);
x_33 = l_Lean_nullKind___closed__2;
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
x_35 = l_myMacro____x40_Init_Data_ToString_Macro___hyg_39____closed__6;
x_36 = lean_array_push(x_35, x_34);
x_37 = l_myMacro____x40_Init_Data_ToString_Macro___hyg_39____closed__15;
x_38 = lean_array_push(x_36, x_37);
x_39 = l_myMacro____x40_Init_Data_ToString_Macro___hyg_39____closed__4;
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
x_41 = lean_array_push(x_24, x_40);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_33);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_array_push(x_25, x_42);
x_44 = l_Lean_mkAppStx___closed__8;
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_3);
return x_46;
}
}
}
}
lean_object* initialize_Init_LeanInit(lean_object*);
lean_object* initialize_Init_System_IO(lean_object*);
lean_object* initialize_Init_Data_ToString(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_System_Macros(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_LeanInit(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_IO(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___kind_term____x40_Init_System_Macros___hyg_2____closed__1 = _init_l___kind_term____x40_Init_System_Macros___hyg_2____closed__1();
lean_mark_persistent(l___kind_term____x40_Init_System_Macros___hyg_2____closed__1);
l___kind_term____x40_Init_System_Macros___hyg_2____closed__2 = _init_l___kind_term____x40_Init_System_Macros___hyg_2____closed__2();
lean_mark_persistent(l___kind_term____x40_Init_System_Macros___hyg_2____closed__2);
l___kind_term____x40_Init_System_Macros___hyg_2____closed__3 = _init_l___kind_term____x40_Init_System_Macros___hyg_2____closed__3();
lean_mark_persistent(l___kind_term____x40_Init_System_Macros___hyg_2____closed__3);
l___kind_term____x40_Init_System_Macros___hyg_2____closed__4 = _init_l___kind_term____x40_Init_System_Macros___hyg_2____closed__4();
lean_mark_persistent(l___kind_term____x40_Init_System_Macros___hyg_2____closed__4);
l___kind_term____x40_Init_System_Macros___hyg_2____closed__5 = _init_l___kind_term____x40_Init_System_Macros___hyg_2____closed__5();
lean_mark_persistent(l___kind_term____x40_Init_System_Macros___hyg_2____closed__5);
l___kind_term____x40_Init_System_Macros___hyg_2____closed__6 = _init_l___kind_term____x40_Init_System_Macros___hyg_2____closed__6();
lean_mark_persistent(l___kind_term____x40_Init_System_Macros___hyg_2____closed__6);
l___kind_term____x40_Init_System_Macros___hyg_2____closed__7 = _init_l___kind_term____x40_Init_System_Macros___hyg_2____closed__7();
lean_mark_persistent(l___kind_term____x40_Init_System_Macros___hyg_2____closed__7);
l___kind_term____x40_Init_System_Macros___hyg_2____closed__8 = _init_l___kind_term____x40_Init_System_Macros___hyg_2____closed__8();
lean_mark_persistent(l___kind_term____x40_Init_System_Macros___hyg_2____closed__8);
l___kind_term____x40_Init_System_Macros___hyg_2____closed__9 = _init_l___kind_term____x40_Init_System_Macros___hyg_2____closed__9();
lean_mark_persistent(l___kind_term____x40_Init_System_Macros___hyg_2____closed__9);
l___kind_term____x40_Init_System_Macros___hyg_2____closed__10 = _init_l___kind_term____x40_Init_System_Macros___hyg_2____closed__10();
lean_mark_persistent(l___kind_term____x40_Init_System_Macros___hyg_2____closed__10);
l___kind_term____x40_Init_System_Macros___hyg_2_ = _init_l___kind_term____x40_Init_System_Macros___hyg_2_();
lean_mark_persistent(l___kind_term____x40_Init_System_Macros___hyg_2_);
l_myMacro____x40_Init_System_Macros___hyg_39____closed__1 = _init_l_myMacro____x40_Init_System_Macros___hyg_39____closed__1();
lean_mark_persistent(l_myMacro____x40_Init_System_Macros___hyg_39____closed__1);
l_myMacro____x40_Init_System_Macros___hyg_39____closed__2 = _init_l_myMacro____x40_Init_System_Macros___hyg_39____closed__2();
lean_mark_persistent(l_myMacro____x40_Init_System_Macros___hyg_39____closed__2);
l_myMacro____x40_Init_System_Macros___hyg_39____closed__3 = _init_l_myMacro____x40_Init_System_Macros___hyg_39____closed__3();
lean_mark_persistent(l_myMacro____x40_Init_System_Macros___hyg_39____closed__3);
l_myMacro____x40_Init_System_Macros___hyg_39____closed__4 = _init_l_myMacro____x40_Init_System_Macros___hyg_39____closed__4();
lean_mark_persistent(l_myMacro____x40_Init_System_Macros___hyg_39____closed__4);
l_myMacro____x40_Init_System_Macros___hyg_39____closed__5 = _init_l_myMacro____x40_Init_System_Macros___hyg_39____closed__5();
lean_mark_persistent(l_myMacro____x40_Init_System_Macros___hyg_39____closed__5);
l_myMacro____x40_Init_System_Macros___hyg_39____closed__6 = _init_l_myMacro____x40_Init_System_Macros___hyg_39____closed__6();
lean_mark_persistent(l_myMacro____x40_Init_System_Macros___hyg_39____closed__6);
l_myMacro____x40_Init_System_Macros___hyg_39____closed__7 = _init_l_myMacro____x40_Init_System_Macros___hyg_39____closed__7();
lean_mark_persistent(l_myMacro____x40_Init_System_Macros___hyg_39____closed__7);
l_myMacro____x40_Init_System_Macros___hyg_39____closed__8 = _init_l_myMacro____x40_Init_System_Macros___hyg_39____closed__8();
lean_mark_persistent(l_myMacro____x40_Init_System_Macros___hyg_39____closed__8);
l_myMacro____x40_Init_System_Macros___hyg_39____closed__9 = _init_l_myMacro____x40_Init_System_Macros___hyg_39____closed__9();
lean_mark_persistent(l_myMacro____x40_Init_System_Macros___hyg_39____closed__9);
l_myMacro____x40_Init_System_Macros___hyg_39____closed__10 = _init_l_myMacro____x40_Init_System_Macros___hyg_39____closed__10();
lean_mark_persistent(l_myMacro____x40_Init_System_Macros___hyg_39____closed__10);
l_myMacro____x40_Init_System_Macros___hyg_39____closed__11 = _init_l_myMacro____x40_Init_System_Macros___hyg_39____closed__11();
lean_mark_persistent(l_myMacro____x40_Init_System_Macros___hyg_39____closed__11);
l_myMacro____x40_Init_System_Macros___hyg_39____closed__12 = _init_l_myMacro____x40_Init_System_Macros___hyg_39____closed__12();
lean_mark_persistent(l_myMacro____x40_Init_System_Macros___hyg_39____closed__12);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
