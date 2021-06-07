// Lean compiler output
// Module: Init.Data.Format.Macro
// Imports: Init.Data.Format.Basic Init.Data.ToString.Macro
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
lean_object* l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__14;
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_71____spec__1(lean_object*, lean_object*);
lean_object* l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__10;
lean_object* l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__5;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__3;
extern lean_object* l_termS_x21_____closed__7;
lean_object* l_Std_termF_x21_____closed__7;
lean_object* l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__7;
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Std_termF_x21__;
lean_object* l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__13;
lean_object* l_Lean_Syntax_expandInterpolatedStr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18_(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__6;
lean_object* l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__2;
lean_object* l_Std_termF_x21_____closed__5;
lean_object* l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__11;
lean_object* l_Std_termF_x21_____closed__3;
extern lean_object* l_Lean_Parser_Syntax_addPrec___closed__10;
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__9;
lean_object* l_Std_termF_x21_____closed__4;
lean_object* l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__4;
lean_object* l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__8;
lean_object* l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__1;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Std_termF_x21_____closed__8;
lean_object* l_Std_termF_x21_____closed__2;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Std_termF_x21_____closed__1;
lean_object* l_Std_termF_x21_____closed__6;
lean_object* l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__12;
#define _init_l_Std_termF_x21_____closed__1(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_mk_string("Std");\
__INIT_VAR__ = x_1; goto l_Std_termF_x21_____closed__1_end;\
}\
l_Std_termF_x21_____closed__1_end: ((void) 0);}
#define _init_l_Std_termF_x21_____closed__2(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; lean_object* x_3; \
x_1 = lean_box(0);\
x_2 = l_Std_termF_x21_____closed__1;\
x_3 = lean_name_mk_string(x_1, x_2);\
__INIT_VAR__ = x_3; goto l_Std_termF_x21_____closed__2_end;\
}\
l_Std_termF_x21_____closed__2_end: ((void) 0);}
#define _init_l_Std_termF_x21_____closed__3(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_mk_string("termF!_");\
__INIT_VAR__ = x_1; goto l_Std_termF_x21_____closed__3_end;\
}\
l_Std_termF_x21_____closed__3_end: ((void) 0);}
#define _init_l_Std_termF_x21_____closed__4(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; lean_object* x_3; \
x_1 = l_Std_termF_x21_____closed__2;\
x_2 = l_Std_termF_x21_____closed__3;\
x_3 = lean_name_mk_string(x_1, x_2);\
__INIT_VAR__ = x_3; goto l_Std_termF_x21_____closed__4_end;\
}\
l_Std_termF_x21_____closed__4_end: ((void) 0);}
#define _init_l_Std_termF_x21_____closed__5(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_mk_string("f!");\
__INIT_VAR__ = x_1; goto l_Std_termF_x21_____closed__5_end;\
}\
l_Std_termF_x21_____closed__5_end: ((void) 0);}
#define _init_l_Std_termF_x21_____closed__6(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; \
x_1 = l_Std_termF_x21_____closed__5;\
x_2 = lean_alloc_ctor(5, 1, 0);\
lean_ctor_set(x_2, 0, x_1);\
__INIT_VAR__ = x_2; goto l_Std_termF_x21_____closed__6_end;\
}\
l_Std_termF_x21_____closed__6_end: ((void) 0);}
#define _init_l_Std_termF_x21_____closed__7(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; \
x_1 = l_Lean_Parser_Syntax_addPrec___closed__10;\
x_2 = l_Std_termF_x21_____closed__6;\
x_3 = l_termS_x21_____closed__7;\
x_4 = lean_alloc_ctor(2, 3, 0);\
lean_ctor_set(x_4, 0, x_1);\
lean_ctor_set(x_4, 1, x_2);\
lean_ctor_set(x_4, 2, x_3);\
__INIT_VAR__ = x_4; goto l_Std_termF_x21_____closed__7_end;\
}\
l_Std_termF_x21_____closed__7_end: ((void) 0);}
#define _init_l_Std_termF_x21_____closed__8(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; \
x_1 = l_Std_termF_x21_____closed__4;\
x_2 = lean_unsigned_to_nat(1024u);\
x_3 = l_Std_termF_x21_____closed__7;\
x_4 = lean_alloc_ctor(3, 3, 0);\
lean_ctor_set(x_4, 0, x_1);\
lean_ctor_set(x_4, 1, x_2);\
lean_ctor_set(x_4, 2, x_3);\
__INIT_VAR__ = x_4; goto l_Std_termF_x21_____closed__8_end;\
}\
l_Std_termF_x21_____closed__8_end: ((void) 0);}
#define _init_l_Std_termF_x21__(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = l_Std_termF_x21_____closed__8;\
__INIT_VAR__ = x_1; goto l_Std_termF_x21___end;\
}\
l_Std_termF_x21___end: ((void) 0);}
#define _init_l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__1(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_mk_string("Format");\
__INIT_VAR__ = x_1; goto l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__1_end;\
}\
l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__1_end: ((void) 0);}
#define _init_l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__2(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; \
x_1 = l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__1;\
x_2 = lean_string_utf8_byte_size(x_1);\
__INIT_VAR__ = x_2; goto l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__2_end;\
}\
l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__2_end: ((void) 0);}
#define _init_l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__3(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; \
x_1 = l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__1;\
x_2 = lean_unsigned_to_nat(0u);\
x_3 = l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__2;\
x_4 = lean_alloc_ctor(0, 3, 0);\
lean_ctor_set(x_4, 0, x_1);\
lean_ctor_set(x_4, 1, x_2);\
lean_ctor_set(x_4, 2, x_3);\
__INIT_VAR__ = x_4; goto l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__3_end;\
}\
l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__3_end: ((void) 0);}
#define _init_l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__4(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; lean_object* x_3; \
x_1 = lean_box(0);\
x_2 = l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__1;\
x_3 = lean_name_mk_string(x_1, x_2);\
__INIT_VAR__ = x_3; goto l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__4_end;\
}\
l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__4_end: ((void) 0);}
#define _init_l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__5(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; lean_object* x_3; \
x_1 = l_Std_termF_x21_____closed__2;\
x_2 = l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__1;\
x_3 = lean_name_mk_string(x_1, x_2);\
__INIT_VAR__ = x_3; goto l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__5_end;\
}\
l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__5_end: ((void) 0);}
#define _init_l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__6(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; lean_object* x_3; \
x_1 = lean_box(0);\
x_2 = l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__5;\
x_3 = lean_alloc_ctor(0, 2, 0);\
lean_ctor_set(x_3, 0, x_2);\
lean_ctor_set(x_3, 1, x_1);\
__INIT_VAR__ = x_3; goto l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__6_end;\
}\
l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__6_end: ((void) 0);}
#define _init_l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__7(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; lean_object* x_3; \
x_1 = lean_box(0);\
x_2 = l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__6;\
x_3 = lean_alloc_ctor(1, 2, 0);\
lean_ctor_set(x_3, 0, x_2);\
lean_ctor_set(x_3, 1, x_1);\
__INIT_VAR__ = x_3; goto l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__7_end;\
}\
l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__7_end: ((void) 0);}
#define _init_l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__8(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_mk_string("fmt");\
__INIT_VAR__ = x_1; goto l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__8_end;\
}\
l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__8_end: ((void) 0);}
#define _init_l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__9(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; \
x_1 = l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__8;\
x_2 = lean_string_utf8_byte_size(x_1);\
__INIT_VAR__ = x_2; goto l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__9_end;\
}\
l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__9_end: ((void) 0);}
#define _init_l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__10(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; \
x_1 = l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__8;\
x_2 = lean_unsigned_to_nat(0u);\
x_3 = l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__9;\
x_4 = lean_alloc_ctor(0, 3, 0);\
lean_ctor_set(x_4, 0, x_1);\
lean_ctor_set(x_4, 1, x_2);\
lean_ctor_set(x_4, 2, x_3);\
__INIT_VAR__ = x_4; goto l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__10_end;\
}\
l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__10_end: ((void) 0);}
#define _init_l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__11(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; lean_object* x_3; \
x_1 = lean_box(0);\
x_2 = l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__8;\
x_3 = lean_name_mk_string(x_1, x_2);\
__INIT_VAR__ = x_3; goto l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__11_end;\
}\
l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__11_end: ((void) 0);}
#define _init_l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__12(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; lean_object* x_3; \
x_1 = l_Std_termF_x21_____closed__2;\
x_2 = l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__8;\
x_3 = lean_name_mk_string(x_1, x_2);\
__INIT_VAR__ = x_3; goto l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__12_end;\
}\
l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__12_end: ((void) 0);}
#define _init_l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__13(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; lean_object* x_3; \
x_1 = lean_box(0);\
x_2 = l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__12;\
x_3 = lean_alloc_ctor(0, 2, 0);\
lean_ctor_set(x_3, 0, x_2);\
lean_ctor_set(x_3, 1, x_1);\
__INIT_VAR__ = x_3; goto l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__13_end;\
}\
l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__13_end: ((void) 0);}
#define _init_l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__14(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; lean_object* x_3; \
x_1 = lean_box(0);\
x_2 = l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__13;\
x_3 = lean_alloc_ctor(1, 2, 0);\
lean_ctor_set(x_3, 0, x_2);\
lean_ctor_set(x_3, 1, x_1);\
__INIT_VAR__ = x_3; goto l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__14_end;\
}\
l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__14_end: ((void) 0);}
lean_object* l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18_(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Std_termF_x21_____closed__4;
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
lean_dec(x_1);
x_10 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_71____spec__1(x_2, x_3);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_2, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
x_15 = l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__4;
lean_inc(x_13);
lean_inc(x_14);
x_16 = l_Lean_addMacroScope(x_14, x_15, x_13);
x_17 = l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__3;
x_18 = l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__7;
x_19 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_19, 0, x_11);
lean_ctor_set(x_19, 1, x_17);
lean_ctor_set(x_19, 2, x_16);
lean_ctor_set(x_19, 3, x_18);
x_20 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_71____spec__1(x_2, x_12);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__11;
x_24 = l_Lean_addMacroScope(x_14, x_23, x_13);
x_25 = l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__10;
x_26 = l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__14;
x_27 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_27, 0, x_21);
lean_ctor_set(x_27, 1, x_25);
lean_ctor_set(x_27, 2, x_24);
lean_ctor_set(x_27, 3, x_26);
x_28 = l_Lean_Syntax_expandInterpolatedStr(x_9, x_19, x_27, x_2, x_22);
lean_dec(x_9);
return x_28;
}
}
}
lean_object* initialize_Init_Data_Format_Basic(lean_object*);
lean_object* initialize_Init_Data_ToString_Macro(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Data_Format_Macro(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Format_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString_Macro(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
_init_l_Std_termF_x21_____closed__1(l_Std_termF_x21_____closed__1);
lean_mark_persistent(l_Std_termF_x21_____closed__1);
_init_l_Std_termF_x21_____closed__2(l_Std_termF_x21_____closed__2);
lean_mark_persistent(l_Std_termF_x21_____closed__2);
_init_l_Std_termF_x21_____closed__3(l_Std_termF_x21_____closed__3);
lean_mark_persistent(l_Std_termF_x21_____closed__3);
_init_l_Std_termF_x21_____closed__4(l_Std_termF_x21_____closed__4);
lean_mark_persistent(l_Std_termF_x21_____closed__4);
_init_l_Std_termF_x21_____closed__5(l_Std_termF_x21_____closed__5);
lean_mark_persistent(l_Std_termF_x21_____closed__5);
_init_l_Std_termF_x21_____closed__6(l_Std_termF_x21_____closed__6);
lean_mark_persistent(l_Std_termF_x21_____closed__6);
_init_l_Std_termF_x21_____closed__7(l_Std_termF_x21_____closed__7);
lean_mark_persistent(l_Std_termF_x21_____closed__7);
_init_l_Std_termF_x21_____closed__8(l_Std_termF_x21_____closed__8);
lean_mark_persistent(l_Std_termF_x21_____closed__8);
_init_l_Std_termF_x21__(l_Std_termF_x21__);
lean_mark_persistent(l_Std_termF_x21__);
_init_l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__1(l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__1);
lean_mark_persistent(l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__1);
_init_l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__2(l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__2);
lean_mark_persistent(l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__2);
_init_l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__3(l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__3);
lean_mark_persistent(l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__3);
_init_l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__4(l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__4);
lean_mark_persistent(l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__4);
_init_l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__5(l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__5);
lean_mark_persistent(l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__5);
_init_l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__6(l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__6);
lean_mark_persistent(l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__6);
_init_l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__7(l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__7);
lean_mark_persistent(l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__7);
_init_l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__8(l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__8);
lean_mark_persistent(l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__8);
_init_l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__9(l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__9);
lean_mark_persistent(l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__9);
_init_l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__10(l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__10);
lean_mark_persistent(l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__10);
_init_l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__11(l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__11);
lean_mark_persistent(l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__11);
_init_l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__12(l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__12);
lean_mark_persistent(l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__12);
_init_l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__13(l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__13);
lean_mark_persistent(l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__13);
_init_l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__14(l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__14);
lean_mark_persistent(l_Std_myMacro____x40_Init_Data_Format_Macro___hyg_18____closed__14);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
