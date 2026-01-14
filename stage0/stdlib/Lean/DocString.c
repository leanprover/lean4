// Lean compiler output
// Module: Lean.DocString
// Imports: public import Lean.DocString.Extension public import Lean.DocString.Links public import Lean.Parser.Tactic.Doc public import Lean.Parser.Term.Doc
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
LEAN_EXPORT lean_object* l_Lean_findDocString_x3f(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_findDocString_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_Doc_alternativeOfTactic(lean_object*, lean_object*);
lean_object* l_Lean_findSimpleDocString_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Parser_Tactic_Doc_getTacticExtensionString(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_Doc_getRecommendedSpellingString(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_rewriteManualLinks(lean_object*);
LEAN_EXPORT lean_object* l_Lean_findDocString_x3f(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_5; lean_object* x_30; 
lean_inc(x_2);
lean_inc_ref(x_1);
x_30 = l_Lean_Parser_Tactic_Doc_alternativeOfTactic(x_1, x_2);
if (lean_obj_tag(x_30) == 0)
{
x_5 = x_2;
goto block_29;
}
else
{
lean_object* x_31; 
lean_dec(x_2);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec_ref(x_30);
x_5 = x_31;
goto block_29;
}
block_29:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc(x_5);
lean_inc_ref(x_1);
x_6 = l_Lean_Parser_Tactic_Doc_getTacticExtensionString(x_1, x_5);
lean_inc(x_5);
lean_inc_ref(x_1);
x_7 = l_Lean_Parser_Term_Doc_getRecommendedSpellingString(x_1, x_5);
x_8 = l_Lean_findSimpleDocString_x3f(x_1, x_5, x_3);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_dec_ref(x_7);
lean_dec_ref(x_6);
return x_8;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_8, 0);
lean_dec(x_11);
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = lean_string_append(x_13, x_6);
lean_dec_ref(x_6);
x_15 = lean_string_append(x_14, x_7);
lean_dec_ref(x_7);
x_16 = l_Lean_rewriteManualLinks(x_15);
lean_ctor_set(x_9, 0, x_16);
return x_8;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_9, 0);
lean_inc(x_17);
lean_dec(x_9);
x_18 = lean_string_append(x_17, x_6);
lean_dec_ref(x_6);
x_19 = lean_string_append(x_18, x_7);
lean_dec_ref(x_7);
x_20 = l_Lean_rewriteManualLinks(x_19);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_8, 0, x_21);
return x_8;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_8);
x_22 = lean_ctor_get(x_9, 0);
lean_inc(x_22);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 x_23 = x_9;
} else {
 lean_dec_ref(x_9);
 x_23 = lean_box(0);
}
x_24 = lean_string_append(x_22, x_6);
lean_dec_ref(x_6);
x_25 = lean_string_append(x_24, x_7);
lean_dec_ref(x_7);
x_26 = l_Lean_rewriteManualLinks(x_25);
if (lean_is_scalar(x_23)) {
 x_27 = lean_alloc_ctor(1, 1, 0);
} else {
 x_27 = x_23;
}
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
}
else
{
lean_dec_ref(x_7);
lean_dec_ref(x_6);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findDocString_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_3);
x_6 = l_Lean_findDocString_x3f(x_1, x_2, x_5);
return x_6;
}
}
lean_object* initialize_Lean_DocString_Extension(uint8_t builtin);
lean_object* initialize_Lean_DocString_Links(uint8_t builtin);
lean_object* initialize_Lean_Parser_Tactic_Doc(uint8_t builtin);
lean_object* initialize_Lean_Parser_Term_Doc(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_DocString(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_DocString_Extension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_DocString_Links(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Tactic_Doc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Term_Doc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
