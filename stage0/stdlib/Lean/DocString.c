// Lean compiler output
// Module: Lean.DocString
// Imports: Lean.DocString.Extension Lean.Parser.Tactic.Doc
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
LEAN_EXPORT lean_object* l_Lean_findDocString_x3f(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findDocString_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_Doc_alternativeOfTactic(lean_object*, lean_object*);
lean_object* l_Lean_findSimpleDocString_x3f(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Parser_Tactic_Doc_getTacticExtensionString(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findDocString_x3f(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_2);
x_5 = l_Lean_Parser_Tactic_Doc_alternativeOfTactic(x_1, x_2);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc(x_2);
x_6 = l_Lean_Parser_Tactic_Doc_getTacticExtensionString(x_1, x_2);
x_7 = l_Lean_findSimpleDocString_x3f(x_1, x_2, x_3, x_4);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
lean_dec(x_6);
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_7, 0);
lean_dec(x_10);
x_11 = lean_box(0);
lean_ctor_set(x_7, 0, x_11);
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_7);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_7, 0);
lean_dec(x_16);
x_17 = !lean_is_exclusive(x_8);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_8, 0);
x_19 = lean_string_append(x_18, x_6);
lean_dec(x_6);
lean_ctor_set(x_8, 0, x_19);
return x_7;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_8, 0);
lean_inc(x_20);
lean_dec(x_8);
x_21 = lean_string_append(x_20, x_6);
lean_dec(x_6);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_7, 0, x_22);
return x_7;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_7, 1);
lean_inc(x_23);
lean_dec(x_7);
x_24 = lean_ctor_get(x_8, 0);
lean_inc(x_24);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 x_25 = x_8;
} else {
 lean_dec_ref(x_8);
 x_25 = lean_box(0);
}
x_26 = lean_string_append(x_24, x_6);
lean_dec(x_6);
if (lean_is_scalar(x_25)) {
 x_27 = lean_alloc_ctor(1, 1, 0);
} else {
 x_27 = x_25;
}
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_23);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_2);
x_29 = lean_ctor_get(x_5, 0);
lean_inc(x_29);
lean_dec(x_5);
lean_inc(x_29);
x_30 = l_Lean_Parser_Tactic_Doc_getTacticExtensionString(x_1, x_29);
x_31 = l_Lean_findSimpleDocString_x3f(x_1, x_29, x_3, x_4);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
lean_dec(x_30);
x_33 = !lean_is_exclusive(x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_31, 0);
lean_dec(x_34);
x_35 = lean_box(0);
lean_ctor_set(x_31, 0, x_35);
return x_31;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
lean_dec(x_31);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
else
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_31);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_31, 0);
lean_dec(x_40);
x_41 = !lean_is_exclusive(x_32);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_32, 0);
x_43 = lean_string_append(x_42, x_30);
lean_dec(x_30);
lean_ctor_set(x_32, 0, x_43);
return x_31;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_32, 0);
lean_inc(x_44);
lean_dec(x_32);
x_45 = lean_string_append(x_44, x_30);
lean_dec(x_30);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_31, 0, x_46);
return x_31;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_47 = lean_ctor_get(x_31, 1);
lean_inc(x_47);
lean_dec(x_31);
x_48 = lean_ctor_get(x_32, 0);
lean_inc(x_48);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 x_49 = x_32;
} else {
 lean_dec_ref(x_32);
 x_49 = lean_box(0);
}
x_50 = lean_string_append(x_48, x_30);
lean_dec(x_30);
if (lean_is_scalar(x_49)) {
 x_51 = lean_alloc_ctor(1, 1, 0);
} else {
 x_51 = x_49;
}
lean_ctor_set(x_51, 0, x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_47);
return x_52;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findDocString_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_3);
lean_dec(x_3);
x_6 = l_Lean_findDocString_x3f(x_1, x_2, x_5, x_4);
lean_dec(x_1);
return x_6;
}
}
lean_object* initialize_Lean_DocString_Extension(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Parser_Tactic_Doc(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_DocString(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_DocString_Extension(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Tactic_Doc(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
