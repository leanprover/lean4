// Lean compiler output
// Module: Lean.DocString.Add
// Imports: Lean.Environment Lean.Exception Lean.Log Lean.DocString.Extension Lean.DocString.Links
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
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_logError___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDocString___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
lean_object* l_String_removeLeadingSpaces(lean_object*);
lean_object* l_Lean_rewriteManualLinksCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_validateDocComment___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_validateDocComment___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_validateDocComment(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDocString___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addDocString___redArg___lam__5___closed__1;
LEAN_EXPORT lean_object* l_Lean_addDocString___redArg___lam__6___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDocString___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_validateDocComment___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_validateDocComment___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_validateDocComment___redArg___lam__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addDocString___redArg___lam__5___closed__0;
LEAN_EXPORT lean_object* l_Lean_addDocString_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_docStringExt;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_validateDocComment___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getDocString(lean_object*);
LEAN_EXPORT lean_object* l_Lean_validateDocComment___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_addDocString___redArg___lam__6(uint8_t, lean_object*);
lean_object* l_Lean_logErrorAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_getPos_x3f(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_validateDocComment___redArg___lam__0(lean_object*, lean_object*);
lean_object* l_Lean_getDocStringText___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDocString(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDocString___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forIn_x27Unsafe_loop___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDocString___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getHeadInfo_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDocString___redArg___lam__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDocString___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_validateDocComment___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDocString___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
static lean_object* l_Lean_addDocString___redArg___lam__0___closed__0;
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDocString___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_validateDocComment___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDocString_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDocString___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_validateDocComment___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_validateDocComment___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_rewriteManualLinksCore(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_validateDocComment___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_1);
x_5 = lean_apply_2(x_2, lean_box(0), x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_validateDocComment___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_13);
lean_dec(x_9);
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = l_Lean_MessageData_ofFormat(x_15);
x_17 = l_Lean_logError___redArg(x_2, x_3, x_4, x_5, x_16);
x_18 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_17, x_7);
return x_18;
}
else
{
lean_object* x_19; uint8_t x_20; 
lean_dec(x_7);
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_dec(x_10);
x_20 = !lean_is_exclusive(x_13);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_1);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_22 = lean_ctor_get(x_13, 0);
x_23 = lean_ctor_get(x_13, 1);
x_24 = lean_ctor_get(x_1, 0);
x_25 = lean_nat_add(x_24, x_22);
x_26 = lean_nat_add(x_24, x_23);
lean_dec(x_24);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_26);
x_29 = lean_unbox(x_27);
lean_ctor_set_uint8(x_28, sizeof(void*)*2, x_29);
x_30 = lean_string_utf8_extract(x_8, x_22, x_23);
lean_dec(x_23);
lean_dec(x_22);
lean_ctor_set_tag(x_13, 2);
lean_ctor_set(x_13, 1, x_30);
lean_ctor_set(x_13, 0, x_28);
lean_ctor_set_tag(x_1, 3);
lean_ctor_set(x_1, 0, x_19);
x_31 = l_Lean_MessageData_ofFormat(x_1);
x_32 = l_Lean_logErrorAt___redArg(x_2, x_3, x_4, x_5, x_13, x_31);
x_33 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_32, x_9);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_34 = lean_ctor_get(x_13, 0);
x_35 = lean_ctor_get(x_13, 1);
x_36 = lean_ctor_get(x_1, 0);
lean_inc(x_36);
lean_dec(x_1);
x_37 = lean_nat_add(x_36, x_34);
x_38 = lean_nat_add(x_36, x_35);
lean_dec(x_36);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_38);
x_41 = lean_unbox(x_39);
lean_ctor_set_uint8(x_40, sizeof(void*)*2, x_41);
x_42 = lean_string_utf8_extract(x_8, x_34, x_35);
lean_dec(x_35);
lean_dec(x_34);
lean_ctor_set_tag(x_13, 2);
lean_ctor_set(x_13, 1, x_42);
lean_ctor_set(x_13, 0, x_40);
x_43 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_43, 0, x_19);
x_44 = l_Lean_MessageData_ofFormat(x_43);
x_45 = l_Lean_logErrorAt___redArg(x_2, x_3, x_4, x_5, x_13, x_44);
x_46 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_45, x_9);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_47 = lean_ctor_get(x_13, 0);
x_48 = lean_ctor_get(x_13, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_13);
x_49 = lean_ctor_get(x_1, 0);
lean_inc(x_49);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_50 = x_1;
} else {
 lean_dec_ref(x_1);
 x_50 = lean_box(0);
}
x_51 = lean_nat_add(x_49, x_47);
x_52 = lean_nat_add(x_49, x_48);
lean_dec(x_49);
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_54, 0, x_51);
lean_ctor_set(x_54, 1, x_52);
x_55 = lean_unbox(x_53);
lean_ctor_set_uint8(x_54, sizeof(void*)*2, x_55);
x_56 = lean_string_utf8_extract(x_8, x_47, x_48);
lean_dec(x_48);
lean_dec(x_47);
x_57 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_56);
if (lean_is_scalar(x_50)) {
 x_58 = lean_alloc_ctor(3, 1, 0);
} else {
 x_58 = x_50;
 lean_ctor_set_tag(x_58, 3);
}
lean_ctor_set(x_58, 0, x_19);
x_59 = l_Lean_MessageData_ofFormat(x_58);
x_60 = l_Lean_logErrorAt___redArg(x_2, x_3, x_4, x_5, x_57, x_59);
x_61 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_60, x_9);
return x_61;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_validateDocComment___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, lean_box(0), x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_validateDocComment___redArg___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_box(0);
lean_inc(x_1);
x_12 = lean_alloc_closure((void*)(l_Lean_validateDocComment___redArg___lam__1___boxed), 3, 2);
lean_closure_set(x_12, 0, x_11);
lean_closure_set(x_12, 1, x_1);
lean_inc(x_12);
lean_inc(x_7);
lean_inc(x_3);
x_13 = lean_alloc_closure((void*)(l_Lean_validateDocComment___redArg___lam__3___boxed), 12, 9);
lean_closure_set(x_13, 0, x_2);
lean_closure_set(x_13, 1, x_3);
lean_closure_set(x_13, 2, x_4);
lean_closure_set(x_13, 3, x_5);
lean_closure_set(x_13, 4, x_6);
lean_closure_set(x_13, 5, x_7);
lean_closure_set(x_13, 6, x_12);
lean_closure_set(x_13, 7, x_8);
lean_closure_set(x_13, 8, x_12);
x_14 = lean_alloc_closure((void*)(l_Lean_validateDocComment___redArg___lam__2___boxed), 3, 2);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_11);
x_15 = lean_array_size(x_10);
x_16 = 0;
x_17 = l_Array_forIn_x27Unsafe_loop___redArg(x_3, x_10, x_13, x_15, x_16, x_11);
x_18 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_17, x_14);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_validateDocComment___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_TSyntax_getDocString(x_6);
lean_inc(x_10);
x_11 = lean_alloc_closure((void*)(l_Lean_validateDocComment___redArg___lam__0), 2, 1);
lean_closure_set(x_11, 0, x_10);
x_17 = lean_unsigned_to_nat(1u);
x_18 = l_Lean_Syntax_getArg(x_6, x_17);
x_19 = l_Lean_Syntax_getHeadInfo_x3f(x_18);
lean_dec(x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_box(0);
x_12 = x_20;
goto block_16;
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_box(0);
x_23 = lean_unbox(x_22);
x_24 = l_Lean_SourceInfo_getPos_x3f(x_21, x_23);
lean_dec(x_21);
x_12 = x_24;
goto block_16;
}
block_16:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_inc(x_8);
x_13 = lean_alloc_closure((void*)(l_Lean_validateDocComment___redArg___lam__4), 9, 8);
lean_closure_set(x_13, 0, x_9);
lean_closure_set(x_13, 1, x_12);
lean_closure_set(x_13, 2, x_1);
lean_closure_set(x_13, 3, x_2);
lean_closure_set(x_13, 4, x_3);
lean_closure_set(x_13, 5, x_4);
lean_closure_set(x_13, 6, x_8);
lean_closure_set(x_13, 7, x_10);
x_14 = lean_apply_2(x_5, lean_box(0), x_11);
x_15 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_14, x_13);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_validateDocComment(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_validateDocComment___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_validateDocComment___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_validateDocComment___redArg___lam__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_validateDocComment___redArg___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_validateDocComment___redArg___lam__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec(x_8);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_validateDocComment___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_validateDocComment___redArg___lam__2(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_validateDocComment___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_validateDocComment___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_validateDocComment___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_validateDocComment(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
return x_8;
}
}
static lean_object* _init_l_Lean_addDocString___redArg___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_docStringExt;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Lean_addDocString___redArg___lam__0___closed__0;
x_5 = l_String_removeLeadingSpaces(x_1);
x_6 = l_Lean_MapDeclarationExtension_insert___redArg(x_4, x_3, x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_Lean_addDocString___redArg___lam__0), 3, 2);
lean_closure_set(x_4, 0, x_3);
lean_closure_set(x_4, 1, x_1);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_getDocStringText___redArg(x_1, x_2, x_3);
x_8 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_7, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_validateDocComment___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
x_11 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_10, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString___redArg___lam__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_addDocString___redArg___lam__6(uint8_t x_1, lean_object* x_2) {
_start:
{
return x_1;
}
}
static lean_object* _init_l_Lean_addDocString___redArg___lam__5___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid doc string, declaration '", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Lean_addDocString___redArg___lam__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' is in an imported module", 26, 26);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString___redArg___lam__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Environment_getModuleIdxFor_x3f(x_8, x_1);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_box(0);
x_12 = lean_apply_2(x_10, lean_box(0), x_11);
x_13 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_12, x_4);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_4);
lean_dec(x_2);
x_14 = !lean_is_exclusive(x_9);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_15 = lean_ctor_get(x_9, 0);
lean_dec(x_15);
x_16 = lean_box(0);
x_17 = lean_alloc_closure((void*)(l_Lean_addDocString___redArg___lam__6___boxed), 2, 1);
lean_closure_set(x_17, 0, x_16);
x_18 = l_Lean_addDocString___redArg___lam__5___closed__0;
x_19 = lean_box(1);
x_20 = lean_unbox(x_19);
x_21 = l_Lean_Name_toString(x_1, x_20, x_17);
x_22 = lean_string_append(x_18, x_21);
lean_dec(x_21);
x_23 = l_Lean_addDocString___redArg___lam__5___closed__1;
x_24 = lean_string_append(x_22, x_23);
lean_ctor_set_tag(x_9, 3);
lean_ctor_set(x_9, 0, x_24);
x_25 = l_Lean_MessageData_ofFormat(x_9);
x_26 = l_Lean_throwError___redArg(x_5, x_6, x_25);
x_27 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_26, x_7);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_9);
x_28 = lean_box(0);
x_29 = lean_alloc_closure((void*)(l_Lean_addDocString___redArg___lam__6___boxed), 2, 1);
lean_closure_set(x_29, 0, x_28);
x_30 = l_Lean_addDocString___redArg___lam__5___closed__0;
x_31 = lean_box(1);
x_32 = lean_unbox(x_31);
x_33 = l_Lean_Name_toString(x_1, x_32, x_29);
x_34 = lean_string_append(x_30, x_33);
lean_dec(x_33);
x_35 = l_Lean_addDocString___redArg___lam__5___closed__1;
x_36 = lean_string_append(x_34, x_35);
x_37 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = l_Lean_MessageData_ofFormat(x_37);
x_39 = l_Lean_throwError___redArg(x_5, x_6, x_38);
x_40 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_39, x_7);
return x_40;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
lean_dec(x_3);
lean_inc(x_8);
x_14 = lean_alloc_closure((void*)(l_Lean_addDocString___redArg___lam__1), 3, 2);
lean_closure_set(x_14, 0, x_8);
lean_closure_set(x_14, 1, x_13);
lean_inc(x_11);
lean_inc(x_9);
lean_inc(x_2);
lean_inc(x_1);
x_15 = lean_alloc_closure((void*)(l_Lean_addDocString___redArg___lam__2___boxed), 6, 5);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_2);
lean_closure_set(x_15, 2, x_9);
lean_closure_set(x_15, 3, x_11);
lean_closure_set(x_15, 4, x_14);
lean_inc(x_11);
lean_inc(x_1);
x_16 = lean_alloc_closure((void*)(l_Lean_addDocString___redArg___lam__3___boxed), 9, 8);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_4);
lean_closure_set(x_16, 2, x_5);
lean_closure_set(x_16, 3, x_6);
lean_closure_set(x_16, 4, x_7);
lean_closure_set(x_16, 5, x_9);
lean_closure_set(x_16, 6, x_11);
lean_closure_set(x_16, 7, x_15);
x_17 = lean_alloc_closure((void*)(l_Lean_addDocString___redArg___lam__4), 2, 1);
lean_closure_set(x_17, 0, x_16);
lean_inc(x_17);
lean_inc(x_11);
x_18 = lean_alloc_closure((void*)(l_Lean_addDocString___redArg___lam__5___boxed), 8, 7);
lean_closure_set(x_18, 0, x_8);
lean_closure_set(x_18, 1, x_10);
lean_closure_set(x_18, 2, x_11);
lean_closure_set(x_18, 3, x_17);
lean_closure_set(x_18, 4, x_1);
lean_closure_set(x_18, 5, x_2);
lean_closure_set(x_18, 6, x_17);
x_19 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_12, x_18);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_addDocString___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addDocString___redArg___lam__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString___redArg___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_addDocString___redArg___lam__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec(x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString___redArg___lam__6___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_addDocString___redArg___lam__6(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString___redArg___lam__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_addDocString___redArg___lam__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString_x27___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_box(0);
x_13 = lean_apply_2(x_11, lean_box(0), x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_10);
x_14 = lean_ctor_get(x_9, 0);
lean_inc(x_14);
lean_dec(x_9);
x_15 = l_Lean_addDocString___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDocString_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_addDocString_x27___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
lean_object* initialize_Lean_Environment(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Exception(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Log(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_DocString_Extension(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_DocString_Links(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_DocString_Add(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Environment(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Exception(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Log(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_DocString_Extension(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_DocString_Links(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_addDocString___redArg___lam__0___closed__0 = _init_l_Lean_addDocString___redArg___lam__0___closed__0();
lean_mark_persistent(l_Lean_addDocString___redArg___lam__0___closed__0);
l_Lean_addDocString___redArg___lam__5___closed__0 = _init_l_Lean_addDocString___redArg___lam__5___closed__0();
lean_mark_persistent(l_Lean_addDocString___redArg___lam__5___closed__0);
l_Lean_addDocString___redArg___lam__5___closed__1 = _init_l_Lean_addDocString___redArg___lam__5___closed__1();
lean_mark_persistent(l_Lean_addDocString___redArg___lam__5___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
