// Lean compiler output
// Module: Init.Lean.Elaborator.ResolveName
// Imports: Init.Lean.Modifiers Init.Lean.Elaborator.Alias Init.Lean.Elaborator.Basic
#include "runtime/lean.h"
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
lean_object* l_Lean_Elab_preresolveNames___rarg___boxed(lean_object*, lean_object*, lean_object*);
extern uint8_t l_String_anyAux___main___at_String_all___spec__1___closed__1;
extern lean_object* l_Array_empty___closed__1;
lean_object* l_List_append___rarg(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_resolveName(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elaborator_ResolveName_6__preresolveNamesAux___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Elab_preresolveNames(lean_object*);
lean_object* l_Lean_Elab_preresolveNames___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elaborator_ResolveName_6__preresolveNamesAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getOpenDecls___rarg(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elaborator_ResolveName_5__resolveNameAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_rootNamespace;
lean_object* l_Lean_Elab_getNamespace___rarg(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elaborator_ResolveName_2__resolveUsingNamespace(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append___main(lean_object*, lean_object*);
lean_object* l_List_map___main___at___private_Init_Lean_Elaborator_ResolveName_5__resolveNameAux___main___spec__2(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elaborator_ResolveName_1__resolveQualifiedName___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elaborator_ResolveName_4__resolveOpenDecls___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isAtomic(lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*);
extern lean_object* l_Lean_protectedExt;
lean_object* l___private_Init_Lean_Elaborator_ResolveName_6__preresolveNamesAux___main___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getAliases(lean_object*, lean_object*);
lean_object* l_Lean_Name_replacePrefix___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elaborator_ResolveName_6__preresolveNamesAux___main___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elaborator_ResolveName_4__resolveOpenDecls___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elaborator_ResolveName_6__preresolveNamesAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elaborator_ResolveName_6__preresolveNamesAux___main___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at___private_Init_Lean_Elaborator_ResolveName_5__resolveNameAux___main___spec__1(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elaborator_ResolveName_2__resolveUsingNamespace___main(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elaborator_ResolveName_5__resolveNameAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elaborator_ResolveName_5__resolveNameAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_resolveName___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_eraseDups___at_Lean_Parser_addBuiltinLeadingParser___spec__2(lean_object*);
lean_object* l___private_Init_Lean_Elaborator_ResolveName_2__resolveUsingNamespace___main___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elaborator_ResolveName_6__preresolveNamesAux___main___spec__1(lean_object*);
lean_object* l___private_Init_Lean_Elaborator_ResolveName_2__resolveUsingNamespace___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elaborator_ResolveName_6__preresolveNamesAux(lean_object*);
lean_object* l_Lean_Elab_getEnv___rarg(lean_object*);
lean_object* l___private_Init_Lean_Elaborator_ResolveName_6__preresolveNamesAux___main(lean_object*);
lean_object* l___private_Init_Lean_Elaborator_ResolveName_4__resolveOpenDecls(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_TagDeclarationExtension_isTagged(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elaborator_ResolveName_5__resolveNameAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elaborator_ResolveName_4__resolveOpenDecls___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elaborator_ResolveName_3__resolveExact(lean_object*, lean_object*);
uint8_t l_Bool_DecidableEq(uint8_t, uint8_t);
lean_object* l___private_Init_Lean_Elaborator_ResolveName_1__resolveQualifiedName(lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elaborator_ResolveName_3__resolveExact___boxed(lean_object*, lean_object*);
uint8_t l_List_elem___main___at_Lean_Parser_addBuiltinLeadingParser___spec__4(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elaborator_ResolveName_1__resolveQualifiedName(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
lean_inc(x_3);
x_4 = l_Lean_Name_append___main(x_2, x_3);
x_5 = l_Lean_getAliases(x_1, x_4);
x_6 = l_Lean_Environment_contains(x_1, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_3);
x_7 = l_String_anyAux___main___at_String_all___spec__1___closed__1;
if (x_7 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_5);
return x_8;
}
}
else
{
uint8_t x_9; 
x_9 = l_Lean_Name_isAtomic(x_3);
lean_dec(x_3);
if (x_9 == 0)
{
uint8_t x_10; uint8_t x_11; 
x_10 = 1;
x_11 = l_Bool_DecidableEq(x_6, x_10);
if (x_11 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_5);
return x_12;
}
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_Lean_protectedExt;
x_14 = l_Lean_TagDeclarationExtension_isTagged(x_13, x_1, x_4);
if (x_14 == 0)
{
uint8_t x_15; uint8_t x_16; 
x_15 = 1;
x_16 = l_Bool_DecidableEq(x_6, x_15);
if (x_16 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_4);
lean_ctor_set(x_17, 1, x_5);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = l_String_anyAux___main___at_String_all___spec__1___closed__1;
if (x_18 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_4);
lean_ctor_set(x_19, 1, x_5);
return x_19;
}
}
}
}
}
}
lean_object* l___private_Init_Lean_Elaborator_ResolveName_1__resolveQualifiedName___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Elaborator_ResolveName_1__resolveQualifiedName(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Init_Lean_Elaborator_ResolveName_2__resolveUsingNamespace___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_2);
x_5 = l___private_Init_Lean_Elaborator_ResolveName_1__resolveQualifiedName(x_1, x_3, x_2);
if (lean_obj_tag(x_5) == 0)
{
x_3 = x_4;
goto _start;
}
else
{
lean_dec(x_2);
return x_5;
}
}
else
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_box(0);
return x_7;
}
}
}
lean_object* l___private_Init_Lean_Elaborator_ResolveName_2__resolveUsingNamespace___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Elaborator_ResolveName_2__resolveUsingNamespace___main(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Init_Lean_Elaborator_ResolveName_2__resolveUsingNamespace(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Elaborator_ResolveName_2__resolveUsingNamespace___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l___private_Init_Lean_Elaborator_ResolveName_2__resolveUsingNamespace___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Elaborator_ResolveName_2__resolveUsingNamespace(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Init_Lean_Elaborator_ResolveName_3__resolveExact(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; 
x_3 = l_Lean_Name_isAtomic(x_2);
x_4 = 1;
x_5 = l_Bool_DecidableEq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; 
x_6 = l_Lean_Elab_rootNamespace;
x_7 = lean_box(0);
x_8 = l_Lean_Name_replacePrefix___main(x_2, x_6, x_7);
x_9 = l_Lean_Environment_contains(x_1, x_8);
x_10 = l_Bool_DecidableEq(x_9, x_4);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
x_11 = lean_box(0);
return x_11;
}
else
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_8);
return x_12;
}
}
else
{
lean_object* x_13; 
lean_dec(x_2);
x_13 = lean_box(0);
return x_13;
}
}
}
lean_object* l___private_Init_Lean_Elaborator_ResolveName_3__resolveExact___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Lean_Elaborator_ResolveName_3__resolveExact(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l___private_Init_Lean_Elaborator_ResolveName_4__resolveOpenDecls___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; 
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = l_List_elem___main___at_Lean_Parser_addBuiltinLeadingParser___spec__4(x_2, x_8);
lean_dec(x_8);
x_10 = 1;
x_11 = l_Bool_DecidableEq(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_inc(x_2);
x_12 = l___private_Init_Lean_Elaborator_ResolveName_1__resolveQualifiedName(x_1, x_7, x_2);
lean_dec(x_7);
x_13 = l_List_append___rarg(x_12, x_4);
x_3 = x_6;
x_4 = x_13;
goto _start;
}
else
{
lean_dec(x_7);
x_3 = x_6;
goto _start;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_3);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; 
x_17 = lean_ctor_get(x_3, 1);
x_18 = lean_ctor_get(x_3, 0);
lean_dec(x_18);
x_19 = lean_ctor_get(x_5, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_5, 1);
lean_inc(x_20);
lean_dec(x_5);
x_21 = lean_name_eq(x_2, x_19);
lean_dec(x_19);
x_22 = 1;
x_23 = l_Bool_DecidableEq(x_21, x_22);
if (x_23 == 0)
{
lean_dec(x_20);
lean_free_object(x_3);
x_3 = x_17;
goto _start;
}
else
{
lean_ctor_set(x_3, 1, x_4);
lean_ctor_set(x_3, 0, x_20);
{
lean_object* _tmp_2 = x_17;
lean_object* _tmp_3 = x_3;
x_3 = _tmp_2;
x_4 = _tmp_3;
}
goto _start;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; 
x_26 = lean_ctor_get(x_3, 1);
lean_inc(x_26);
lean_dec(x_3);
x_27 = lean_ctor_get(x_5, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_5, 1);
lean_inc(x_28);
lean_dec(x_5);
x_29 = lean_name_eq(x_2, x_27);
lean_dec(x_27);
x_30 = 1;
x_31 = l_Bool_DecidableEq(x_29, x_30);
if (x_31 == 0)
{
lean_dec(x_28);
x_3 = x_26;
goto _start;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_28);
lean_ctor_set(x_33, 1, x_4);
x_3 = x_26;
x_4 = x_33;
goto _start;
}
}
}
}
}
}
lean_object* l___private_Init_Lean_Elaborator_ResolveName_4__resolveOpenDecls___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Elaborator_ResolveName_4__resolveOpenDecls___main(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Init_Lean_Elaborator_ResolveName_4__resolveOpenDecls(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Elaborator_ResolveName_4__resolveOpenDecls___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l___private_Init_Lean_Elaborator_ResolveName_4__resolveOpenDecls___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Elaborator_ResolveName_4__resolveOpenDecls(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_List_map___main___at___private_Init_Lean_Elaborator_ResolveName_5__resolveNameAux___main___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_5);
x_8 = l_List_map___main___at___private_Init_Lean_Elaborator_ResolveName_5__resolveNameAux___main___spec__1(x_1, x_6);
lean_ctor_set(x_2, 1, x_8);
lean_ctor_set(x_2, 0, x_7);
return x_2;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_2);
lean_inc(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_9);
x_12 = l_List_map___main___at___private_Init_Lean_Elaborator_ResolveName_5__resolveNameAux___main___spec__1(x_1, x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
lean_object* l_List_map___main___at___private_Init_Lean_Elaborator_ResolveName_5__resolveNameAux___main___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_5);
x_8 = l_List_map___main___at___private_Init_Lean_Elaborator_ResolveName_5__resolveNameAux___main___spec__2(x_1, x_6);
lean_ctor_set(x_2, 1, x_8);
lean_ctor_set(x_2, 0, x_7);
return x_2;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_2);
lean_inc(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_9);
x_12 = l_List_map___main___at___private_Init_Lean_Elaborator_ResolveName_5__resolveNameAux___main___spec__2(x_1, x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
lean_object* l___private_Init_Lean_Elaborator_ResolveName_5__resolveNameAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_4) == 1)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_inc(x_4);
x_7 = l___private_Init_Lean_Elaborator_ResolveName_2__resolveUsingNamespace___main(x_1, x_4, x_2);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
lean_inc(x_4);
x_8 = l___private_Init_Lean_Elaborator_ResolveName_3__resolveExact(x_1, x_4);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_9 = l_Lean_Environment_contains(x_1, x_4);
x_10 = 1;
x_11 = l_Bool_DecidableEq(x_9, x_10);
x_12 = l_Lean_getAliases(x_1, x_4);
if (x_11 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_inc(x_3);
x_20 = l___private_Init_Lean_Elaborator_ResolveName_4__resolveOpenDecls___main(x_1, x_4, x_3, x_7);
x_21 = l_List_append___rarg(x_12, x_20);
x_13 = x_21;
goto block_19;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_inc(x_4);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_4);
lean_ctor_set(x_22, 1, x_7);
lean_inc(x_3);
x_23 = l___private_Init_Lean_Elaborator_ResolveName_4__resolveOpenDecls___main(x_1, x_4, x_3, x_22);
x_24 = l_List_append___rarg(x_12, x_23);
x_13 = x_24;
goto block_19;
}
block_19:
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_5, x_14);
lean_dec(x_5);
x_4 = x_6;
x_5 = x_15;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_6);
lean_dec(x_3);
x_17 = l_List_eraseDups___at_Lean_Parser_addBuiltinLeadingParser___spec__2(x_13);
x_18 = l_List_map___main___at___private_Init_Lean_Elaborator_ResolveName_5__resolveNameAux___main___spec__1(x_5, x_17);
return x_18;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_25 = lean_ctor_get(x_8, 0);
lean_inc(x_25);
lean_dec(x_8);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_5);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_29 = l_List_eraseDups___at_Lean_Parser_addBuiltinLeadingParser___spec__2(x_7);
x_30 = l_List_map___main___at___private_Init_Lean_Elaborator_ResolveName_5__resolveNameAux___main___spec__2(x_5, x_29);
return x_30;
}
}
else
{
lean_object* x_31; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_31 = lean_box(0);
return x_31;
}
}
}
lean_object* l___private_Init_Lean_Elaborator_ResolveName_5__resolveNameAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Lean_Elaborator_ResolveName_5__resolveNameAux___main(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l___private_Init_Lean_Elaborator_ResolveName_5__resolveNameAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Lean_Elaborator_ResolveName_5__resolveNameAux___main(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l___private_Init_Lean_Elaborator_ResolveName_5__resolveNameAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Lean_Elaborator_ResolveName_5__resolveNameAux(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_Elab_resolveName(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_4 = l_Lean_Elab_getEnv___rarg(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_Lean_Elab_getNamespace___rarg(x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Elab_getOpenDecls___rarg(x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l___private_Init_Lean_Elaborator_ResolveName_5__resolveNameAux___main(x_5, x_8, x_12, x_1, x_13);
lean_dec(x_8);
lean_dec(x_5);
lean_ctor_set(x_10, 0, x_14);
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_10, 0);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_10);
x_17 = lean_unsigned_to_nat(0u);
x_18 = l___private_Init_Lean_Elaborator_ResolveName_5__resolveNameAux___main(x_5, x_8, x_15, x_1, x_17);
lean_dec(x_8);
lean_dec(x_5);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_16);
return x_19;
}
}
}
lean_object* l_Lean_Elab_resolveName___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_resolveName(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elaborator_ResolveName_6__preresolveNamesAux___main___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_5);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_3);
x_8 = l_Array_empty___closed__1;
x_9 = x_5;
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = lean_array_fget(x_5, x_4);
x_11 = lean_box(0);
lean_inc(x_10);
x_12 = x_11;
x_13 = lean_array_fset(x_5, x_4, x_12);
lean_inc(x_10);
lean_inc(x_3);
x_14 = l___private_Init_Lean_Elaborator_ResolveName_6__preresolveNamesAux___main___rarg(x_1, x_2, x_3, x_10);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_4, x_15);
x_17 = x_14;
x_18 = lean_array_fset(x_13, x_4, x_17);
lean_dec(x_4);
x_4 = x_16;
x_5 = x_18;
goto _start;
}
}
}
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elaborator_ResolveName_6__preresolveNamesAux___main___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Init_Lean_Elaborator_ResolveName_6__preresolveNamesAux___main___spec__1___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l___private_Init_Lean_Elaborator_ResolveName_6__preresolveNamesAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_4)) {
case 1:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 1);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_umapMAux___main___at___private_Init_Lean_Elaborator_ResolveName_6__preresolveNamesAux___main___spec__1___rarg(x_1, x_2, x_3, x_7, x_6);
lean_ctor_set(x_4, 1, x_8);
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_4);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_umapMAux___main___at___private_Init_Lean_Elaborator_ResolveName_6__preresolveNamesAux___main___spec__1___rarg(x_1, x_2, x_3, x_11, x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
case 3:
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_4);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_4, 2);
x_16 = lean_ctor_get(x_4, 3);
lean_dec(x_16);
x_17 = lean_unsigned_to_nat(0u);
lean_inc(x_15);
x_18 = l___private_Init_Lean_Elaborator_ResolveName_5__resolveNameAux___main(x_1, x_2, x_3, x_15, x_17);
lean_ctor_set(x_4, 3, x_18);
return x_4;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_4, 0);
x_20 = lean_ctor_get(x_4, 1);
x_21 = lean_ctor_get(x_4, 2);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_4);
x_22 = lean_unsigned_to_nat(0u);
lean_inc(x_21);
x_23 = l___private_Init_Lean_Elaborator_ResolveName_5__resolveNameAux___main(x_1, x_2, x_3, x_21, x_22);
x_24 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_24, 1, x_20);
lean_ctor_set(x_24, 2, x_21);
lean_ctor_set(x_24, 3, x_23);
return x_24;
}
}
default: 
{
lean_dec(x_3);
return x_4;
}
}
}
}
lean_object* l___private_Init_Lean_Elaborator_ResolveName_6__preresolveNamesAux___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_Elaborator_ResolveName_6__preresolveNamesAux___main___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_Elaborator_ResolveName_6__preresolveNamesAux___main___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_umapMAux___main___at___private_Init_Lean_Elaborator_ResolveName_6__preresolveNamesAux___main___spec__1___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l___private_Init_Lean_Elaborator_ResolveName_6__preresolveNamesAux___main___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Elaborator_ResolveName_6__preresolveNamesAux___main___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Init_Lean_Elaborator_ResolveName_6__preresolveNamesAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Elaborator_ResolveName_6__preresolveNamesAux___main___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l___private_Init_Lean_Elaborator_ResolveName_6__preresolveNamesAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_Elaborator_ResolveName_6__preresolveNamesAux___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l___private_Init_Lean_Elaborator_ResolveName_6__preresolveNamesAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Elaborator_ResolveName_6__preresolveNamesAux___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_preresolveNames___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_4 = l_Lean_Elab_getEnv___rarg(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_Lean_Elab_getNamespace___rarg(x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Elab_getOpenDecls___rarg(x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = l___private_Init_Lean_Elaborator_ResolveName_6__preresolveNamesAux___main___rarg(x_5, x_8, x_12, x_1);
lean_dec(x_8);
lean_dec(x_5);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_10);
x_16 = l___private_Init_Lean_Elaborator_ResolveName_6__preresolveNamesAux___main___rarg(x_5, x_8, x_14, x_1);
lean_dec(x_8);
lean_dec(x_5);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
}
lean_object* l_Lean_Elab_preresolveNames(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_preresolveNames___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_preresolveNames___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_preresolveNames___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* initialize_Init_Lean_Modifiers(lean_object*);
lean_object* initialize_Init_Lean_Elaborator_Alias(lean_object*);
lean_object* initialize_Init_Lean_Elaborator_Basic(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Elaborator_ResolveName(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Modifiers(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Elaborator_Alias(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Elaborator_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
