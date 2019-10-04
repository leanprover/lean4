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
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elaborator_ResolveName_5__resolveNameAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_preresolveNames___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_Elab_preresolveNames(lean_object*);
lean_object* l___private_Init_Lean_Elaborator_ResolveName_2__resolveUsingNamespace___main___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_preresolveNames___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elaborator_ResolveName_2__resolveUsingNamespace___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elaborator_ResolveName_6__preresolveNamesAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_ummapAux___main___at___private_Init_Lean_Elaborator_ResolveName_6__preresolveNamesAux___main___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elaborator_ResolveName_6__preresolveNamesAux___main___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elaborator_ResolveName_1__resolveQualifiedName(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elaborator_ResolveName_5__resolveNameAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elaborator_ResolveName_3__resolveExact(lean_object*, lean_object*);
uint8_t l_Lean_Name_isAtomic(lean_object*);
lean_object* l_Lean_getAliases(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elaborator_ResolveName_2__resolveUsingNamespace___main(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elaborator_ResolveName_6__preresolveNamesAux___main(lean_object*);
lean_object* l___private_Init_Lean_Elaborator_ResolveName_3__resolveExact___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elaborator_ResolveName_6__preresolveNamesAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getNamespace___rarg(lean_object*);
lean_object* l___private_Init_Lean_Elaborator_ResolveName_1__resolveQualifiedName___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_List_append___rarg(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Elab_resolveName___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elaborator_ResolveName_5__resolveNameAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_rootNamespace;
lean_object* l_Lean_Elab_resolveName(lean_object*, lean_object*, lean_object*);
uint8_t l_List_elem___main___at_Lean_Parser_addBuiltinLeadingParser___spec__4(lean_object*, lean_object*);
lean_object* l_List_eraseDups___at_Lean_Parser_addBuiltinLeadingParser___spec__2(lean_object*);
lean_object* l_Array_ummapAux___main___at___private_Init_Lean_Elaborator_ResolveName_6__preresolveNamesAux___main___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_replacePrefix___main(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elaborator_ResolveName_2__resolveUsingNamespace(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getOpenDecls___rarg(lean_object*);
uint8_t lean_is_protected(lean_object*, lean_object*);
lean_object* l_Lean_Elab_getEnv___rarg(lean_object*);
lean_object* l_Array_size(lean_object*, lean_object*);
lean_object* l_Array_get(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elaborator_ResolveName_5__resolveNameAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elaborator_ResolveName_4__resolveOpenDecls___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elaborator_ResolveName_6__preresolveNamesAux___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_set(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at___private_Init_Lean_Elaborator_ResolveName_5__resolveNameAux___main___spec__1(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elaborator_ResolveName_6__preresolveNamesAux(lean_object*);
lean_object* l_Lean_Name_append___main(lean_object*, lean_object*);
lean_object* l_Array_ummapAux___main___at___private_Init_Lean_Elaborator_ResolveName_6__preresolveNamesAux___main___spec__1(lean_object*);
lean_object* l___private_Init_Lean_Elaborator_ResolveName_4__resolveOpenDecls(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at___private_Init_Lean_Elaborator_ResolveName_5__resolveNameAux___main___spec__2(lean_object*, lean_object*);
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
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
else
{
uint8_t x_7; 
x_7 = l_Lean_Name_isAtomic(x_3);
lean_dec(x_3);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_1);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_5);
return x_8;
}
else
{
uint8_t x_9; 
lean_inc(x_4);
x_9 = lean_is_protected(x_1, x_4);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_5);
return x_10;
}
else
{
lean_dec(x_4);
return x_5;
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
lean_inc(x_1);
x_5 = l___private_Init_Lean_Elaborator_ResolveName_1__resolveQualifiedName(x_1, x_3, x_2);
if (lean_obj_tag(x_5) == 0)
{
x_3 = x_4;
goto _start;
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
else
{
lean_object* x_7; 
lean_dec(x_2);
lean_dec(x_1);
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
return x_4;
}
}
lean_object* l___private_Init_Lean_Elaborator_ResolveName_3__resolveExact(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Name_isAtomic(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = l_Lean_Elab_rootNamespace;
x_5 = lean_box(0);
x_6 = l_Lean_Name_replacePrefix___main(x_2, x_4, x_5);
x_7 = l_Lean_Environment_contains(x_1, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_6);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_6);
return x_9;
}
}
else
{
lean_object* x_10; 
lean_dec(x_2);
x_10 = lean_box(0);
return x_10;
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
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
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
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_inc(x_2);
lean_inc(x_1);
x_10 = l___private_Init_Lean_Elaborator_ResolveName_1__resolveQualifiedName(x_1, x_7, x_2);
lean_dec(x_7);
x_11 = l_List_append___rarg(x_10, x_4);
x_3 = x_6;
x_4 = x_11;
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
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_3);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_3, 1);
x_16 = lean_ctor_get(x_3, 0);
lean_dec(x_16);
x_17 = lean_ctor_get(x_5, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_5, 1);
lean_inc(x_18);
lean_dec(x_5);
x_19 = lean_name_dec_eq(x_2, x_17);
lean_dec(x_17);
if (x_19 == 0)
{
lean_dec(x_18);
lean_free_object(x_3);
x_3 = x_15;
goto _start;
}
else
{
lean_ctor_set(x_3, 1, x_4);
lean_ctor_set(x_3, 0, x_18);
{
lean_object* _tmp_2 = x_15;
lean_object* _tmp_3 = x_3;
x_3 = _tmp_2;
x_4 = _tmp_3;
}
goto _start;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_3, 1);
lean_inc(x_22);
lean_dec(x_3);
x_23 = lean_ctor_get(x_5, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_5, 1);
lean_inc(x_24);
lean_dec(x_5);
x_25 = lean_name_dec_eq(x_2, x_23);
lean_dec(x_23);
if (x_25 == 0)
{
lean_dec(x_24);
x_3 = x_22;
goto _start;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_4);
x_3 = x_22;
x_4 = x_27;
goto _start;
}
}
}
}
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
lean_inc(x_1);
x_7 = l___private_Init_Lean_Elaborator_ResolveName_2__resolveUsingNamespace___main(x_1, x_4, x_2);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
lean_inc(x_4);
x_8 = l___private_Init_Lean_Elaborator_ResolveName_3__resolveExact(x_1, x_4);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_Lean_Environment_contains(x_1, x_4);
x_10 = l_Lean_getAliases(x_1, x_4);
if (x_9 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_inc(x_3);
lean_inc(x_1);
x_18 = l___private_Init_Lean_Elaborator_ResolveName_4__resolveOpenDecls___main(x_1, x_4, x_3, x_7);
x_19 = l_List_append___rarg(x_10, x_18);
x_11 = x_19;
goto block_17;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_inc(x_4);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_4);
lean_ctor_set(x_20, 1, x_7);
lean_inc(x_3);
lean_inc(x_1);
x_21 = l___private_Init_Lean_Elaborator_ResolveName_4__resolveOpenDecls___main(x_1, x_4, x_3, x_20);
x_22 = l_List_append___rarg(x_10, x_21);
x_11 = x_22;
goto block_17;
}
block_17:
{
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_5, x_12);
lean_dec(x_5);
x_4 = x_6;
x_5 = x_13;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_15 = l_List_eraseDups___at_Lean_Parser_addBuiltinLeadingParser___spec__2(x_11);
x_16 = l_List_map___main___at___private_Init_Lean_Elaborator_ResolveName_5__resolveNameAux___main___spec__1(x_5, x_15);
return x_16;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_23 = lean_ctor_get(x_8, 0);
lean_inc(x_23);
lean_dec(x_8);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_5);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_27 = l_List_eraseDups___at_Lean_Parser_addBuiltinLeadingParser___spec__2(x_7);
x_28 = l_List_map___main___at___private_Init_Lean_Elaborator_ResolveName_5__resolveNameAux___main___spec__2(x_5, x_27);
return x_28;
}
}
else
{
lean_object* x_29; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_29 = lean_box(0);
return x_29;
}
}
}
lean_object* l___private_Init_Lean_Elaborator_ResolveName_5__resolveNameAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Lean_Elaborator_ResolveName_5__resolveNameAux___main(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
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
return x_6;
}
}
lean_object* l_Lean_Elab_resolveName(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_getEnv___rarg(x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_box(0);
lean_ctor_set(x_4, 0, x_7);
x_8 = l_Lean_Elab_getNamespace___rarg(x_4);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_ctor_set(x_8, 0, x_7);
x_11 = l_Lean_Elab_getOpenDecls___rarg(x_8);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_unsigned_to_nat(0u);
x_15 = l___private_Init_Lean_Elaborator_ResolveName_5__resolveNameAux___main(x_6, x_10, x_13, x_1, x_14);
lean_dec(x_10);
lean_ctor_set(x_11, 0, x_15);
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_11, 0);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l___private_Init_Lean_Elaborator_ResolveName_5__resolveNameAux___main(x_6, x_10, x_16, x_1, x_18);
lean_dec(x_10);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
return x_20;
}
}
else
{
uint8_t x_21; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_11);
if (x_21 == 0)
{
return x_11;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_11, 0);
x_23 = lean_ctor_get(x_11, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_11);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_8, 0);
x_26 = lean_ctor_get(x_8, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_8);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_7);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_Elab_getOpenDecls___rarg(x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_31 = x_28;
} else {
 lean_dec_ref(x_28);
 x_31 = lean_box(0);
}
x_32 = lean_unsigned_to_nat(0u);
x_33 = l___private_Init_Lean_Elaborator_ResolveName_5__resolveNameAux___main(x_6, x_25, x_29, x_1, x_32);
lean_dec(x_25);
if (lean_is_scalar(x_31)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_31;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_30);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_25);
lean_dec(x_6);
lean_dec(x_1);
x_35 = lean_ctor_get(x_28, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_28, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_37 = x_28;
} else {
 lean_dec_ref(x_28);
 x_37 = lean_box(0);
}
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(1, 2, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_6);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_8);
if (x_39 == 0)
{
return x_8;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_8, 0);
x_41 = lean_ctor_get(x_8, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_8);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_43 = lean_ctor_get(x_4, 0);
x_44 = lean_ctor_get(x_4, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_4);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
x_47 = l_Lean_Elab_getNamespace___rarg(x_46);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_50 = x_47;
} else {
 lean_dec_ref(x_47);
 x_50 = lean_box(0);
}
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_50;
}
lean_ctor_set(x_51, 0, x_45);
lean_ctor_set(x_51, 1, x_49);
x_52 = l_Lean_Elab_getOpenDecls___rarg(x_51);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_55 = x_52;
} else {
 lean_dec_ref(x_52);
 x_55 = lean_box(0);
}
x_56 = lean_unsigned_to_nat(0u);
x_57 = l___private_Init_Lean_Elaborator_ResolveName_5__resolveNameAux___main(x_43, x_48, x_53, x_1, x_56);
lean_dec(x_48);
if (lean_is_scalar(x_55)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_55;
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_54);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_48);
lean_dec(x_43);
lean_dec(x_1);
x_59 = lean_ctor_get(x_52, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_52, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_61 = x_52;
} else {
 lean_dec_ref(x_52);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(1, 2, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_43);
lean_dec(x_1);
x_63 = lean_ctor_get(x_47, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_47, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_65 = x_47;
} else {
 lean_dec_ref(x_47);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(1, 2, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_1);
x_67 = !lean_is_exclusive(x_4);
if (x_67 == 0)
{
return x_4;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_4, 0);
x_69 = lean_ctor_get(x_4, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_4);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
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
lean_object* l_Array_ummapAux___main___at___private_Init_Lean_Elaborator_ResolveName_6__preresolveNamesAux___main___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_dec(x_1);
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
lean_inc(x_1);
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
lean_object* l_Array_ummapAux___main___at___private_Init_Lean_Elaborator_ResolveName_6__preresolveNamesAux___main___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_ummapAux___main___at___private_Init_Lean_Elaborator_ResolveName_6__preresolveNamesAux___main___spec__1___rarg___boxed), 5, 0);
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
x_8 = l_Array_ummapAux___main___at___private_Init_Lean_Elaborator_ResolveName_6__preresolveNamesAux___main___spec__1___rarg(x_1, x_2, x_3, x_7, x_6);
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
x_12 = l_Array_ummapAux___main___at___private_Init_Lean_Elaborator_ResolveName_6__preresolveNamesAux___main___spec__1___rarg(x_1, x_2, x_3, x_11, x_10);
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
lean_dec(x_1);
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
lean_object* l_Array_ummapAux___main___at___private_Init_Lean_Elaborator_ResolveName_6__preresolveNamesAux___main___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_ummapAux___main___at___private_Init_Lean_Elaborator_ResolveName_6__preresolveNamesAux___main___spec__1___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* l___private_Init_Lean_Elaborator_ResolveName_6__preresolveNamesAux___main___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Elaborator_ResolveName_6__preresolveNamesAux___main___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
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
return x_5;
}
}
lean_object* l_Lean_Elab_preresolveNames___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_getEnv___rarg(x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_box(0);
lean_ctor_set(x_4, 0, x_7);
x_8 = l_Lean_Elab_getNamespace___rarg(x_4);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_ctor_set(x_8, 0, x_7);
x_11 = l_Lean_Elab_getOpenDecls___rarg(x_8);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = l___private_Init_Lean_Elaborator_ResolveName_6__preresolveNamesAux___main___rarg(x_6, x_10, x_13, x_1);
lean_dec(x_10);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_11);
x_17 = l___private_Init_Lean_Elaborator_ResolveName_6__preresolveNamesAux___main___rarg(x_6, x_10, x_15, x_1);
lean_dec(x_10);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
uint8_t x_19; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_11);
if (x_19 == 0)
{
return x_11;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_11, 0);
x_21 = lean_ctor_get(x_11, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_11);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_8, 0);
x_24 = lean_ctor_get(x_8, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_8);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_7);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_Elab_getOpenDecls___rarg(x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_29 = x_26;
} else {
 lean_dec_ref(x_26);
 x_29 = lean_box(0);
}
x_30 = l___private_Init_Lean_Elaborator_ResolveName_6__preresolveNamesAux___main___rarg(x_6, x_23, x_27, x_1);
lean_dec(x_23);
if (lean_is_scalar(x_29)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_29;
}
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_28);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_23);
lean_dec(x_6);
lean_dec(x_1);
x_32 = lean_ctor_get(x_26, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_26, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_34 = x_26;
} else {
 lean_dec_ref(x_26);
 x_34 = lean_box(0);
}
if (lean_is_scalar(x_34)) {
 x_35 = lean_alloc_ctor(1, 2, 0);
} else {
 x_35 = x_34;
}
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_6);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_8);
if (x_36 == 0)
{
return x_8;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_8, 0);
x_38 = lean_ctor_get(x_8, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_8);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_4, 0);
x_41 = lean_ctor_get(x_4, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_4);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
x_44 = l_Lean_Elab_getNamespace___rarg(x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_47 = x_44;
} else {
 lean_dec_ref(x_44);
 x_47 = lean_box(0);
}
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_42);
lean_ctor_set(x_48, 1, x_46);
x_49 = l_Lean_Elab_getOpenDecls___rarg(x_48);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_52 = x_49;
} else {
 lean_dec_ref(x_49);
 x_52 = lean_box(0);
}
x_53 = l___private_Init_Lean_Elaborator_ResolveName_6__preresolveNamesAux___main___rarg(x_40, x_45, x_50, x_1);
lean_dec(x_45);
if (lean_is_scalar(x_52)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_52;
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_51);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_45);
lean_dec(x_40);
lean_dec(x_1);
x_55 = lean_ctor_get(x_49, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_49, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_57 = x_49;
} else {
 lean_dec_ref(x_49);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(1, 2, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_56);
return x_58;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_40);
lean_dec(x_1);
x_59 = lean_ctor_get(x_44, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_44, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_61 = x_44;
} else {
 lean_dec_ref(x_44);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(1, 2, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
}
else
{
uint8_t x_63; 
lean_dec(x_1);
x_63 = !lean_is_exclusive(x_4);
if (x_63 == 0)
{
return x_4;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_4, 0);
x_65 = lean_ctor_get(x_4, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_4);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
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
if (_G_initialized) return w;
_G_initialized = true;
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Lean_Modifiers(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Lean_Elaborator_Alias(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Lean_Elaborator_Basic(w);
if (lean_io_result_is_error(w)) return w;
return w;
}
#ifdef __cplusplus
}
#endif
