// Lean compiler output
// Module: Init.Lean.Elab.ResolveName
// Imports: Init.Lean.Modifiers Init.Lean.Elab.Alias
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
lean_object* l_List_reverse___rarg(lean_object*);
lean_object* l_Lean_Elab_resolveNamespaceUsingScope(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Name_toString___closed__1;
lean_object* l___private_Init_Lean_Elab_ResolveName_1__resolveQualifiedName(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_ResolveName_4__resolveOpenDecls___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unreachable_x21___rarg(lean_object*);
extern lean_object* l_List_repr___rarg___closed__1;
lean_object* l___private_Init_Lean_Elab_ResolveName_2__resolveUsingNamespace(lean_object*, lean_object*, lean_object*);
uint8_t l_List_elem___main___at_Lean_addAliasEntry___spec__18(lean_object*, lean_object*);
lean_object* l_List_append___rarg(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_List_toStringAux___main___at_Lean_Elab_OpenDecl_HasToString___spec__3___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_resolveGlobalName___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_ResolveName_5__resolveGlobalNameAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_resolveNamespaceUsingScope___main(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_List_eraseDupsAux___main___at___private_Init_Lean_Elab_ResolveName_5__resolveGlobalNameAux___main___spec__2(lean_object*, lean_object*);
extern lean_object* l_String_splitAux___main___closed__1;
extern lean_object* l_List_repr___rarg___closed__3;
lean_object* l_Lean_Elab_rootNamespace;
lean_object* l_Lean_Elab_resolveNamespaceUsingScope___main___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_List_beq___main___at_Lean_Elab_OpenDecl_HasToString___spec__1(lean_object*, lean_object*);
lean_object* l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(lean_object*);
lean_object* l_Lean_Name_append___main(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_ResolveName_2__resolveUsingNamespace___main___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_toStringAux___main___at_Lean_Elab_OpenDecl_HasToString___spec__3(uint8_t, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
extern lean_object* l_List_repr___rarg___closed__2;
extern lean_object* l_List_reprAux___main___rarg___closed__1;
lean_object* l_Lean_Elab_resolveNamespaceUsingOpenDecls___main(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isAtomic(lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*);
extern lean_object* l_Lean_protectedExt;
lean_object* l_Lean_Elab_resolveNamespaceUsingOpenDecls(lean_object*, lean_object*, lean_object*);
lean_object* l_List_eraseDups___at___private_Init_Lean_Elab_ResolveName_5__resolveGlobalNameAux___main___spec__1(lean_object*);
lean_object* l___private_Init_Lean_Elab_ResolveName_2__resolveUsingNamespace___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_removeRoot(lean_object*);
lean_object* l_Lean_Elab_resolveNamespace___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_resolveNamespaceUsingScope___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getAliases(lean_object*, lean_object*);
lean_object* l_Lean_Elab_OpenDecl_Inhabited___closed__1;
lean_object* l_Lean_Name_replacePrefix___main(lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at___private_Init_Lean_Elab_ResolveName_5__resolveGlobalNameAux___main___spec__4(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_ResolveName_2__resolveUsingNamespace___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_ResolveName_4__resolveOpenDecls(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_ResolveName_5__resolveGlobalNameAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at___private_Init_Lean_Elab_ResolveName_5__resolveGlobalNameAux___main___spec__3(lean_object*, lean_object*);
lean_object* l_Lean_Elab_rootNamespace___closed__1;
lean_object* l___private_Init_Lean_Elab_ResolveName_5__resolveGlobalNameAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_OpenDecl_HasToString___closed__2;
lean_object* l_Lean_Elab_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_rootNamespace___closed__2;
uint8_t l_Lean_TagDeclarationExtension_isTagged(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_ResolveName_5__resolveGlobalNameAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_OpenDecl_Inhabited;
lean_object* l_Lean_Elab_OpenDecl_HasToString(lean_object*);
lean_object* l___private_Init_Lean_Elab_ResolveName_3__resolveExact(lean_object*, lean_object*);
lean_object* l_Lean_Elab_resolveNamespaceUsingOpenDecls___main___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_resolveNamespaceUsingOpenDecls___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_OpenDecl_HasToString___closed__1;
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l_List_beq___main___at_Lean_Elab_OpenDecl_HasToString___spec__1___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_ResolveName_1__resolveQualifiedName___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isNamespace(lean_object*, lean_object*);
lean_object* l_Lean_Elab_resolveNamespace(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* _init_l_Lean_Elab_OpenDecl_Inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_OpenDecl_Inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_OpenDecl_Inhabited___closed__1;
return x_1;
}
}
uint8_t l_List_beq___main___at_Lean_Elab_OpenDecl_HasToString___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_name_eq(x_6, x_8);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
else
{
x_1 = x_7;
x_2 = x_9;
goto _start;
}
}
}
}
}
lean_object* l_List_toStringAux___main___at_Lean_Elab_OpenDecl_HasToString___spec__3(uint8_t x_1, lean_object* x_2) {
_start:
{
if (x_1 == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = l_String_splitAux___main___closed__1;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l_Lean_Name_toString___closed__1;
x_7 = l_Lean_Name_toStringWithSep___main(x_6, x_4);
x_8 = l_List_reprAux___main___rarg___closed__1;
x_9 = lean_string_append(x_8, x_7);
lean_dec(x_7);
x_10 = l_List_toStringAux___main___at_Lean_Elab_OpenDecl_HasToString___spec__3(x_1, x_5);
x_11 = lean_string_append(x_9, x_10);
lean_dec(x_10);
return x_11;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_12; 
x_12 = l_String_splitAux___main___closed__1;
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
lean_dec(x_2);
x_15 = l_Lean_Name_toString___closed__1;
x_16 = l_Lean_Name_toStringWithSep___main(x_15, x_13);
x_17 = 0;
x_18 = l_List_toStringAux___main___at_Lean_Elab_OpenDecl_HasToString___spec__3(x_17, x_14);
x_19 = lean_string_append(x_16, x_18);
lean_dec(x_18);
return x_19;
}
}
}
}
lean_object* l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_List_repr___rarg___closed__1;
return x_2;
}
else
{
uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = 1;
x_4 = l_List_toStringAux___main___at_Lean_Elab_OpenDecl_HasToString___spec__3(x_3, x_1);
x_5 = l_List_repr___rarg___closed__2;
x_6 = lean_string_append(x_5, x_4);
lean_dec(x_4);
x_7 = l_List_repr___rarg___closed__3;
x_8 = lean_string_append(x_6, x_7);
return x_8;
}
}
}
lean_object* _init_l_Lean_Elab_OpenDecl_HasToString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" hiding ");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_OpenDecl_HasToString___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" → ");
return x_1;
}
}
lean_object* l_Lean_Elab_OpenDecl_HasToString(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Name_toString___closed__1;
x_5 = l_Lean_Name_toStringWithSep___main(x_4, x_2);
x_6 = lean_box(0);
x_7 = l_List_beq___main___at_Lean_Elab_OpenDecl_HasToString___spec__1(x_3, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_3);
x_9 = l_Lean_Elab_OpenDecl_HasToString___closed__1;
x_10 = lean_string_append(x_9, x_8);
lean_dec(x_8);
x_11 = lean_string_append(x_5, x_10);
lean_dec(x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_3);
x_12 = l_String_splitAux___main___closed__1;
x_13 = lean_string_append(x_5, x_12);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
lean_dec(x_1);
x_16 = l_Lean_Name_toString___closed__1;
x_17 = l_Lean_Name_toStringWithSep___main(x_16, x_14);
x_18 = l_Lean_Elab_OpenDecl_HasToString___closed__2;
x_19 = lean_string_append(x_17, x_18);
x_20 = l_Lean_Name_toStringWithSep___main(x_16, x_15);
x_21 = lean_string_append(x_19, x_20);
lean_dec(x_20);
return x_21;
}
}
}
lean_object* l_List_beq___main___at_Lean_Elab_OpenDecl_HasToString___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_beq___main___at_Lean_Elab_OpenDecl_HasToString___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_List_toStringAux___main___at_Lean_Elab_OpenDecl_HasToString___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_List_toStringAux___main___at_Lean_Elab_OpenDecl_HasToString___spec__3(x_3, x_2);
return x_4;
}
}
lean_object* _init_l_Lean_Elab_rootNamespace___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_root_");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_rootNamespace___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_rootNamespace___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_rootNamespace() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_rootNamespace___closed__2;
return x_1;
}
}
lean_object* l_Lean_Elab_removeRoot(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Elab_rootNamespace;
x_3 = lean_box(0);
x_4 = l_Lean_Name_replacePrefix___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l___private_Init_Lean_Elab_ResolveName_1__resolveQualifiedName(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
lean_inc(x_3);
x_4 = l_Lean_Name_append___main(x_2, x_3);
x_5 = l_Lean_getAliases(x_1, x_4);
lean_inc(x_1);
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
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_protectedExt;
x_10 = l_Lean_TagDeclarationExtension_isTagged(x_9, x_1, x_4);
lean_dec(x_1);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_5);
return x_11;
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
lean_object* l___private_Init_Lean_Elab_ResolveName_1__resolveQualifiedName___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Elab_ResolveName_1__resolveQualifiedName(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l___private_Init_Lean_Elab_ResolveName_2__resolveUsingNamespace___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_2);
lean_inc(x_1);
x_5 = l___private_Init_Lean_Elab_ResolveName_1__resolveQualifiedName(x_1, x_3, x_2);
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
lean_object* l___private_Init_Lean_Elab_ResolveName_2__resolveUsingNamespace___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Elab_ResolveName_2__resolveUsingNamespace___main(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l___private_Init_Lean_Elab_ResolveName_2__resolveUsingNamespace(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Elab_ResolveName_2__resolveUsingNamespace___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l___private_Init_Lean_Elab_ResolveName_2__resolveUsingNamespace___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Elab_ResolveName_2__resolveUsingNamespace(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l___private_Init_Lean_Elab_ResolveName_3__resolveExact(lean_object* x_1, lean_object* x_2) {
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
lean_dec(x_1);
x_10 = lean_box(0);
return x_10;
}
}
}
lean_object* l___private_Init_Lean_Elab_ResolveName_4__resolveOpenDecls___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_9 = l_List_elem___main___at_Lean_addAliasEntry___spec__18(x_2, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_inc(x_2);
lean_inc(x_1);
x_10 = l___private_Init_Lean_Elab_ResolveName_1__resolveQualifiedName(x_1, x_7, x_2);
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
x_19 = lean_name_eq(x_2, x_17);
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
x_25 = lean_name_eq(x_2, x_23);
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
lean_object* l___private_Init_Lean_Elab_ResolveName_4__resolveOpenDecls(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Elab_ResolveName_4__resolveOpenDecls___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_List_eraseDupsAux___main___at___private_Init_Lean_Elab_ResolveName_5__resolveGlobalNameAux___main___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___rarg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_List_elem___main___at_Lean_addAliasEntry___spec__18(x_5, x_2);
if (x_7 == 0)
{
lean_ctor_set(x_1, 1, x_2);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_free_object(x_1);
lean_dec(x_5);
x_1 = x_6;
goto _start;
}
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
x_12 = l_List_elem___main___at_Lean_addAliasEntry___spec__18(x_10, x_2);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_2);
x_1 = x_11;
x_2 = x_13;
goto _start;
}
else
{
lean_dec(x_10);
x_1 = x_11;
goto _start;
}
}
}
}
}
lean_object* l_List_eraseDups___at___private_Init_Lean_Elab_ResolveName_5__resolveGlobalNameAux___main___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = l_List_eraseDupsAux___main___at___private_Init_Lean_Elab_ResolveName_5__resolveGlobalNameAux___main___spec__2(x_1, x_2);
return x_3;
}
}
lean_object* l_List_map___main___at___private_Init_Lean_Elab_ResolveName_5__resolveGlobalNameAux___main___spec__3(lean_object* x_1, lean_object* x_2) {
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
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_1);
x_8 = l_List_map___main___at___private_Init_Lean_Elab_ResolveName_5__resolveGlobalNameAux___main___spec__3(x_1, x_6);
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
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_1);
x_12 = l_List_map___main___at___private_Init_Lean_Elab_ResolveName_5__resolveGlobalNameAux___main___spec__3(x_1, x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
lean_object* l_List_map___main___at___private_Init_Lean_Elab_ResolveName_5__resolveGlobalNameAux___main___spec__4(lean_object* x_1, lean_object* x_2) {
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
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_1);
x_8 = l_List_map___main___at___private_Init_Lean_Elab_ResolveName_5__resolveGlobalNameAux___main___spec__4(x_1, x_6);
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
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_1);
x_12 = l_List_map___main___at___private_Init_Lean_Elab_ResolveName_5__resolveGlobalNameAux___main___spec__4(x_1, x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
lean_object* l___private_Init_Lean_Elab_ResolveName_5__resolveGlobalNameAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_4) == 1)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_inc(x_4);
lean_inc(x_1);
x_8 = l___private_Init_Lean_Elab_ResolveName_2__resolveUsingNamespace___main(x_1, x_4, x_2);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
lean_inc(x_4);
lean_inc(x_1);
x_9 = l___private_Init_Lean_Elab_ResolveName_3__resolveExact(x_1, x_4);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; 
lean_inc(x_1);
x_10 = l_Lean_Environment_contains(x_1, x_4);
x_11 = l_Lean_getAliases(x_1, x_4);
if (x_10 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_inc(x_3);
lean_inc(x_1);
x_18 = l___private_Init_Lean_Elab_ResolveName_4__resolveOpenDecls___main(x_1, x_4, x_3, x_8);
x_19 = l_List_append___rarg(x_11, x_18);
x_12 = x_19;
goto block_17;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_inc(x_4);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_4);
lean_ctor_set(x_20, 1, x_8);
lean_inc(x_3);
lean_inc(x_1);
x_21 = l___private_Init_Lean_Elab_ResolveName_4__resolveOpenDecls___main(x_1, x_4, x_3, x_20);
x_22 = l_List_append___rarg(x_11, x_21);
x_12 = x_22;
goto block_17;
}
block_17:
{
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_5);
x_4 = x_6;
x_5 = x_13;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_15 = l_List_eraseDups___at___private_Init_Lean_Elab_ResolveName_5__resolveGlobalNameAux___main___spec__1(x_12);
x_16 = l_List_map___main___at___private_Init_Lean_Elab_ResolveName_5__resolveGlobalNameAux___main___spec__3(x_5, x_15);
return x_16;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_23 = lean_ctor_get(x_9, 0);
lean_inc(x_23);
lean_dec(x_9);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_5);
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
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_27 = l_List_eraseDups___at___private_Init_Lean_Elab_ResolveName_5__resolveGlobalNameAux___main___spec__1(x_8);
x_28 = l_List_map___main___at___private_Init_Lean_Elab_ResolveName_5__resolveGlobalNameAux___main___spec__4(x_5, x_27);
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
lean_object* l___private_Init_Lean_Elab_ResolveName_5__resolveGlobalNameAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Lean_Elab_ResolveName_5__resolveGlobalNameAux___main(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* l___private_Init_Lean_Elab_ResolveName_5__resolveGlobalNameAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Lean_Elab_ResolveName_5__resolveGlobalNameAux___main(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l___private_Init_Lean_Elab_ResolveName_5__resolveGlobalNameAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Lean_Elab_ResolveName_5__resolveGlobalNameAux(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_Elab_resolveGlobalName(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = l___private_Init_Lean_Elab_ResolveName_5__resolveGlobalNameAux___main(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_Elab_resolveGlobalName___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_resolveGlobalName(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Elab_resolveNamespaceUsingScope___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_box(0);
return x_4;
}
case 1:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_2);
x_6 = l_Lean_Name_append___main(x_3, x_2);
x_7 = l_Lean_isNamespace(x_1, x_6);
if (x_7 == 0)
{
lean_dec(x_6);
x_3 = x_5;
goto _start;
}
else
{
lean_object* x_9; 
lean_dec(x_2);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_6);
return x_9;
}
}
default: 
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
x_10 = lean_box(0);
x_11 = l_unreachable_x21___rarg(x_10);
return x_11;
}
}
}
}
lean_object* l_Lean_Elab_resolveNamespaceUsingScope___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_resolveNamespaceUsingScope___main(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_resolveNamespaceUsingScope(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_resolveNamespaceUsingScope___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Elab_resolveNamespaceUsingScope___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_resolveNamespaceUsingScope(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_resolveNamespaceUsingOpenDecls___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_3, 0);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 1);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_2);
x_9 = l_Lean_Name_append___main(x_8, x_2);
x_10 = l_Lean_isNamespace(x_1, x_9);
if (x_10 == 0)
{
lean_dec(x_9);
x_3 = x_7;
goto _start;
}
else
{
lean_object* x_12; 
lean_dec(x_2);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_9);
return x_12;
}
}
else
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_3, 1);
x_3 = x_13;
goto _start;
}
}
else
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_3, 1);
x_3 = x_15;
goto _start;
}
}
}
}
lean_object* l_Lean_Elab_resolveNamespaceUsingOpenDecls___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_resolveNamespaceUsingOpenDecls___main(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_resolveNamespaceUsingOpenDecls(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_resolveNamespaceUsingOpenDecls___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Elab_resolveNamespaceUsingOpenDecls___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_resolveNamespaceUsingOpenDecls(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_resolveNamespace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_isNamespace(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_inc(x_4);
x_6 = l_Lean_Elab_resolveNamespaceUsingScope___main(x_1, x_4, x_2);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = l_Lean_Elab_resolveNamespaceUsingOpenDecls___main(x_1, x_4, x_3);
return x_7;
}
else
{
lean_dec(x_4);
return x_6;
}
}
else
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_4);
return x_8;
}
}
}
lean_object* l_Lean_Elab_resolveNamespace___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_resolveNamespace(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* initialize_Init_Lean_Modifiers(lean_object*);
lean_object* initialize_Init_Lean_Elab_Alias(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Elab_ResolveName(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Modifiers(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Elab_Alias(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_OpenDecl_Inhabited___closed__1 = _init_l_Lean_Elab_OpenDecl_Inhabited___closed__1();
lean_mark_persistent(l_Lean_Elab_OpenDecl_Inhabited___closed__1);
l_Lean_Elab_OpenDecl_Inhabited = _init_l_Lean_Elab_OpenDecl_Inhabited();
lean_mark_persistent(l_Lean_Elab_OpenDecl_Inhabited);
l_Lean_Elab_OpenDecl_HasToString___closed__1 = _init_l_Lean_Elab_OpenDecl_HasToString___closed__1();
lean_mark_persistent(l_Lean_Elab_OpenDecl_HasToString___closed__1);
l_Lean_Elab_OpenDecl_HasToString___closed__2 = _init_l_Lean_Elab_OpenDecl_HasToString___closed__2();
lean_mark_persistent(l_Lean_Elab_OpenDecl_HasToString___closed__2);
l_Lean_Elab_rootNamespace___closed__1 = _init_l_Lean_Elab_rootNamespace___closed__1();
lean_mark_persistent(l_Lean_Elab_rootNamespace___closed__1);
l_Lean_Elab_rootNamespace___closed__2 = _init_l_Lean_Elab_rootNamespace___closed__2();
lean_mark_persistent(l_Lean_Elab_rootNamespace___closed__2);
l_Lean_Elab_rootNamespace = _init_l_Lean_Elab_rootNamespace();
lean_mark_persistent(l_Lean_Elab_rootNamespace);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
