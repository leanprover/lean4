// Lean compiler output
// Module: Init.Lean.Scopes
// Imports: Init.Lean.Environment
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
lean_object* l_Lean_scopeManagerExt___closed__6;
lean_object* l_Lean_scopeManagerExt___closed__4;
lean_object* l_Lean_registerEnvExtensionUnsafe___at_Lean_regScopeManagerExtension___spec__7(lean_object*, lean_object*);
uint8_t lean_name_dec_eq(lean_object*, lean_object*);
lean_object* l_Array_anyMAux___main___at_Lean_regScopeManagerExtension___spec__6___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
extern lean_object* l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
extern lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
lean_object* l_List_foldl___main___at_Lean_Environment_toValidNamespace___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_regScopeManagerExtension___closed__4;
extern lean_object* l_Lean_EnvExtension_Inhabited___rarg___closed__1;
lean_object* l_Lean_scopeManagerExt___closed__3;
lean_object* l_Lean_Environment_popScopeCore___lambda__1(lean_object*);
lean_object* l_Lean_scopeManagerExt___elambda__1(lean_object*);
uint8_t lean_has_open_scopes(lean_object*);
lean_object* l_Lean_Environment_popScopeCore___closed__1;
lean_object* l_Lean_Environment_pushScopeCore___lambda__1(lean_object*, lean_object*, uint8_t, lean_object*);
extern lean_object* l___private_Init_Lean_Environment_5__envExtensionsRef;
lean_object* lean_get_namespaces(lean_object*);
lean_object* lean_get_scope_header(lean_object*);
extern lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__4;
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___rarg(lean_object*, lean_object*);
lean_object* l_Lean_scopeManagerExt;
lean_object* l_Lean_registerEnvExtensionUnsafe___at_Lean_regScopeManagerExtension___spec__7___closed__2;
lean_object* l_Lean_ScopeManagerState_Inhabited;
lean_object* l_Lean_Environment_registerNamespaceAux(lean_object*, lean_object*);
lean_object* lean_io_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_get_namespace(lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__3(lean_object*, lean_object*);
lean_object* lean_io_initializing(lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_modifyState___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_regScopeManagerExtension___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_scopeManagerExt___closed__2;
lean_object* l_Lean_registerEnvExtensionUnsafe___at_Lean_regScopeManagerExtension___spec__7___closed__3;
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_Environment_inSection___boxed(lean_object*);
lean_object* l_RBNode_insert___at_Lean_NameSet_insert___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_regScopeManagerExtension___lambda__2___boxed(lean_object*);
lean_object* l_Lean_regScopeManagerExtension(lean_object*);
lean_object* l_Lean_Environment_getNamespaceSet(lean_object*);
extern lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__3;
lean_object* l_Lean_mkStateFromImportedEntries___at_Lean_regScopeManagerExtension___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_scopeManagerExt___elambda__3___boxed(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_regScopeManagerExtension___spec__5(lean_object*, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l___private_Init_Lean_Environment_8__persistentEnvExtensionsRef;
uint8_t lean_is_namespace(lean_object*, lean_object*);
extern lean_object* l_Lean_regNamespacesExtension___closed__4;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_regScopeManagerExtension___closed__5;
uint8_t l_List_isEmpty___rarg(lean_object*);
uint8_t l_Array_anyMAux___main___at_Lean_regScopeManagerExtension___spec__6(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerEnvExtensionUnsafe___at_Lean_regScopeManagerExtension___spec__7___closed__1;
extern lean_object* l_Lean_registerSimplePersistentEnvExtension___rarg___closed__1;
lean_object* l_Lean_registerSimplePersistentEnvExtension___at_Lean_regScopeManagerExtension___spec__4(lean_object*, lean_object*);
lean_object* l_Lean_mkStateFromImportedEntries___at_Lean_regScopeManagerExtension___spec__1(lean_object*, lean_object*);
lean_object* lean_register_namespace(lean_object*, lean_object*);
lean_object* l_Lean_regScopeManagerExtension___lambda__2(lean_object*);
lean_object* l_Lean_scopeManagerExt___elambda__2___boxed(lean_object*);
lean_object* l_Lean_regScopeManagerExtension___closed__3;
lean_object* l_Lean_scopeManagerExt___elambda__4___boxed(lean_object*);
lean_object* l_List_foldl___main___at_Lean_Environment_toValidNamespace___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ScopeManagerState_saveNamespace(lean_object*, lean_object*);
lean_object* l_EState_bind___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_regScopeManagerExtension___closed__1;
lean_object* l_Lean_Environment_popScopeCore(lean_object*);
lean_object* l_Lean_Environment_getNamespaceSet___boxed(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_scopeManagerExt___closed__1;
lean_object* l_Lean_scopeManagerExt___elambda__3(lean_object*, lean_object*);
lean_object* l_Lean_ScopeManagerState_Inhabited___closed__1;
lean_object* l_Lean_scopeManagerExt___elambda__1___boxed(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Environment_registerNamespace___main(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_regScopeManagerExtension___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_regScopeManagerExtension___closed__2;
lean_object* l_Array_iterateMAux___main___at_Lean_regScopeManagerExtension___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
extern lean_object* l_Lean_Name_toString___closed__1;
lean_object* l_Lean_Environment_pushScopeCore___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_regScopeManagerExtension___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_scopeManagerExt___elambda__2(lean_object*);
uint8_t lean_in_section(lean_object*);
lean_object* l_Lean_scopeManagerExt___closed__5;
lean_object* l_Lean_Environment_pushScopeCore(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Environment_isNamespace___boxed(lean_object*, lean_object*);
lean_object* l_List_tail_x21___rarg(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_regScopeManagerExtension___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_hasOpenScopes___boxed(lean_object*);
lean_object* l_Lean_Name_append___main(lean_object*, lean_object*);
lean_object* l_Lean_Environment_pushScopeCore___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_registerEnvExtensionUnsafe___rarg___closed__1;
lean_object* lean_to_valid_namespace(lean_object*, lean_object*);
lean_object* lean_io_ref_reset(lean_object*, lean_object*);
lean_object* l_Lean_scopeManagerExt___elambda__4(lean_object*);
lean_object* l_Lean_scopeManagerExt___elambda__4___rarg(lean_object*);
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* _init_l_Lean_ScopeManagerState_Inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_ScopeManagerState_Inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_ScopeManagerState_Inhabited___closed__1;
return x_1;
}
}
lean_object* l_Lean_ScopeManagerState_saveNamespace(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_box(0);
x_6 = l_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_4, x_2, x_5);
lean_ctor_set(x_1, 0, x_6);
return x_1;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_ctor_get(x_1, 2);
x_10 = lean_ctor_get(x_1, 3);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = l_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_7, x_2, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_9);
lean_ctor_set(x_13, 3, x_10);
return x_13;
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_regScopeManagerExtension___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_dec(x_3);
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = l_Lean_ScopeManagerState_saveNamespace(x_4, x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_3, x_9);
lean_dec(x_3);
x_3 = x_10;
x_4 = x_8;
goto _start;
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_regScopeManagerExtension___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_dec(x_3);
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_iterateMAux___main___at_Lean_regScopeManagerExtension___spec__2(x_7, x_7, x_8, x_4);
lean_dec(x_7);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_3, x_10);
lean_dec(x_3);
x_3 = x_11;
x_4 = x_9;
goto _start;
}
}
}
lean_object* l_Lean_mkStateFromImportedEntries___at_Lean_regScopeManagerExtension___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Array_iterateMAux___main___at_Lean_regScopeManagerExtension___spec__3(x_2, x_2, x_3, x_1);
return x_4;
}
}
uint8_t l_Array_anyMAux___main___at_Lean_regScopeManagerExtension___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_3);
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_name_dec_eq(x_8, x_9);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_3, x_11);
lean_dec(x_3);
x_3 = x_12;
goto _start;
}
else
{
lean_dec(x_3);
return x_10;
}
}
}
}
lean_object* _init_l_Lean_registerEnvExtensionUnsafe___at_Lean_regScopeManagerExtension___spec__7___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_1);
lean_ctor_set(x_3, 3, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_registerEnvExtensionUnsafe___at_Lean_regScopeManagerExtension___spec__7___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_registerEnvExtensionUnsafe___at_Lean_regScopeManagerExtension___spec__7___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_registerEnvExtensionUnsafe___at_Lean_regScopeManagerExtension___spec__7___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_registerEnvExtensionUnsafe___at_Lean_regScopeManagerExtension___spec__7___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_registerEnvExtensionUnsafe___at_Lean_regScopeManagerExtension___spec__7(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_initializing(x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_unbox(x_4);
lean_dec(x_4);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_1);
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_3, 0);
lean_dec(x_7);
x_8 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__1;
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_8);
return x_3;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_dec(x_3);
x_10 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__1;
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_dec(x_3);
x_13 = l___private_Init_Lean_Environment_5__envExtensionsRef;
x_14 = lean_io_ref_get(x_13, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_array_get_size(x_15);
lean_dec(x_15);
x_18 = l_Lean_registerEnvExtensionUnsafe___at_Lean_regScopeManagerExtension___spec__7___closed__3;
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_1);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_io_ref_get(x_13, x_16);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_io_ref_reset(x_13, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean_inc(x_19);
x_26 = x_19;
x_27 = lean_array_push(x_21, x_26);
x_28 = lean_io_ref_set(x_13, x_27, x_24);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
lean_ctor_set(x_28, 0, x_19);
return x_28;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_19);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_19);
x_33 = !lean_is_exclusive(x_28);
if (x_33 == 0)
{
return x_28;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_28, 0);
x_35 = lean_ctor_get(x_28, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_28);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_21);
lean_dec(x_19);
x_37 = !lean_is_exclusive(x_23);
if (x_37 == 0)
{
return x_23;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_23, 0);
x_39 = lean_ctor_get(x_23, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_23);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_19);
x_41 = !lean_is_exclusive(x_20);
if (x_41 == 0)
{
return x_20;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_20, 0);
x_43 = lean_ctor_get(x_20, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_20);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_14);
if (x_45 == 0)
{
return x_14;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_14, 0);
x_47 = lean_ctor_get(x_14, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_14);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_3);
if (x_49 == 0)
{
return x_3;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_3, 0);
x_51 = lean_ctor_get(x_3, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_3);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_regScopeManagerExtension___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l___private_Init_Lean_Environment_8__persistentEnvExtensionsRef;
x_4 = lean_io_ref_get(x_3, x_2);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_anyMAux___main___at_Lean_regScopeManagerExtension___spec__6(x_1, x_6, x_8);
lean_dec(x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_free_object(x_4);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = l_Array_empty___closed__1;
lean_inc(x_10);
x_12 = lean_apply_1(x_10, x_11);
x_13 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
x_14 = lean_alloc_closure((void*)(l_EState_bind___rarg), 3, 2);
lean_closure_set(x_14, 0, x_12);
lean_closure_set(x_14, 1, x_13);
x_15 = l_Lean_registerEnvExtensionUnsafe___at_Lean_regScopeManagerExtension___spec__7(x_14, x_7);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 2);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 3);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 4);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_22, 0, x_16);
lean_ctor_set(x_22, 1, x_18);
lean_ctor_set(x_22, 2, x_10);
lean_ctor_set(x_22, 3, x_19);
lean_ctor_set(x_22, 4, x_20);
lean_ctor_set(x_22, 5, x_21);
x_23 = lean_io_ref_get(x_3, x_17);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_io_ref_reset(x_3, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
lean_inc(x_22);
x_29 = x_22;
x_30 = lean_array_push(x_24, x_29);
x_31 = lean_io_ref_set(x_3, x_30, x_27);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
lean_ctor_set(x_31, 0, x_22);
return x_31;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_22);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_22);
x_36 = !lean_is_exclusive(x_31);
if (x_36 == 0)
{
return x_31;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_31, 0);
x_38 = lean_ctor_get(x_31, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_31);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_24);
lean_dec(x_22);
x_40 = !lean_is_exclusive(x_26);
if (x_40 == 0)
{
return x_26;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_26, 0);
x_42 = lean_ctor_get(x_26, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_26);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_22);
x_44 = !lean_is_exclusive(x_23);
if (x_44 == 0)
{
return x_23;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_23, 0);
x_46 = lean_ctor_get(x_23, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_23);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_10);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_15);
if (x_48 == 0)
{
return x_15;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_15, 0);
x_50 = lean_ctor_get(x_15, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_15);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_52 = lean_ctor_get(x_1, 0);
lean_inc(x_52);
lean_dec(x_1);
x_53 = l_Lean_Name_toString___closed__1;
x_54 = l_Lean_Name_toStringWithSep___main(x_53, x_52);
x_55 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__3;
x_56 = lean_string_append(x_55, x_54);
lean_dec(x_54);
x_57 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__4;
x_58 = lean_string_append(x_56, x_57);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_58);
return x_4;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_59 = lean_ctor_get(x_4, 0);
x_60 = lean_ctor_get(x_4, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_4);
x_61 = lean_unsigned_to_nat(0u);
x_62 = l_Array_anyMAux___main___at_Lean_regScopeManagerExtension___spec__6(x_1, x_59, x_61);
lean_dec(x_59);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_63 = lean_ctor_get(x_1, 1);
lean_inc(x_63);
x_64 = l_Array_empty___closed__1;
lean_inc(x_63);
x_65 = lean_apply_1(x_63, x_64);
x_66 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
x_67 = lean_alloc_closure((void*)(l_EState_bind___rarg), 3, 2);
lean_closure_set(x_67, 0, x_65);
lean_closure_set(x_67, 1, x_66);
x_68 = l_Lean_registerEnvExtensionUnsafe___at_Lean_regScopeManagerExtension___spec__7(x_67, x_60);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_ctor_get(x_1, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_1, 2);
lean_inc(x_72);
x_73 = lean_ctor_get(x_1, 3);
lean_inc(x_73);
x_74 = lean_ctor_get(x_1, 4);
lean_inc(x_74);
lean_dec(x_1);
x_75 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_75, 0, x_69);
lean_ctor_set(x_75, 1, x_71);
lean_ctor_set(x_75, 2, x_63);
lean_ctor_set(x_75, 3, x_72);
lean_ctor_set(x_75, 4, x_73);
lean_ctor_set(x_75, 5, x_74);
x_76 = lean_io_ref_get(x_3, x_70);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = lean_io_ref_reset(x_3, x_78);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
lean_dec(x_79);
x_81 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
lean_inc(x_75);
x_82 = x_75;
x_83 = lean_array_push(x_77, x_82);
x_84 = lean_io_ref_set(x_3, x_83, x_80);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_86 = x_84;
} else {
 lean_dec_ref(x_84);
 x_86 = lean_box(0);
}
if (lean_is_scalar(x_86)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_86;
}
lean_ctor_set(x_87, 0, x_75);
lean_ctor_set(x_87, 1, x_85);
return x_87;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_75);
x_88 = lean_ctor_get(x_84, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_84, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_90 = x_84;
} else {
 lean_dec_ref(x_84);
 x_90 = lean_box(0);
}
if (lean_is_scalar(x_90)) {
 x_91 = lean_alloc_ctor(1, 2, 0);
} else {
 x_91 = x_90;
}
lean_ctor_set(x_91, 0, x_88);
lean_ctor_set(x_91, 1, x_89);
return x_91;
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_77);
lean_dec(x_75);
x_92 = lean_ctor_get(x_79, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_79, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_94 = x_79;
} else {
 lean_dec_ref(x_79);
 x_94 = lean_box(0);
}
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(1, 2, 0);
} else {
 x_95 = x_94;
}
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_93);
return x_95;
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_75);
x_96 = lean_ctor_get(x_76, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_76, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_98 = x_76;
} else {
 lean_dec_ref(x_76);
 x_98 = lean_box(0);
}
if (lean_is_scalar(x_98)) {
 x_99 = lean_alloc_ctor(1, 2, 0);
} else {
 x_99 = x_98;
}
lean_ctor_set(x_99, 0, x_96);
lean_ctor_set(x_99, 1, x_97);
return x_99;
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_63);
lean_dec(x_1);
x_100 = lean_ctor_get(x_68, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_68, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_102 = x_68;
} else {
 lean_dec_ref(x_68);
 x_102 = lean_box(0);
}
if (lean_is_scalar(x_102)) {
 x_103 = lean_alloc_ctor(1, 2, 0);
} else {
 x_103 = x_102;
}
lean_ctor_set(x_103, 0, x_100);
lean_ctor_set(x_103, 1, x_101);
return x_103;
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_104 = lean_ctor_get(x_1, 0);
lean_inc(x_104);
lean_dec(x_1);
x_105 = l_Lean_Name_toString___closed__1;
x_106 = l_Lean_Name_toStringWithSep___main(x_105, x_104);
x_107 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__3;
x_108 = lean_string_append(x_107, x_106);
lean_dec(x_106);
x_109 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__4;
x_110 = lean_string_append(x_108, x_109);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_60);
return x_111;
}
}
}
else
{
uint8_t x_112; 
lean_dec(x_1);
x_112 = !lean_is_exclusive(x_4);
if (x_112 == 0)
{
return x_4;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_4, 0);
x_114 = lean_ctor_get(x_4, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_4);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
}
lean_object* l_Lean_registerSimplePersistentEnvExtension___at_Lean_regScopeManagerExtension___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_inc(x_1);
x_4 = lean_alloc_closure((void*)(l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__1), 3, 1);
lean_closure_set(x_4, 0, x_1);
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__2), 3, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = lean_alloc_closure((void*)(l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__3), 2, 1);
lean_closure_set(x_6, 0, x_1);
x_7 = l_Lean_registerSimplePersistentEnvExtension___rarg___closed__1;
x_8 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_4);
lean_ctor_set(x_8, 2, x_5);
lean_ctor_set(x_8, 3, x_6);
lean_ctor_set(x_8, 4, x_7);
x_9 = l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_regScopeManagerExtension___spec__5(x_8, x_2);
return x_9;
}
}
lean_object* l_Lean_regScopeManagerExtension___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_box(0);
x_6 = l_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_4, x_2, x_5);
lean_ctor_set(x_1, 0, x_6);
return x_1;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_ctor_get(x_1, 2);
x_10 = lean_ctor_get(x_1, 3);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = l_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_7, x_2, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_9);
lean_ctor_set(x_13, 3, x_10);
return x_13;
}
}
}
lean_object* l_Lean_regScopeManagerExtension___lambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_ScopeManagerState_Inhabited___closed__1;
x_4 = l_Array_iterateMAux___main___at_Lean_regScopeManagerExtension___spec__3(x_1, x_1, x_2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_regScopeManagerExtension___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("scopes");
return x_1;
}
}
lean_object* _init_l_Lean_regScopeManagerExtension___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_regScopeManagerExtension___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_regScopeManagerExtension___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_regScopeManagerExtension___lambda__1), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_regScopeManagerExtension___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_regScopeManagerExtension___lambda__2___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_regScopeManagerExtension___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_regScopeManagerExtension___closed__2;
x_2 = l_Lean_regScopeManagerExtension___closed__3;
x_3 = l_Lean_regScopeManagerExtension___closed__4;
x_4 = l_Lean_regNamespacesExtension___closed__4;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
lean_object* l_Lean_regScopeManagerExtension(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_regScopeManagerExtension___closed__5;
x_3 = l_Lean_registerSimplePersistentEnvExtension___at_Lean_regScopeManagerExtension___spec__4(x_2, x_1);
return x_3;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_regScopeManagerExtension___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_iterateMAux___main___at_Lean_regScopeManagerExtension___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_regScopeManagerExtension___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_iterateMAux___main___at_Lean_regScopeManagerExtension___spec__3(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_mkStateFromImportedEntries___at_Lean_regScopeManagerExtension___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkStateFromImportedEntries___at_Lean_regScopeManagerExtension___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_anyMAux___main___at_Lean_regScopeManagerExtension___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Array_anyMAux___main___at_Lean_regScopeManagerExtension___spec__6(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* l_Lean_regScopeManagerExtension___lambda__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_regScopeManagerExtension___lambda__2(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_scopeManagerExt___elambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
lean_object* l_Lean_scopeManagerExt___elambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_empty___closed__1;
return x_2;
}
}
lean_object* l_Lean_scopeManagerExt___elambda__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
lean_object* l_Lean_scopeManagerExt___elambda__4___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_String_splitAux___main___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_scopeManagerExt___elambda__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_scopeManagerExt___elambda__4___rarg), 1, 0);
return x_2;
}
}
lean_object* _init_l_Lean_scopeManagerExt___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_EnvExtension_Inhabited___rarg___closed__1;
x_3 = l_Lean_registerEnvExtensionUnsafe___at_Lean_regScopeManagerExtension___spec__7___closed__3;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_scopeManagerExt___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_scopeManagerExt___elambda__4___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_scopeManagerExt___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_scopeManagerExt___elambda__3___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_scopeManagerExt___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_scopeManagerExt___elambda__2___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_scopeManagerExt___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_scopeManagerExt___elambda__1___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_scopeManagerExt___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_Lean_scopeManagerExt___closed__1;
x_2 = lean_box(0);
x_3 = l_Lean_scopeManagerExt___closed__2;
x_4 = l_Lean_scopeManagerExt___closed__3;
x_5 = l_Lean_scopeManagerExt___closed__4;
x_6 = l_Lean_scopeManagerExt___closed__5;
x_7 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_3);
lean_ctor_set(x_7, 3, x_4);
lean_ctor_set(x_7, 4, x_5);
lean_ctor_set(x_7, 5, x_6);
return x_7;
}
}
lean_object* l_Lean_scopeManagerExt___elambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_scopeManagerExt___elambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_scopeManagerExt___elambda__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_scopeManagerExt___elambda__2(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_scopeManagerExt___elambda__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_scopeManagerExt___elambda__3(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_scopeManagerExt___elambda__4___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_scopeManagerExt___elambda__4(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* lean_get_namespaces(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_scopeManagerExt;
x_3 = l_Lean_SimplePersistentEnvExtension_getState___rarg(x_2, x_1);
lean_dec(x_1);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_Lean_Environment_getNamespaceSet(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_scopeManagerExt;
x_3 = l_Lean_SimplePersistentEnvExtension_getState___rarg(x_2, x_1);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_Lean_Environment_getNamespaceSet___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Environment_getNamespaceSet(x_1);
lean_dec(x_1);
return x_2;
}
}
uint8_t lean_is_namespace(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_Environment_getNamespaceSet(x_1);
lean_dec(x_1);
x_4 = l_Lean_NameSet_contains(x_3, x_2);
lean_dec(x_2);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_Lean_Environment_isNamespace___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_is_namespace(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t lean_in_section(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_scopeManagerExt;
x_3 = l_Lean_SimplePersistentEnvExtension_getState___rarg(x_2, x_1);
lean_dec(x_1);
x_4 = lean_ctor_get(x_3, 3);
lean_inc(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_unbox(x_6);
lean_dec(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
else
{
uint8_t x_9; 
x_9 = 0;
return x_9;
}
}
}
}
lean_object* l_Lean_Environment_inSection___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_in_section(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t lean_has_open_scopes(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_get_namespaces(x_1);
x_3 = l_List_isEmpty___rarg(x_2);
lean_dec(x_2);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = 1;
return x_4;
}
else
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
}
}
lean_object* l_Lean_Environment_hasOpenScopes___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_has_open_scopes(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* lean_get_namespace(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_get_namespaces(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
return x_4;
}
}
}
lean_object* lean_get_scope_header(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_scopeManagerExt;
x_3 = l_Lean_SimplePersistentEnvExtension_getState___rarg(x_2, x_1);
lean_dec(x_1);
x_4 = lean_ctor_get(x_3, 2);
lean_inc(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
return x_6;
}
}
}
lean_object* l_List_foldl___main___at_Lean_Environment_toValidNamespace___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_dec(x_1);
return x_3;
}
else
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_1);
x_7 = l_Lean_Name_append___main(x_5, x_1);
x_8 = l_Lean_NameSet_contains(x_2, x_7);
if (x_8 == 0)
{
lean_dec(x_7);
x_4 = x_6;
goto _start;
}
else
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_7);
x_3 = x_10;
x_4 = x_6;
goto _start;
}
}
else
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_4, 1);
x_4 = x_12;
goto _start;
}
}
}
}
lean_object* lean_to_valid_namespace(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = l_Lean_scopeManagerExt;
x_4 = l_Lean_SimplePersistentEnvExtension_getState___rarg(x_3, x_1);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = l_Lean_NameSet_contains(x_5, x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_box(0);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
lean_dec(x_4);
x_9 = l_List_foldl___main___at_Lean_Environment_toValidNamespace___spec__1(x_2, x_5, x_7, x_8);
lean_dec(x_8);
lean_dec(x_5);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_5);
lean_dec(x_4);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_2);
return x_10;
}
}
}
lean_object* l_List_foldl___main___at_Lean_Environment_toValidNamespace___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_foldl___main___at_Lean_Environment_toValidNamespace___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Environment_registerNamespaceAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_Environment_getNamespaceSet(x_1);
x_4 = l_Lean_NameSet_contains(x_3, x_2);
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_scopeManagerExt;
x_6 = l_Lean_PersistentEnvExtension_addEntry___rarg(x_5, x_1, x_2);
return x_6;
}
else
{
lean_dec(x_2);
return x_1;
}
}
}
lean_object* l_Lean_Environment_registerNamespace___main(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = l_Lean_Environment_registerNamespaceAux(x_1, x_2);
x_1 = x_4;
x_2 = x_3;
goto _start;
}
else
{
lean_dec(x_2);
return x_1;
}
}
}
lean_object* lean_register_namespace(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Environment_registerNamespace___main(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Environment_pushScopeCore___lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_4, 1);
x_7 = lean_ctor_get(x_4, 2);
x_8 = lean_ctor_get(x_4, 3);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_6);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_7);
x_11 = lean_box(x_3);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_8);
lean_ctor_set(x_4, 3, x_12);
lean_ctor_set(x_4, 2, x_10);
lean_ctor_set(x_4, 1, x_9);
return x_4;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_ctor_get(x_4, 1);
x_15 = lean_ctor_get(x_4, 2);
x_16 = lean_ctor_get(x_4, 3);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_4);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_14);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_2);
lean_ctor_set(x_18, 1, x_15);
x_19 = lean_box(x_3);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_16);
x_21 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_21, 0, x_13);
lean_ctor_set(x_21, 1, x_17);
lean_ctor_set(x_21, 2, x_18);
lean_ctor_set(x_21, 3, x_20);
return x_21;
}
}
}
lean_object* l_Lean_Environment_pushScopeCore(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_1);
x_4 = lean_get_namespace(x_1);
if (x_3 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_inc(x_4);
x_5 = l_Lean_Environment_registerNamespaceAux(x_1, x_4);
x_6 = lean_box(x_3);
x_7 = lean_alloc_closure((void*)(l_Lean_Environment_pushScopeCore___lambda__1___boxed), 4, 3);
lean_closure_set(x_7, 0, x_4);
lean_closure_set(x_7, 1, x_2);
lean_closure_set(x_7, 2, x_6);
x_8 = l_Lean_scopeManagerExt;
x_9 = l_Lean_SimplePersistentEnvExtension_modifyState___rarg(x_8, x_5, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_inc(x_2);
x_10 = l_Lean_Name_append___main(x_4, x_2);
lean_dec(x_4);
lean_inc(x_10);
x_11 = l_Lean_Environment_registerNamespaceAux(x_1, x_10);
x_12 = lean_box(x_3);
x_13 = lean_alloc_closure((void*)(l_Lean_Environment_pushScopeCore___lambda__1___boxed), 4, 3);
lean_closure_set(x_13, 0, x_10);
lean_closure_set(x_13, 1, x_2);
lean_closure_set(x_13, 2, x_12);
x_14 = l_Lean_scopeManagerExt;
x_15 = l_Lean_SimplePersistentEnvExtension_modifyState___rarg(x_14, x_11, x_13);
return x_15;
}
}
}
lean_object* l_Lean_Environment_pushScopeCore___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_3);
lean_dec(x_3);
x_6 = l_Lean_Environment_pushScopeCore___lambda__1(x_1, x_2, x_5, x_4);
return x_6;
}
}
lean_object* l_Lean_Environment_pushScopeCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
lean_dec(x_3);
x_5 = l_Lean_Environment_pushScopeCore(x_1, x_2, x_4);
return x_5;
}
}
lean_object* l_Lean_Environment_popScopeCore___lambda__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_ctor_get(x_1, 3);
x_6 = l_List_tail_x21___rarg(x_3);
lean_dec(x_3);
x_7 = l_List_tail_x21___rarg(x_4);
lean_dec(x_4);
x_8 = l_List_tail_x21___rarg(x_5);
lean_dec(x_5);
lean_ctor_set(x_1, 3, x_8);
lean_ctor_set(x_1, 2, x_7);
lean_ctor_set(x_1, 1, x_6);
return x_1;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_1, 2);
x_12 = lean_ctor_get(x_1, 3);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_13 = l_List_tail_x21___rarg(x_10);
lean_dec(x_10);
x_14 = l_List_tail_x21___rarg(x_11);
lean_dec(x_11);
x_15 = l_List_tail_x21___rarg(x_12);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_13);
lean_ctor_set(x_16, 2, x_14);
lean_ctor_set(x_16, 3, x_15);
return x_16;
}
}
}
lean_object* _init_l_Lean_Environment_popScopeCore___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Environment_popScopeCore___lambda__1), 1, 0);
return x_1;
}
}
lean_object* l_Lean_Environment_popScopeCore(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
lean_inc(x_1);
x_2 = lean_get_namespaces(x_1);
x_3 = l_List_isEmpty___rarg(x_2);
lean_dec(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Lean_scopeManagerExt;
x_5 = l_Lean_Environment_popScopeCore___closed__1;
x_6 = l_Lean_SimplePersistentEnvExtension_modifyState___rarg(x_4, x_1, x_5);
return x_6;
}
else
{
return x_1;
}
}
}
lean_object* initialize_Init_Lean_Environment(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Scopes(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Environment(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_ScopeManagerState_Inhabited___closed__1 = _init_l_Lean_ScopeManagerState_Inhabited___closed__1();
lean_mark_persistent(l_Lean_ScopeManagerState_Inhabited___closed__1);
l_Lean_ScopeManagerState_Inhabited = _init_l_Lean_ScopeManagerState_Inhabited();
lean_mark_persistent(l_Lean_ScopeManagerState_Inhabited);
l_Lean_registerEnvExtensionUnsafe___at_Lean_regScopeManagerExtension___spec__7___closed__1 = _init_l_Lean_registerEnvExtensionUnsafe___at_Lean_regScopeManagerExtension___spec__7___closed__1();
lean_mark_persistent(l_Lean_registerEnvExtensionUnsafe___at_Lean_regScopeManagerExtension___spec__7___closed__1);
l_Lean_registerEnvExtensionUnsafe___at_Lean_regScopeManagerExtension___spec__7___closed__2 = _init_l_Lean_registerEnvExtensionUnsafe___at_Lean_regScopeManagerExtension___spec__7___closed__2();
lean_mark_persistent(l_Lean_registerEnvExtensionUnsafe___at_Lean_regScopeManagerExtension___spec__7___closed__2);
l_Lean_registerEnvExtensionUnsafe___at_Lean_regScopeManagerExtension___spec__7___closed__3 = _init_l_Lean_registerEnvExtensionUnsafe___at_Lean_regScopeManagerExtension___spec__7___closed__3();
lean_mark_persistent(l_Lean_registerEnvExtensionUnsafe___at_Lean_regScopeManagerExtension___spec__7___closed__3);
l_Lean_regScopeManagerExtension___closed__1 = _init_l_Lean_regScopeManagerExtension___closed__1();
lean_mark_persistent(l_Lean_regScopeManagerExtension___closed__1);
l_Lean_regScopeManagerExtension___closed__2 = _init_l_Lean_regScopeManagerExtension___closed__2();
lean_mark_persistent(l_Lean_regScopeManagerExtension___closed__2);
l_Lean_regScopeManagerExtension___closed__3 = _init_l_Lean_regScopeManagerExtension___closed__3();
lean_mark_persistent(l_Lean_regScopeManagerExtension___closed__3);
l_Lean_regScopeManagerExtension___closed__4 = _init_l_Lean_regScopeManagerExtension___closed__4();
lean_mark_persistent(l_Lean_regScopeManagerExtension___closed__4);
l_Lean_regScopeManagerExtension___closed__5 = _init_l_Lean_regScopeManagerExtension___closed__5();
lean_mark_persistent(l_Lean_regScopeManagerExtension___closed__5);
l_Lean_scopeManagerExt___closed__1 = _init_l_Lean_scopeManagerExt___closed__1();
lean_mark_persistent(l_Lean_scopeManagerExt___closed__1);
l_Lean_scopeManagerExt___closed__2 = _init_l_Lean_scopeManagerExt___closed__2();
lean_mark_persistent(l_Lean_scopeManagerExt___closed__2);
l_Lean_scopeManagerExt___closed__3 = _init_l_Lean_scopeManagerExt___closed__3();
lean_mark_persistent(l_Lean_scopeManagerExt___closed__3);
l_Lean_scopeManagerExt___closed__4 = _init_l_Lean_scopeManagerExt___closed__4();
lean_mark_persistent(l_Lean_scopeManagerExt___closed__4);
l_Lean_scopeManagerExt___closed__5 = _init_l_Lean_scopeManagerExt___closed__5();
lean_mark_persistent(l_Lean_scopeManagerExt___closed__5);
l_Lean_scopeManagerExt___closed__6 = _init_l_Lean_scopeManagerExt___closed__6();
lean_mark_persistent(l_Lean_scopeManagerExt___closed__6);
res = l_Lean_regScopeManagerExtension(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_scopeManagerExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_scopeManagerExt);
lean_dec_ref(res);
l_Lean_Environment_popScopeCore___closed__1 = _init_l_Lean_Environment_popScopeCore___closed__1();
lean_mark_persistent(l_Lean_Environment_popScopeCore___closed__1);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
