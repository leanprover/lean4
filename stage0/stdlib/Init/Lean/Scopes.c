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
lean_object* l_Lean_ScopeManagerState_Inhabited;
extern lean_object* l_Lean_Name_toString___closed__1;
lean_object* l_Lean_registerEnvExtensionUnsafe___at_Lean_regScopeManagerExtension___spec__7___closed__1;
lean_object* l_Lean_Environment_isNamespace___boxed(lean_object*, lean_object*);
lean_object* l_List_tail_x21___rarg(lean_object*);
extern lean_object* l___private_Init_Lean_Environment_8__persistentEnvExtensionsRef;
uint8_t lean_is_namespace(lean_object*, lean_object*);
lean_object* l_Lean_registerEnvExtensionUnsafe___at_Lean_regScopeManagerExtension___spec__7___closed__2;
lean_object* l_Lean_Environment_registerNamespace___main(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_scopeManagerExt___elambda__1(lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Lean_regScopeManagerExtension___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_regScopeManagerExtension___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Array_iterateMAux___main___at_Lean_regScopeManagerExtension___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at_Lean_regScopeManagerExtension___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_scopeManagerExt___closed__5;
lean_object* lean_get_namespaces(lean_object*);
lean_object* l_Lean_Environment_popScopeCore(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_scopeManagerExt___closed__3;
lean_object* lean_to_valid_namespace(lean_object*, lean_object*);
lean_object* l_Lean_scopeManagerExt___elambda__2___boxed(lean_object*);
lean_object* l_Lean_regScopeManagerExtension___closed__5;
lean_object* l_Lean_regScopeManagerExtension___closed__3;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_scopeManagerExt___elambda__4(lean_object*, lean_object*);
lean_object* l_Lean_Environment_popScopeCore___closed__1;
lean_object* l_Lean_Environment_popScopeCore___lambda__1(lean_object*);
lean_object* l_Lean_mkStateFromImportedEntries___at_Lean_regScopeManagerExtension___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Environment_inSection___boxed(lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_scopeManagerExt___elambda__4___boxed(lean_object*, lean_object*);
lean_object* l_Lean_scopeManagerExt___elambda__3___boxed(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Environment_pushScopeCore___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ScopeManagerState_saveNamespace(lean_object*, lean_object*);
lean_object* l_Lean_scopeManagerExt___closed__4;
extern lean_object* l_Lean_EnvExtension_Inhabited___rarg___closed__1;
lean_object* l_EStateM_bind___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append___main(lean_object*, lean_object*);
lean_object* l_Lean_regScopeManagerExtension___closed__4;
lean_object* l_Lean_Environment_registerNamespaceAux(lean_object*, lean_object*);
lean_object* l_Lean_Environment_pushScopeCore___lambda__1(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Environment_hasOpenScopes___boxed(lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__3(lean_object*, lean_object*);
lean_object* l_Lean_scopeManagerExt___elambda__4___rarg(lean_object*);
lean_object* l_Lean_Environment_pushScopeCore___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_modifyState___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_regScopeManagerExtension___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_regScopeManagerExtension___lambda__2___boxed(lean_object*);
extern lean_object* l_IO_Error_Inhabited___closed__1;
uint8_t l_coeDecidableEq(uint8_t);
extern lean_object* l___private_Init_Lean_Environment_5__envExtensionsRef;
lean_object* l_Array_iterateMAux___main___at_Lean_regScopeManagerExtension___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_regScopeManagerExtension___lambda__2(lean_object*);
lean_object* l_Lean_registerEnvExtensionUnsafe___at_Lean_regScopeManagerExtension___spec__7___closed__3;
lean_object* l_Lean_scopeManagerExt___elambda__1___boxed(lean_object*);
lean_object* l_Lean_scopeManagerExt___closed__6;
lean_object* l_RBNode_insert___at_Lean_NameSet_insert___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerEnvExtensionUnsafe___at_Lean_regScopeManagerExtension___spec__7(lean_object*, lean_object*);
lean_object* lean_get_scope_header(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___rarg(lean_object*, lean_object*);
lean_object* l_Lean_regScopeManagerExtension(lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_regScopeManagerExtension___spec__5(lean_object*, lean_object*);
extern lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__3;
extern lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
lean_object* l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_scopeManagerExt___elambda__3(lean_object*, lean_object*);
lean_object* lean_register_namespace(lean_object*, lean_object*);
lean_object* l_Lean_Environment_getNamespaceSet(lean_object*);
extern lean_object* l_Lean_registerSimplePersistentEnvExtension___rarg___closed__1;
lean_object* l_Lean_registerSimplePersistentEnvExtension___at_Lean_regScopeManagerExtension___spec__4(lean_object*, lean_object*);
extern lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__4;
lean_object* l_Lean_mkStateFromImportedEntries___at_Lean_regScopeManagerExtension___spec__1___boxed(lean_object*, lean_object*);
lean_object* lean_io_ref_reset(lean_object*, lean_object*);
extern lean_object* l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean_object* lean_get_namespace(lean_object*);
uint8_t lean_in_section(lean_object*);
lean_object* lean_io_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_getNamespaceSet___boxed(lean_object*);
extern lean_object* l_Lean_registerEnvExtensionUnsafe___rarg___closed__3;
lean_object* lean_io_initializing(lean_object*);
extern lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_List_foldl___main___at_Lean_Environment_toValidNamespace___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___rarg(lean_object*);
lean_object* l_Lean_scopeManagerExt___elambda__2(lean_object*);
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
extern lean_object* l_Lean_regNamespacesExtension___closed__4;
lean_object* l_Lean_ScopeManagerState_Inhabited___closed__1;
lean_object* l_Lean_Environment_pushScopeCore(lean_object*, lean_object*, uint8_t);
lean_object* l_EStateM_pure___rarg(lean_object*, lean_object*);
lean_object* l_Lean_scopeManagerExt;
lean_object* l_Lean_regScopeManagerExtension___closed__1;
lean_object* l_Lean_scopeManagerExt___closed__1;
lean_object* l_Array_iterateMAux___main___at_Lean_regScopeManagerExtension___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_regScopeManagerExtension___closed__2;
lean_object* l_Lean_scopeManagerExt___closed__2;
lean_object* l_List_foldl___main___at_Lean_Environment_toValidNamespace___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_has_open_scopes(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
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
uint8_t l_Array_anyRangeMAux___main___at_Lean_regScopeManagerExtension___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_5);
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_array_fget(x_3, x_5);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_name_eq(x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_5, x_12);
lean_dec(x_5);
x_5 = x_13;
goto _start;
}
else
{
lean_dec(x_5);
return x_11;
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
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_unbox(x_5);
lean_dec(x_5);
x_8 = l_coeDecidableEq(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_1);
x_9 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_9);
return x_3;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_free_object(x_3);
x_10 = l___private_Init_Lean_Environment_5__envExtensionsRef;
x_11 = lean_io_ref_get(x_10, x_6);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_array_get_size(x_12);
lean_dec(x_12);
x_15 = l_Lean_registerEnvExtensionUnsafe___at_Lean_regScopeManagerExtension___spec__7___closed__3;
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_1);
lean_ctor_set(x_16, 2, x_15);
x_17 = lean_io_ref_get(x_10, x_13);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_io_ref_reset(x_10, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__3;
lean_inc(x_16);
x_23 = x_16;
x_24 = lean_array_push(x_18, x_23);
x_25 = lean_io_ref_set(x_10, x_24, x_21);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
lean_ctor_set(x_25, 0, x_16);
return x_25;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_16);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec(x_16);
x_30 = !lean_is_exclusive(x_25);
if (x_30 == 0)
{
return x_25;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_25, 0);
x_32 = lean_ctor_get(x_25, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_25);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_18);
lean_dec(x_16);
x_34 = !lean_is_exclusive(x_20);
if (x_34 == 0)
{
return x_20;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_20, 0);
x_36 = lean_ctor_get(x_20, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_20);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_16);
x_38 = !lean_is_exclusive(x_17);
if (x_38 == 0)
{
return x_17;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_17, 0);
x_40 = lean_ctor_get(x_17, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_17);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_11);
if (x_42 == 0)
{
return x_11;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_11, 0);
x_44 = lean_ctor_get(x_11, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_11);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
else
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_49; 
x_46 = lean_ctor_get(x_3, 0);
x_47 = lean_ctor_get(x_3, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_3);
x_48 = lean_unbox(x_46);
lean_dec(x_46);
x_49 = l_coeDecidableEq(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_1);
x_50 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_47);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = l___private_Init_Lean_Environment_5__envExtensionsRef;
x_53 = lean_io_ref_get(x_52, x_47);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_array_get_size(x_54);
lean_dec(x_54);
x_57 = l_Lean_registerEnvExtensionUnsafe___at_Lean_regScopeManagerExtension___spec__7___closed__3;
x_58 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_1);
lean_ctor_set(x_58, 2, x_57);
x_59 = lean_io_ref_get(x_52, x_55);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = lean_io_ref_reset(x_52, x_61);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec(x_62);
x_64 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__3;
lean_inc(x_58);
x_65 = x_58;
x_66 = lean_array_push(x_60, x_65);
x_67 = lean_io_ref_set(x_52, x_66, x_63);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_69 = x_67;
} else {
 lean_dec_ref(x_67);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_69;
}
lean_ctor_set(x_70, 0, x_58);
lean_ctor_set(x_70, 1, x_68);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_58);
x_71 = lean_ctor_get(x_67, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_67, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_73 = x_67;
} else {
 lean_dec_ref(x_67);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(1, 2, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_60);
lean_dec(x_58);
x_75 = lean_ctor_get(x_62, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_62, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_77 = x_62;
} else {
 lean_dec_ref(x_62);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(1, 2, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_58);
x_79 = lean_ctor_get(x_59, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_59, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_81 = x_59;
} else {
 lean_dec_ref(x_59);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(1, 2, 0);
} else {
 x_82 = x_81;
}
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_80);
return x_82;
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_1);
x_83 = lean_ctor_get(x_53, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_53, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_85 = x_53;
} else {
 lean_dec_ref(x_53);
 x_85 = lean_box(0);
}
if (lean_is_scalar(x_85)) {
 x_86 = lean_alloc_ctor(1, 2, 0);
} else {
 x_86 = x_85;
}
lean_ctor_set(x_86, 0, x_83);
lean_ctor_set(x_86, 1, x_84);
return x_86;
}
}
}
}
else
{
uint8_t x_87; 
lean_dec(x_1);
x_87 = !lean_is_exclusive(x_3);
if (x_87 == 0)
{
return x_3;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_3, 0);
x_89 = lean_ctor_get(x_3, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_3);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_array_get_size(x_6);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_anyRangeMAux___main___at_Lean_regScopeManagerExtension___spec__6(x_1, x_6, x_6, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
x_11 = l_coeDecidableEq(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_free_object(x_4);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 2);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 3);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 4);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 5);
lean_inc(x_17);
lean_dec(x_1);
x_18 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
x_19 = lean_alloc_closure((void*)(l_EStateM_bind___rarg), 3, 2);
lean_closure_set(x_19, 0, x_13);
lean_closure_set(x_19, 1, x_18);
x_20 = l_Lean_registerEnvExtensionUnsafe___at_Lean_regScopeManagerExtension___spec__7(x_19, x_7);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_12);
lean_ctor_set(x_23, 2, x_14);
lean_ctor_set(x_23, 3, x_15);
lean_ctor_set(x_23, 4, x_16);
lean_ctor_set(x_23, 5, x_17);
x_24 = lean_io_ref_get(x_3, x_22);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_io_ref_reset(x_3, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
lean_inc(x_23);
x_30 = x_23;
x_31 = lean_array_push(x_25, x_30);
x_32 = lean_io_ref_set(x_3, x_31, x_28);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_32, 0);
lean_dec(x_34);
lean_ctor_set(x_32, 0, x_23);
return x_32;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_23);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
else
{
uint8_t x_37; 
lean_dec(x_23);
x_37 = !lean_is_exclusive(x_32);
if (x_37 == 0)
{
return x_32;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_32, 0);
x_39 = lean_ctor_get(x_32, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_32);
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
lean_dec(x_25);
lean_dec(x_23);
x_41 = !lean_is_exclusive(x_27);
if (x_41 == 0)
{
return x_27;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_27, 0);
x_43 = lean_ctor_get(x_27, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_27);
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
lean_dec(x_23);
x_45 = !lean_is_exclusive(x_24);
if (x_45 == 0)
{
return x_24;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_24, 0);
x_47 = lean_ctor_get(x_24, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_24);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
x_49 = !lean_is_exclusive(x_20);
if (x_49 == 0)
{
return x_20;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_20, 0);
x_51 = lean_ctor_get(x_20, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_20);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_53 = lean_ctor_get(x_1, 0);
lean_inc(x_53);
lean_dec(x_1);
x_54 = l_Lean_Name_toString___closed__1;
x_55 = l_Lean_Name_toStringWithSep___main(x_54, x_53);
x_56 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__3;
x_57 = lean_string_append(x_56, x_55);
lean_dec(x_55);
x_58 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__4;
x_59 = lean_string_append(x_57, x_58);
x_60 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_60);
return x_4;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; uint8_t x_66; 
x_61 = lean_ctor_get(x_4, 0);
x_62 = lean_ctor_get(x_4, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_4);
x_63 = lean_array_get_size(x_61);
x_64 = lean_unsigned_to_nat(0u);
x_65 = l_Array_anyRangeMAux___main___at_Lean_regScopeManagerExtension___spec__6(x_1, x_61, x_61, x_63, x_64);
lean_dec(x_63);
lean_dec(x_61);
x_66 = l_coeDecidableEq(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_67 = lean_ctor_get(x_1, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_1, 1);
lean_inc(x_68);
x_69 = lean_ctor_get(x_1, 2);
lean_inc(x_69);
x_70 = lean_ctor_get(x_1, 3);
lean_inc(x_70);
x_71 = lean_ctor_get(x_1, 4);
lean_inc(x_71);
x_72 = lean_ctor_get(x_1, 5);
lean_inc(x_72);
lean_dec(x_1);
x_73 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
x_74 = lean_alloc_closure((void*)(l_EStateM_bind___rarg), 3, 2);
lean_closure_set(x_74, 0, x_68);
lean_closure_set(x_74, 1, x_73);
x_75 = l_Lean_registerEnvExtensionUnsafe___at_Lean_regScopeManagerExtension___spec__7(x_74, x_62);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_67);
lean_ctor_set(x_78, 2, x_69);
lean_ctor_set(x_78, 3, x_70);
lean_ctor_set(x_78, 4, x_71);
lean_ctor_set(x_78, 5, x_72);
x_79 = lean_io_ref_get(x_3, x_77);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = lean_io_ref_reset(x_3, x_81);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
lean_dec(x_82);
x_84 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
lean_inc(x_78);
x_85 = x_78;
x_86 = lean_array_push(x_80, x_85);
x_87 = lean_io_ref_set(x_3, x_86, x_83);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_89 = x_87;
} else {
 lean_dec_ref(x_87);
 x_89 = lean_box(0);
}
if (lean_is_scalar(x_89)) {
 x_90 = lean_alloc_ctor(0, 2, 0);
} else {
 x_90 = x_89;
}
lean_ctor_set(x_90, 0, x_78);
lean_ctor_set(x_90, 1, x_88);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_78);
x_91 = lean_ctor_get(x_87, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_87, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_93 = x_87;
} else {
 lean_dec_ref(x_87);
 x_93 = lean_box(0);
}
if (lean_is_scalar(x_93)) {
 x_94 = lean_alloc_ctor(1, 2, 0);
} else {
 x_94 = x_93;
}
lean_ctor_set(x_94, 0, x_91);
lean_ctor_set(x_94, 1, x_92);
return x_94;
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_80);
lean_dec(x_78);
x_95 = lean_ctor_get(x_82, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_82, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_97 = x_82;
} else {
 lean_dec_ref(x_82);
 x_97 = lean_box(0);
}
if (lean_is_scalar(x_97)) {
 x_98 = lean_alloc_ctor(1, 2, 0);
} else {
 x_98 = x_97;
}
lean_ctor_set(x_98, 0, x_95);
lean_ctor_set(x_98, 1, x_96);
return x_98;
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_78);
x_99 = lean_ctor_get(x_79, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_79, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_101 = x_79;
} else {
 lean_dec_ref(x_79);
 x_101 = lean_box(0);
}
if (lean_is_scalar(x_101)) {
 x_102 = lean_alloc_ctor(1, 2, 0);
} else {
 x_102 = x_101;
}
lean_ctor_set(x_102, 0, x_99);
lean_ctor_set(x_102, 1, x_100);
return x_102;
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_67);
x_103 = lean_ctor_get(x_75, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_75, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_105 = x_75;
} else {
 lean_dec_ref(x_75);
 x_105 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(1, 2, 0);
} else {
 x_106 = x_105;
}
lean_ctor_set(x_106, 0, x_103);
lean_ctor_set(x_106, 1, x_104);
return x_106;
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_107 = lean_ctor_get(x_1, 0);
lean_inc(x_107);
lean_dec(x_1);
x_108 = l_Lean_Name_toString___closed__1;
x_109 = l_Lean_Name_toStringWithSep___main(x_108, x_107);
x_110 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__3;
x_111 = lean_string_append(x_110, x_109);
lean_dec(x_109);
x_112 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__4;
x_113 = lean_string_append(x_111, x_112);
x_114 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_114, 0, x_113);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_62);
return x_115;
}
}
}
else
{
uint8_t x_116; 
lean_dec(x_1);
x_116 = !lean_is_exclusive(x_4);
if (x_116 == 0)
{
return x_4;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_4, 0);
x_118 = lean_ctor_get(x_4, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_4);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
return x_119;
}
}
}
}
lean_object* l_Lean_registerSimplePersistentEnvExtension___at_Lean_regScopeManagerExtension___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
x_5 = lean_box(0);
x_6 = l_Array_empty___closed__1;
lean_inc(x_4);
x_7 = lean_apply_1(x_4, x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_alloc_closure((void*)(l_EStateM_pure___rarg), 2, 1);
lean_closure_set(x_9, 0, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__1___boxed), 5, 2);
lean_closure_set(x_10, 0, x_4);
lean_closure_set(x_10, 1, x_5);
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__2), 3, 1);
lean_closure_set(x_11, 0, x_1);
x_12 = lean_alloc_closure((void*)(l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__3), 2, 1);
lean_closure_set(x_12, 0, x_1);
x_13 = l_Lean_registerSimplePersistentEnvExtension___rarg___closed__1;
x_14 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_14, 0, x_3);
lean_ctor_set(x_14, 1, x_9);
lean_ctor_set(x_14, 2, x_10);
lean_ctor_set(x_14, 3, x_11);
lean_ctor_set(x_14, 4, x_12);
lean_ctor_set(x_14, 5, x_13);
x_15 = l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_regScopeManagerExtension___spec__5(x_14, x_2);
return x_15;
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
lean_object* l_Array_anyRangeMAux___main___at_Lean_regScopeManagerExtension___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at_Lean_regScopeManagerExtension___spec__6(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
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
x_2 = l_IO_Error_Inhabited___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_scopeManagerExt___elambda__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_scopeManagerExt___elambda__4___rarg), 1, 0);
return x_3;
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
x_1 = lean_alloc_closure((void*)(l_Lean_scopeManagerExt___elambda__4___boxed), 2, 0);
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
lean_object* l_Lean_scopeManagerExt___elambda__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_scopeManagerExt___elambda__4(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
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
lean_object* l_List_foldl___main___at_Lean_Environment_toValidNamespace___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_dec(x_1);
return x_4;
}
else
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_5, 0);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_1);
x_8 = l_Lean_Name_append___main(x_6, x_1);
x_9 = l_Lean_NameSet_contains(x_3, x_8);
x_10 = l_coeDecidableEq(x_9);
if (x_10 == 0)
{
lean_dec(x_8);
x_5 = x_7;
goto _start;
}
else
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_8);
x_4 = x_12;
x_5 = x_7;
goto _start;
}
}
else
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_5, 1);
x_5 = x_14;
goto _start;
}
}
}
}
lean_object* lean_to_valid_namespace(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_7; 
x_3 = l_Lean_scopeManagerExt;
x_4 = l_Lean_SimplePersistentEnvExtension_getState___rarg(x_3, x_1);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = l_Lean_NameSet_contains(x_5, x_2);
x_7 = l_coeDecidableEq(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_box(0);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
x_10 = l_List_foldl___main___at_Lean_Environment_toValidNamespace___spec__1(x_2, x_4, x_5, x_8, x_9);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
return x_10;
}
else
{
lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_4);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_2);
return x_11;
}
}
}
lean_object* l_List_foldl___main___at_Lean_Environment_toValidNamespace___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_foldl___main___at_Lean_Environment_toValidNamespace___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_Environment_registerNamespaceAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; uint8_t x_5; 
x_3 = l_Lean_Environment_getNamespaceSet(x_1);
x_4 = l_Lean_NameSet_contains(x_3, x_2);
lean_dec(x_3);
x_5 = l_coeDecidableEq(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_scopeManagerExt;
x_7 = l_Lean_PersistentEnvExtension_addEntry___rarg(x_6, x_1, x_2);
return x_7;
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
lean_object* x_4; uint8_t x_5; 
lean_inc(x_1);
x_4 = lean_get_namespace(x_1);
x_5 = l_coeDecidableEq(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_inc(x_4);
x_6 = l_Lean_Environment_registerNamespaceAux(x_1, x_4);
x_7 = lean_box(x_3);
x_8 = lean_alloc_closure((void*)(l_Lean_Environment_pushScopeCore___lambda__1___boxed), 4, 3);
lean_closure_set(x_8, 0, x_4);
lean_closure_set(x_8, 1, x_2);
lean_closure_set(x_8, 2, x_7);
x_9 = l_Lean_scopeManagerExt;
x_10 = l_Lean_SimplePersistentEnvExtension_modifyState___rarg(x_9, x_6, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_inc(x_2);
x_11 = l_Lean_Name_append___main(x_4, x_2);
lean_dec(x_4);
lean_inc(x_11);
x_12 = l_Lean_Environment_registerNamespaceAux(x_1, x_11);
x_13 = lean_box(x_3);
x_14 = lean_alloc_closure((void*)(l_Lean_Environment_pushScopeCore___lambda__1___boxed), 4, 3);
lean_closure_set(x_14, 0, x_11);
lean_closure_set(x_14, 1, x_2);
lean_closure_set(x_14, 2, x_13);
x_15 = l_Lean_scopeManagerExt;
x_16 = l_Lean_SimplePersistentEnvExtension_modifyState___rarg(x_15, x_12, x_14);
return x_16;
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
lean_object* x_2; uint8_t x_3; uint8_t x_4; 
lean_inc(x_1);
x_2 = lean_get_namespaces(x_1);
x_3 = l_List_isEmpty___rarg(x_2);
lean_dec(x_2);
x_4 = l_coeDecidableEq(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Lean_scopeManagerExt;
x_6 = l_Lean_Environment_popScopeCore___closed__1;
x_7 = l_Lean_SimplePersistentEnvExtension_modifyState___rarg(x_5, x_1, x_6);
return x_7;
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
