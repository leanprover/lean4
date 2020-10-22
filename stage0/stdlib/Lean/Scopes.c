// Lean compiler output
// Module: Lean.Scopes
// Imports: Init Lean.Environment
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
lean_object* l_Lean_TODELETE_regScopeManagerExtension___closed__2;
lean_object* l_Lean_TODELETE_getNamespaceSet___boxed(lean_object*);
lean_object* l_List_tail_x21___rarg(lean_object*);
lean_object* l_Lean_TODELETE_ScopeManagerState_isNamespace___default;
lean_object* l_Lean_TODELETE_scopeManagerExt___elambda__4(lean_object*, lean_object*);
lean_object* l_Lean_TODELETE_registerNamespaceAux(lean_object*, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___at_Lean_TODELETE_regScopeManagerExtension___spec__4(lean_object*, lean_object*);
lean_object* l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TODELETE_inSection_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TODELETE_regScopeManagerExtension___closed__1;
lean_object* l_Lean_TODELETE_scopeManagerExt___closed__4;
lean_object* l_Lean_TODELETE_regScopeManagerExtension___closed__4;
lean_object* l_Lean_TODELETE_scopeManagerExt___closed__2;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_TODELETE_regScopeManagerExtension(lean_object*);
lean_object* l_Lean_TODELETE_scopeManagerExt___closed__1;
extern lean_object* l_Lean_initFn____x40_Lean_Environment___hyg_2495____closed__4;
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_TODELETE_ScopeManagerState_headers___default;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_TODELETE_registerNamespace_match__1(lean_object*);
lean_object* l_Lean_TODELETE_scopeManagerExt___closed__3;
lean_object* l_Lean_TODELETE_popScopeCore___closed__1;
lean_object* l_Lean_TODELETE_isNamespace___boxed(lean_object*, lean_object*);
lean_object* l_Lean_TODELETE_ScopeManagerState_allNamespaces___default;
lean_object* l_Lean_TODELETE_scopeManagerExt___closed__5;
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_TODELETE_popScopeCore___lambda__1(lean_object*);
lean_object* l_Lean_TODELETE_regScopeManagerExtension___closed__3;
lean_object* l_Lean_TODELETE_scopeManagerExt___elambda__1___boxed(lean_object*);
uint8_t l_Array_anyRangeMAux___main___at_Lean_TODELETE_regScopeManagerExtension___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TODELETE_regScopeManagerExtension___lambda__2___boxed(lean_object*);
lean_object* l_Lean_TODELETE_popScopeCore(lean_object*);
lean_object* lean_get_namespaces(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_TODELETE_getNamespace_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TODELETE_scopeManagerExt___elambda__2(lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TODELETE_ScopeManagerState_namespaces___default;
lean_object* l_Lean_TODELETE_scopeManagerExt;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_to_valid_namespace(lean_object*, lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_TODELETE_regScopeManagerExtension___spec__5(lean_object*, lean_object*);
lean_object* l_Lean_TODELETE_scopeManagerExt___elambda__3(lean_object*, lean_object*);
lean_object* l_Lean_TODELETE_toValidNamespace_match__1(lean_object*);
lean_object* l_Lean_Name_append___main(lean_object*, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__3(lean_object*, lean_object*);
lean_object* l_Lean_TODELETE_toValidNamespace_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_TODELETE_regScopeManagerExtension___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TODELETE_ScopeManagerState_Lean_Scopes___instance__1___closed__1;
lean_object* l_List_foldl___main___at_Lean_TODELETE_toValidNamespace___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_is_namespace(lean_object*, lean_object*);
lean_object* l_Lean_TODELETE_pushScopeCore___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_modifyState___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_persistentEnvExtensionsRef;
lean_object* l_Lean_TODELETE_pushScopeCore(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_TODELETE_hasOpenScopes___boxed(lean_object*);
lean_object* l_Lean_TODELETE_ScopeManagerState_saveNamespace(lean_object*, lean_object*);
lean_object* l_Lean_mkStateFromImportedEntries___at_Lean_TODELETE_regScopeManagerExtension___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_TODELETE_getScopeHeader_match__1___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_PersistentEnvExtension_addEntry___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___rarg(lean_object*, lean_object*);
extern lean_object* l_IO_Error_Init_System_IOError___instance__2___closed__1;
uint8_t lean_has_open_scopes(lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Lean_TODELETE_regScopeManagerExtension___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
lean_object* l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_in_section(lean_object*);
lean_object* lean_get_namespace(lean_object*);
lean_object* l_Lean_TODELETE_regScopeManagerExtension___lambda__2(lean_object*);
lean_object* l_Lean_TODELETE_regScopeManagerExtension___lambda__1(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_TODELETE_regScopeManagerExtension___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_registerSimplePersistentEnvExtension___rarg___closed__1;
lean_object* l_Lean_TODELETE_getScopeHeader_match__1(lean_object*);
lean_object* l_Lean_TODELETE_scopeManagerExt___elambda__4___boxed(lean_object*, lean_object*);
lean_object* l_Lean_TODELETE_scopeManagerExt___elambda__4___rarg(lean_object*);
lean_object* l_Lean_TODELETE_scopeManagerExt___elambda__2___boxed(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_TODELETE_regScopeManagerExtension___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TODELETE_inSection_match__1(lean_object*);
extern lean_object* l_Lean_EnvExtensionInterfaceUnsafe_Lean_Environment___instance__6___closed__2;
lean_object* l_Lean_mkStateFromImportedEntries___at_Lean_TODELETE_regScopeManagerExtension___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_TODELETE_getNamespace_match__1(lean_object*);
lean_object* l_Lean_TODELETE_ScopeManagerState_Lean_Scopes___instance__1;
extern lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
lean_object* l_List_foldl___main___at_Lean_TODELETE_toValidNamespace___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_namespace(lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_TODELETE_scopeManagerExt___elambda__3___boxed(lean_object*, lean_object*);
lean_object* l_Lean_TODELETE_getNamespaceSet(lean_object*);
lean_object* l_Lean_TODELETE_pushScopeCore___lambda__1(lean_object*, lean_object*, uint8_t, lean_object*);
extern lean_object* l_System_FilePath_dirName___closed__1;
uint8_t l_List_isEmpty___rarg(lean_object*);
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l_Lean_TODELETE_inSection___boxed(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_TODELETE_regScopeManagerExtension___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_pure___rarg(lean_object*, lean_object*);
lean_object* l_Lean_TODELETE_scopeManagerExt___elambda__1(lean_object*);
lean_object* l_Lean_TODELETE_registerNamespace_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TODELETE_pushScopeCore___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_get_scope_header(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_TODELETE_regScopeManagerExtension___closed__5;
static lean_object* _init_l_Lean_TODELETE_ScopeManagerState_allNamespaces___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_NameSet_empty;
return x_1;
}
}
static lean_object* _init_l_Lean_TODELETE_ScopeManagerState_namespaces___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_TODELETE_ScopeManagerState_headers___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_TODELETE_ScopeManagerState_isNamespace___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_TODELETE_ScopeManagerState_Lean_Scopes___instance__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_NameSet_empty;
x_3 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_1);
lean_ctor_set(x_3, 3, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_TODELETE_ScopeManagerState_Lean_Scopes___instance__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_TODELETE_ScopeManagerState_Lean_Scopes___instance__1___closed__1;
return x_1;
}
}
lean_object* l_Lean_TODELETE_ScopeManagerState_saveNamespace(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_box(0);
x_6 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_4, x_2, x_5);
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
x_12 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_7, x_2, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_9);
lean_ctor_set(x_13, 3, x_10);
return x_13;
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_TODELETE_regScopeManagerExtension___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_8 = l_Lean_TODELETE_ScopeManagerState_saveNamespace(x_4, x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_3, x_9);
lean_dec(x_3);
x_3 = x_10;
x_4 = x_8;
goto _start;
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_TODELETE_regScopeManagerExtension___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_9 = l_Array_iterateMAux___main___at_Lean_TODELETE_regScopeManagerExtension___spec__2(x_7, x_7, x_8, x_4);
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
lean_object* l_Lean_mkStateFromImportedEntries___at_Lean_TODELETE_regScopeManagerExtension___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Array_iterateMAux___main___at_Lean_TODELETE_regScopeManagerExtension___spec__3(x_2, x_2, x_3, x_1);
return x_4;
}
}
uint8_t l_Array_anyRangeMAux___main___at_Lean_TODELETE_regScopeManagerExtension___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_TODELETE_regScopeManagerExtension___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_persistentEnvExtensionsRef;
x_4 = lean_st_ref_get(x_3, x_2);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_array_get_size(x_6);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_anyRangeMAux___main___at_Lean_TODELETE_regScopeManagerExtension___spec__6(x_1, x_6, x_6, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_free_object(x_4);
x_11 = lean_box(0);
x_12 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__2(x_1, x_11, x_7);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = l_System_FilePath_dirName___closed__1;
x_15 = l_Lean_Name_toStringWithSep___main(x_14, x_13);
x_16 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
x_17 = lean_string_append(x_16, x_15);
lean_dec(x_15);
x_18 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
x_19 = lean_string_append(x_17, x_18);
x_20 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_20);
return x_4;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_4, 0);
x_22 = lean_ctor_get(x_4, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_4);
x_23 = lean_array_get_size(x_21);
x_24 = lean_unsigned_to_nat(0u);
x_25 = l_Array_anyRangeMAux___main___at_Lean_TODELETE_regScopeManagerExtension___spec__6(x_1, x_21, x_21, x_23, x_24);
lean_dec(x_23);
lean_dec(x_21);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_box(0);
x_27 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__2(x_1, x_26, x_22);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_28 = lean_ctor_get(x_1, 0);
lean_inc(x_28);
lean_dec(x_1);
x_29 = l_System_FilePath_dirName___closed__1;
x_30 = l_Lean_Name_toStringWithSep___main(x_29, x_28);
x_31 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
x_32 = lean_string_append(x_31, x_30);
lean_dec(x_30);
x_33 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
x_34 = lean_string_append(x_32, x_33);
x_35 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_22);
return x_36;
}
}
}
}
lean_object* l_Lean_registerSimplePersistentEnvExtension___at_Lean_TODELETE_regScopeManagerExtension___spec__4(lean_object* x_1, lean_object* x_2) {
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
x_15 = l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_TODELETE_regScopeManagerExtension___spec__5(x_14, x_2);
return x_15;
}
}
lean_object* l_Lean_TODELETE_regScopeManagerExtension___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_box(0);
x_6 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_4, x_2, x_5);
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
x_12 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_7, x_2, x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_9);
lean_ctor_set(x_13, 3, x_10);
return x_13;
}
}
}
lean_object* l_Lean_TODELETE_regScopeManagerExtension___lambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_TODELETE_ScopeManagerState_Lean_Scopes___instance__1___closed__1;
x_4 = l_Array_iterateMAux___main___at_Lean_TODELETE_regScopeManagerExtension___spec__3(x_1, x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_TODELETE_regScopeManagerExtension___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("scopes");
return x_1;
}
}
static lean_object* _init_l_Lean_TODELETE_regScopeManagerExtension___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_TODELETE_regScopeManagerExtension___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_TODELETE_regScopeManagerExtension___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_TODELETE_regScopeManagerExtension___lambda__1), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_TODELETE_regScopeManagerExtension___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_TODELETE_regScopeManagerExtension___lambda__2___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_TODELETE_regScopeManagerExtension___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_TODELETE_regScopeManagerExtension___closed__2;
x_2 = l_Lean_TODELETE_regScopeManagerExtension___closed__3;
x_3 = l_Lean_TODELETE_regScopeManagerExtension___closed__4;
x_4 = l_Lean_initFn____x40_Lean_Environment___hyg_2495____closed__4;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
lean_object* l_Lean_TODELETE_regScopeManagerExtension(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_TODELETE_regScopeManagerExtension___closed__5;
x_3 = l_Lean_registerSimplePersistentEnvExtension___at_Lean_TODELETE_regScopeManagerExtension___spec__4(x_2, x_1);
return x_3;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_TODELETE_regScopeManagerExtension___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_iterateMAux___main___at_Lean_TODELETE_regScopeManagerExtension___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_TODELETE_regScopeManagerExtension___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_iterateMAux___main___at_Lean_TODELETE_regScopeManagerExtension___spec__3(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_mkStateFromImportedEntries___at_Lean_TODELETE_regScopeManagerExtension___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkStateFromImportedEntries___at_Lean_TODELETE_regScopeManagerExtension___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_anyRangeMAux___main___at_Lean_TODELETE_regScopeManagerExtension___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at_Lean_TODELETE_regScopeManagerExtension___spec__6(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Lean_TODELETE_regScopeManagerExtension___lambda__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_TODELETE_regScopeManagerExtension___lambda__2(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_TODELETE_scopeManagerExt___elambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
lean_object* l_Lean_TODELETE_scopeManagerExt___elambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_empty___closed__1;
return x_2;
}
}
lean_object* l_Lean_TODELETE_scopeManagerExt___elambda__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
lean_object* l_Lean_TODELETE_scopeManagerExt___elambda__4___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_IO_Error_Init_System_IOError___instance__2___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_TODELETE_scopeManagerExt___elambda__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_TODELETE_scopeManagerExt___elambda__4___rarg), 1, 0);
return x_3;
}
}
static lean_object* _init_l_Lean_TODELETE_scopeManagerExt___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_TODELETE_scopeManagerExt___elambda__4___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_TODELETE_scopeManagerExt___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_TODELETE_scopeManagerExt___elambda__3___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_TODELETE_scopeManagerExt___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_TODELETE_scopeManagerExt___elambda__2___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_TODELETE_scopeManagerExt___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_TODELETE_scopeManagerExt___elambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_TODELETE_scopeManagerExt___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_Lean_EnvExtensionInterfaceUnsafe_Lean_Environment___instance__6___closed__2;
x_2 = lean_box(0);
x_3 = l_Lean_TODELETE_scopeManagerExt___closed__1;
x_4 = l_Lean_TODELETE_scopeManagerExt___closed__2;
x_5 = l_Lean_TODELETE_scopeManagerExt___closed__3;
x_6 = l_Lean_TODELETE_scopeManagerExt___closed__4;
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
lean_object* l_Lean_TODELETE_scopeManagerExt___elambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_TODELETE_scopeManagerExt___elambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_TODELETE_scopeManagerExt___elambda__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_TODELETE_scopeManagerExt___elambda__2(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_TODELETE_scopeManagerExt___elambda__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_TODELETE_scopeManagerExt___elambda__3(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_TODELETE_scopeManagerExt___elambda__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_TODELETE_scopeManagerExt___elambda__4(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* lean_get_namespaces(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_TODELETE_scopeManagerExt;
x_3 = l_Lean_SimplePersistentEnvExtension_getState___rarg(x_2, x_1);
lean_dec(x_1);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_Lean_TODELETE_getNamespaceSet(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_TODELETE_scopeManagerExt;
x_3 = l_Lean_SimplePersistentEnvExtension_getState___rarg(x_2, x_1);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_Lean_TODELETE_getNamespaceSet___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_TODELETE_getNamespaceSet(x_1);
lean_dec(x_1);
return x_2;
}
}
uint8_t lean_is_namespace(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_TODELETE_getNamespaceSet(x_1);
lean_dec(x_1);
x_4 = l_Lean_NameSet_contains(x_3, x_2);
lean_dec(x_2);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_Lean_TODELETE_isNamespace___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_is_namespace(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_TODELETE_inSection_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_1(x_3, x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_2(x_2, x_5, x_6);
return x_7;
}
}
}
lean_object* l_Lean_TODELETE_inSection_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_TODELETE_inSection_match__1___rarg), 3, 0);
return x_2;
}
}
uint8_t lean_in_section(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_TODELETE_scopeManagerExt;
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
lean_object* l_Lean_TODELETE_inSection___boxed(lean_object* x_1) {
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
lean_object* l_Lean_TODELETE_hasOpenScopes___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_has_open_scopes(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_TODELETE_getNamespace_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_1(x_3, x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_2(x_2, x_5, x_6);
return x_7;
}
}
}
lean_object* l_Lean_TODELETE_getNamespace_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_TODELETE_getNamespace_match__1___rarg), 3, 0);
return x_2;
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
lean_object* l_Lean_TODELETE_getScopeHeader_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_1(x_3, x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_2(x_2, x_5, x_6);
return x_7;
}
}
}
lean_object* l_Lean_TODELETE_getScopeHeader_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_TODELETE_getScopeHeader_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* lean_get_scope_header(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_TODELETE_scopeManagerExt;
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
lean_object* l_Lean_TODELETE_toValidNamespace_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l_Lean_TODELETE_toValidNamespace_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_TODELETE_toValidNamespace_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_List_foldl___main___at_Lean_TODELETE_toValidNamespace___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_9; 
lean_dec(x_7);
x_9 = lean_box(0);
x_3 = x_9;
x_4 = x_6;
goto _start;
}
else
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_7);
x_3 = x_11;
x_4 = x_6;
goto _start;
}
}
else
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_4, 1);
x_4 = x_13;
goto _start;
}
}
}
}
lean_object* lean_to_valid_namespace(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = l_Lean_TODELETE_scopeManagerExt;
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
x_9 = l_List_foldl___main___at_Lean_TODELETE_toValidNamespace___spec__1(x_2, x_5, x_7, x_8);
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
lean_object* l_List_foldl___main___at_Lean_TODELETE_toValidNamespace___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_foldl___main___at_Lean_TODELETE_toValidNamespace___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_TODELETE_registerNamespaceAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_TODELETE_getNamespaceSet(x_1);
x_4 = l_Lean_NameSet_contains(x_3, x_2);
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_TODELETE_scopeManagerExt;
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
lean_object* l_Lean_TODELETE_registerNamespace_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_5; lean_object* x_6; size_t x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
x_7 = lean_ctor_get_usize(x_2, 2);
x_8 = lean_box_usize(x_7);
x_9 = lean_apply_5(x_3, x_1, x_2, x_5, x_6, x_8);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_3);
x_10 = lean_apply_2(x_4, x_1, x_2);
return x_10;
}
}
}
lean_object* l_Lean_TODELETE_registerNamespace_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_TODELETE_registerNamespace_match__1___rarg), 4, 0);
return x_2;
}
}
lean_object* lean_register_namespace(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = l_Lean_TODELETE_registerNamespaceAux(x_1, x_2);
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
lean_object* l_Lean_TODELETE_pushScopeCore___lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
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
lean_object* l_Lean_TODELETE_pushScopeCore(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_1);
x_4 = lean_get_namespace(x_1);
if (x_3 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_inc(x_4);
x_5 = l_Lean_TODELETE_registerNamespaceAux(x_1, x_4);
x_6 = lean_box(x_3);
x_7 = lean_alloc_closure((void*)(l_Lean_TODELETE_pushScopeCore___lambda__1___boxed), 4, 3);
lean_closure_set(x_7, 0, x_4);
lean_closure_set(x_7, 1, x_2);
lean_closure_set(x_7, 2, x_6);
x_8 = l_Lean_TODELETE_scopeManagerExt;
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
x_11 = l_Lean_TODELETE_registerNamespaceAux(x_1, x_10);
x_12 = lean_box(x_3);
x_13 = lean_alloc_closure((void*)(l_Lean_TODELETE_pushScopeCore___lambda__1___boxed), 4, 3);
lean_closure_set(x_13, 0, x_10);
lean_closure_set(x_13, 1, x_2);
lean_closure_set(x_13, 2, x_12);
x_14 = l_Lean_TODELETE_scopeManagerExt;
x_15 = l_Lean_SimplePersistentEnvExtension_modifyState___rarg(x_14, x_11, x_13);
return x_15;
}
}
}
lean_object* l_Lean_TODELETE_pushScopeCore___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_3);
lean_dec(x_3);
x_6 = l_Lean_TODELETE_pushScopeCore___lambda__1(x_1, x_2, x_5, x_4);
return x_6;
}
}
lean_object* l_Lean_TODELETE_pushScopeCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
lean_dec(x_3);
x_5 = l_Lean_TODELETE_pushScopeCore(x_1, x_2, x_4);
return x_5;
}
}
lean_object* l_Lean_TODELETE_popScopeCore___lambda__1(lean_object* x_1) {
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
static lean_object* _init_l_Lean_TODELETE_popScopeCore___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_TODELETE_popScopeCore___lambda__1), 1, 0);
return x_1;
}
}
lean_object* l_Lean_TODELETE_popScopeCore(lean_object* x_1) {
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
x_4 = l_Lean_TODELETE_scopeManagerExt;
x_5 = l_Lean_TODELETE_popScopeCore___closed__1;
x_6 = l_Lean_SimplePersistentEnvExtension_modifyState___rarg(x_4, x_1, x_5);
return x_6;
}
else
{
return x_1;
}
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Environment(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Scopes(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Environment(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_TODELETE_ScopeManagerState_allNamespaces___default = _init_l_Lean_TODELETE_ScopeManagerState_allNamespaces___default();
lean_mark_persistent(l_Lean_TODELETE_ScopeManagerState_allNamespaces___default);
l_Lean_TODELETE_ScopeManagerState_namespaces___default = _init_l_Lean_TODELETE_ScopeManagerState_namespaces___default();
lean_mark_persistent(l_Lean_TODELETE_ScopeManagerState_namespaces___default);
l_Lean_TODELETE_ScopeManagerState_headers___default = _init_l_Lean_TODELETE_ScopeManagerState_headers___default();
lean_mark_persistent(l_Lean_TODELETE_ScopeManagerState_headers___default);
l_Lean_TODELETE_ScopeManagerState_isNamespace___default = _init_l_Lean_TODELETE_ScopeManagerState_isNamespace___default();
lean_mark_persistent(l_Lean_TODELETE_ScopeManagerState_isNamespace___default);
l_Lean_TODELETE_ScopeManagerState_Lean_Scopes___instance__1___closed__1 = _init_l_Lean_TODELETE_ScopeManagerState_Lean_Scopes___instance__1___closed__1();
lean_mark_persistent(l_Lean_TODELETE_ScopeManagerState_Lean_Scopes___instance__1___closed__1);
l_Lean_TODELETE_ScopeManagerState_Lean_Scopes___instance__1 = _init_l_Lean_TODELETE_ScopeManagerState_Lean_Scopes___instance__1();
lean_mark_persistent(l_Lean_TODELETE_ScopeManagerState_Lean_Scopes___instance__1);
l_Lean_TODELETE_regScopeManagerExtension___closed__1 = _init_l_Lean_TODELETE_regScopeManagerExtension___closed__1();
lean_mark_persistent(l_Lean_TODELETE_regScopeManagerExtension___closed__1);
l_Lean_TODELETE_regScopeManagerExtension___closed__2 = _init_l_Lean_TODELETE_regScopeManagerExtension___closed__2();
lean_mark_persistent(l_Lean_TODELETE_regScopeManagerExtension___closed__2);
l_Lean_TODELETE_regScopeManagerExtension___closed__3 = _init_l_Lean_TODELETE_regScopeManagerExtension___closed__3();
lean_mark_persistent(l_Lean_TODELETE_regScopeManagerExtension___closed__3);
l_Lean_TODELETE_regScopeManagerExtension___closed__4 = _init_l_Lean_TODELETE_regScopeManagerExtension___closed__4();
lean_mark_persistent(l_Lean_TODELETE_regScopeManagerExtension___closed__4);
l_Lean_TODELETE_regScopeManagerExtension___closed__5 = _init_l_Lean_TODELETE_regScopeManagerExtension___closed__5();
lean_mark_persistent(l_Lean_TODELETE_regScopeManagerExtension___closed__5);
l_Lean_TODELETE_scopeManagerExt___closed__1 = _init_l_Lean_TODELETE_scopeManagerExt___closed__1();
lean_mark_persistent(l_Lean_TODELETE_scopeManagerExt___closed__1);
l_Lean_TODELETE_scopeManagerExt___closed__2 = _init_l_Lean_TODELETE_scopeManagerExt___closed__2();
lean_mark_persistent(l_Lean_TODELETE_scopeManagerExt___closed__2);
l_Lean_TODELETE_scopeManagerExt___closed__3 = _init_l_Lean_TODELETE_scopeManagerExt___closed__3();
lean_mark_persistent(l_Lean_TODELETE_scopeManagerExt___closed__3);
l_Lean_TODELETE_scopeManagerExt___closed__4 = _init_l_Lean_TODELETE_scopeManagerExt___closed__4();
lean_mark_persistent(l_Lean_TODELETE_scopeManagerExt___closed__4);
l_Lean_TODELETE_scopeManagerExt___closed__5 = _init_l_Lean_TODELETE_scopeManagerExt___closed__5();
lean_mark_persistent(l_Lean_TODELETE_scopeManagerExt___closed__5);
res = l_Lean_TODELETE_regScopeManagerExtension(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_TODELETE_scopeManagerExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_TODELETE_scopeManagerExt);
lean_dec_ref(res);
l_Lean_TODELETE_popScopeCore___closed__1 = _init_l_Lean_TODELETE_popScopeCore___closed__1();
lean_mark_persistent(l_Lean_TODELETE_popScopeCore___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
