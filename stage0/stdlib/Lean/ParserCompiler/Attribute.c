// Lean compiler output
// Module: Lean.ParserCompiler.Attribute
// Imports: Init Lean.Attributes Lean.Compiler.InitAttr Lean.ToExpr Lean.Meta.Message
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
extern lean_object* l_Lean_Name_toString___closed__1;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_io_ref_get(lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at_Lean_ParserCompiler_registerCombinatorAttribute___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkStateFromImportedEntries___at_Lean_ParserCompiler_registerCombinatorAttribute___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute___lambda__1___closed__1;
lean_object* l_Lean_Core_getEnv___rarg(lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Array_anyRangeMAux___main___at_Lean_ParserCompiler_registerCombinatorAttribute___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Core_throwError___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_AttributeImpl_inhabited___closed__2;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Core_setEnv(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Environment_8__persistentEnvExtensionsRef;
extern lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg___closed__1;
lean_object* l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__2(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_CombinatorAttribute_Inhabited;
lean_object* lean_io_ref_take(lean_object*, lean_object*);
extern lean_object* l_Lean_EnvExtension_Inhabited___rarg___closed__1;
lean_object* l_Lean_ParserCompiler_CombinatorAttribute_getDeclFor___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_bind___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_CombinatorAttribute_setDeclFor(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg___closed__2;
lean_object* l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__3(lean_object*, lean_object*);
lean_object* l_Lean_mkStateFromImportedEntries___at_Lean_ParserCompiler_registerCombinatorAttribute___spec__1(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_ParserCompiler_registerCombinatorAttribute___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_CombinatorAttribute_getDeclFor(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute___closed__1;
lean_object* l_Lean_attrParamSyntaxToIdentifier(lean_object*);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*, lean_object*);
lean_object* l_Lean_Core_getConstInfo(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg___closed__3;
lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute___lambda__1___closed__5;
lean_object* l_Lean_PersistentEnvExtension_addEntry___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_CombinatorAttribute_Inhabited___closed__2;
lean_object* l_Lean_SimplePersistentEnvExtension_getState___rarg(lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute___lambda__1___closed__3;
extern lean_object* l___private_Lean_Environment_5__envExtensionsRef;
lean_object* l_Lean_registerEnvExtensionUnsafe___at_Lean_ParserCompiler_registerCombinatorAttribute___spec__7___closed__2;
extern lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__3;
extern lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
lean_object* l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerEnvExtensionUnsafe___at_Lean_ParserCompiler_registerCombinatorAttribute___spec__7___closed__1;
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_ParserCompiler_registerCombinatorAttribute___spec__5(lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_CombinatorAttribute_Inhabited___closed__1;
extern lean_object* l_Lean_registerSimplePersistentEnvExtension___rarg___closed__1;
extern lean_object* l_Lean_registerParametricAttribute___rarg___closed__3;
extern lean_object* l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean_object* l_Lean_ParserCompiler_CombinatorAttribute_Inhabited___closed__3;
lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute___lambda__1___closed__6;
lean_object* l_Lean_registerEnvExtensionUnsafe___at_Lean_ParserCompiler_registerCombinatorAttribute___spec__7(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_ParserCompiler_registerCombinatorAttribute___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_initializing(lean_object*);
extern lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
lean_object* l_Std_RBNode_find___main___at_Lean_isIOUnitInitFn___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___at_Lean_ParserCompiler_registerCombinatorAttribute___spec__4(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_ParserCompiler_registerCombinatorAttribute___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
extern lean_object* l_Lean_regNamespacesExtension___closed__4;
lean_object* l_EStateM_pure___rarg(lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute___lambda__1___closed__2;
lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg___closed__4;
lean_object* l_Array_iterateMAux___main___at_Lean_ParserCompiler_registerCombinatorAttribute___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute___lambda__1___closed__4;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_ParserCompiler_registerCombinatorAttribute___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Std_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_4, x_8, x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_3, x_11);
lean_dec(x_3);
x_3 = x_12;
x_4 = x_10;
goto _start;
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_ParserCompiler_registerCombinatorAttribute___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_9 = l_Array_iterateMAux___main___at_Lean_ParserCompiler_registerCombinatorAttribute___spec__2(x_7, x_7, x_8, x_4);
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
lean_object* l_Lean_mkStateFromImportedEntries___at_Lean_ParserCompiler_registerCombinatorAttribute___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Array_iterateMAux___main___at_Lean_ParserCompiler_registerCombinatorAttribute___spec__3(x_2, x_2, x_3, x_1);
return x_4;
}
}
uint8_t l_Array_anyRangeMAux___main___at_Lean_ParserCompiler_registerCombinatorAttribute___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* _init_l_Lean_registerEnvExtensionUnsafe___at_Lean_ParserCompiler_registerCombinatorAttribute___spec__7___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_registerEnvExtensionUnsafe___at_Lean_ParserCompiler_registerCombinatorAttribute___spec__7___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_registerEnvExtensionUnsafe___at_Lean_ParserCompiler_registerCombinatorAttribute___spec__7___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_registerEnvExtensionUnsafe___at_Lean_ParserCompiler_registerCombinatorAttribute___spec__7(lean_object* x_1, lean_object* x_2) {
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
x_8 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
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
x_10 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_dec(x_3);
x_13 = l___private_Lean_Environment_5__envExtensionsRef;
x_14 = lean_io_ref_get(x_13, x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_array_get_size(x_15);
lean_dec(x_15);
x_18 = l_Lean_registerEnvExtensionUnsafe___at_Lean_ParserCompiler_registerCombinatorAttribute___spec__7___closed__2;
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_1);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_io_ref_take(x_13, x_16);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_19);
x_23 = x_19;
x_24 = lean_array_push(x_21, x_23);
x_25 = lean_io_ref_set(x_13, x_24, x_22);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
lean_ctor_set(x_25, 0, x_19);
return x_25;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_19);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_3);
if (x_30 == 0)
{
return x_3;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_3, 0);
x_32 = lean_ctor_get(x_3, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_3);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_ParserCompiler_registerCombinatorAttribute___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l___private_Lean_Environment_8__persistentEnvExtensionsRef;
x_4 = lean_io_ref_get(x_3, x_2);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_array_get_size(x_6);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_anyRangeMAux___main___at_Lean_ParserCompiler_registerCombinatorAttribute___spec__6(x_1, x_6, x_6, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_free_object(x_4);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 3);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 4);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 5);
lean_inc(x_16);
lean_dec(x_1);
x_17 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
x_18 = lean_alloc_closure((void*)(l_EStateM_bind___rarg), 3, 2);
lean_closure_set(x_18, 0, x_12);
lean_closure_set(x_18, 1, x_17);
x_19 = l_Lean_registerEnvExtensionUnsafe___at_Lean_ParserCompiler_registerCombinatorAttribute___spec__7(x_18, x_7);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_11);
lean_ctor_set(x_22, 2, x_13);
lean_ctor_set(x_22, 3, x_14);
lean_ctor_set(x_22, 4, x_15);
lean_ctor_set(x_22, 5, x_16);
x_23 = lean_io_ref_take(x_3, x_21);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_22);
x_26 = x_22;
x_27 = lean_array_push(x_24, x_26);
x_28 = lean_io_ref_set(x_3, x_27, x_25);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
lean_ctor_set(x_28, 0, x_22);
return x_28;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_22);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
x_33 = !lean_is_exclusive(x_19);
if (x_33 == 0)
{
return x_19;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_19, 0);
x_35 = lean_ctor_get(x_19, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_19);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_37 = lean_ctor_get(x_1, 0);
lean_inc(x_37);
lean_dec(x_1);
x_38 = l_Lean_Name_toString___closed__1;
x_39 = l_Lean_Name_toStringWithSep___main(x_38, x_37);
x_40 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
x_41 = lean_string_append(x_40, x_39);
lean_dec(x_39);
x_42 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__3;
x_43 = lean_string_append(x_41, x_42);
x_44 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_44);
return x_4;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_45 = lean_ctor_get(x_4, 0);
x_46 = lean_ctor_get(x_4, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_4);
x_47 = lean_array_get_size(x_45);
x_48 = lean_unsigned_to_nat(0u);
x_49 = l_Array_anyRangeMAux___main___at_Lean_ParserCompiler_registerCombinatorAttribute___spec__6(x_1, x_45, x_45, x_47, x_48);
lean_dec(x_47);
lean_dec(x_45);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_50 = lean_ctor_get(x_1, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_1, 1);
lean_inc(x_51);
x_52 = lean_ctor_get(x_1, 2);
lean_inc(x_52);
x_53 = lean_ctor_get(x_1, 3);
lean_inc(x_53);
x_54 = lean_ctor_get(x_1, 4);
lean_inc(x_54);
x_55 = lean_ctor_get(x_1, 5);
lean_inc(x_55);
lean_dec(x_1);
x_56 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
x_57 = lean_alloc_closure((void*)(l_EStateM_bind___rarg), 3, 2);
lean_closure_set(x_57, 0, x_51);
lean_closure_set(x_57, 1, x_56);
x_58 = l_Lean_registerEnvExtensionUnsafe___at_Lean_ParserCompiler_registerCombinatorAttribute___spec__7(x_57, x_46);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_50);
lean_ctor_set(x_61, 2, x_52);
lean_ctor_set(x_61, 3, x_53);
lean_ctor_set(x_61, 4, x_54);
lean_ctor_set(x_61, 5, x_55);
x_62 = lean_io_ref_take(x_3, x_60);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
lean_inc(x_61);
x_65 = x_61;
x_66 = lean_array_push(x_63, x_65);
x_67 = lean_io_ref_set(x_3, x_66, x_64);
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
lean_ctor_set(x_70, 0, x_61);
lean_ctor_set(x_70, 1, x_68);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_50);
x_71 = lean_ctor_get(x_58, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_58, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_73 = x_58;
} else {
 lean_dec_ref(x_58);
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
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_75 = lean_ctor_get(x_1, 0);
lean_inc(x_75);
lean_dec(x_1);
x_76 = l_Lean_Name_toString___closed__1;
x_77 = l_Lean_Name_toStringWithSep___main(x_76, x_75);
x_78 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
x_79 = lean_string_append(x_78, x_77);
lean_dec(x_77);
x_80 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__3;
x_81 = lean_string_append(x_79, x_80);
x_82 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_82, 0, x_81);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_46);
return x_83;
}
}
}
}
lean_object* l_Lean_registerSimplePersistentEnvExtension___at_Lean_ParserCompiler_registerCombinatorAttribute___spec__4(lean_object* x_1, lean_object* x_2) {
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
x_15 = l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_ParserCompiler_registerCombinatorAttribute___spec__5(x_14, x_2);
return x_15;
}
}
lean_object* _init_l_Lean_ParserCompiler_registerCombinatorAttribute___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid [");
return x_1;
}
}
lean_object* _init_l_Lean_ParserCompiler_registerCombinatorAttribute___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_ParserCompiler_registerCombinatorAttribute___lambda__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_ParserCompiler_registerCombinatorAttribute___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_ParserCompiler_registerCombinatorAttribute___lambda__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_ParserCompiler_registerCombinatorAttribute___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("] argument, expected identifier");
return x_1;
}
}
lean_object* _init_l_Lean_ParserCompiler_registerCombinatorAttribute___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_ParserCompiler_registerCombinatorAttribute___lambda__1___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_ParserCompiler_registerCombinatorAttribute___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_ParserCompiler_registerCombinatorAttribute___lambda__1___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = l_Lean_Core_getEnv___rarg(x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_attrParamSyntaxToIdentifier(x_4);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_13, 0, x_1);
x_14 = l_Lean_ParserCompiler_registerCombinatorAttribute___lambda__1___closed__3;
x_15 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = l_Lean_ParserCompiler_registerCombinatorAttribute___lambda__1___closed__6;
x_17 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_Core_throwError___rarg(x_17, x_6, x_7, x_11);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_1);
x_19 = lean_ctor_get(x_12, 0);
lean_inc(x_19);
lean_dec(x_12);
lean_inc(x_19);
x_20 = l_Lean_Core_getConstInfo(x_19, x_6, x_7, x_11);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_3);
x_23 = l_Lean_PersistentEnvExtension_addEntry___rarg(x_2, x_10, x_22);
x_24 = l_Lean_Core_setEnv(x_23, x_6, x_7, x_21);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_2);
x_25 = !lean_is_exclusive(x_20);
if (x_25 == 0)
{
return x_20;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_20, 0);
x_27 = lean_ctor_get(x_20, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_20);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
}
lean_object* _init_l_Lean_ParserCompiler_registerCombinatorAttribute___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_closure((void*)(l_Lean_mkStateFromImportedEntries___at_Lean_ParserCompiler_registerCombinatorAttribute___spec__1___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = l_Lean_registerParametricAttribute___rarg___closed__3;
x_5 = l_Lean_ParserCompiler_registerCombinatorAttribute___closed__1;
x_6 = l_Lean_regNamespacesExtension___closed__4;
lean_inc(x_1);
x_7 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_4);
lean_ctor_set(x_7, 2, x_5);
lean_ctor_set(x_7, 3, x_6);
x_8 = l_Lean_registerSimplePersistentEnvExtension___at_Lean_ParserCompiler_registerCombinatorAttribute___spec__4(x_7, x_3);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_9);
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l_Lean_ParserCompiler_registerCombinatorAttribute___lambda__1___boxed), 8, 2);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_9);
x_12 = 0;
x_13 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_2);
lean_ctor_set(x_13, 2, x_11);
lean_ctor_set_uint8(x_13, sizeof(void*)*3, x_12);
lean_inc(x_13);
x_14 = l_Lean_registerBuiltinAttribute(x_13, x_10);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set(x_17, 1, x_9);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_9);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
uint8_t x_21; 
lean_dec(x_13);
lean_dec(x_9);
x_21 = !lean_is_exclusive(x_14);
if (x_21 == 0)
{
return x_14;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_14, 0);
x_23 = lean_ctor_get(x_14, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_14);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
uint8_t x_25; 
lean_dec(x_2);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_8);
if (x_25 == 0)
{
return x_8;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_8, 0);
x_27 = lean_ctor_get(x_8, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_8);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_ParserCompiler_registerCombinatorAttribute___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_iterateMAux___main___at_Lean_ParserCompiler_registerCombinatorAttribute___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_ParserCompiler_registerCombinatorAttribute___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_iterateMAux___main___at_Lean_ParserCompiler_registerCombinatorAttribute___spec__3(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_mkStateFromImportedEntries___at_Lean_ParserCompiler_registerCombinatorAttribute___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkStateFromImportedEntries___at_Lean_ParserCompiler_registerCombinatorAttribute___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_anyRangeMAux___main___at_Lean_ParserCompiler_registerCombinatorAttribute___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at_Lean_ParserCompiler_registerCombinatorAttribute___spec__6(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Lean_ParserCompiler_registerCombinatorAttribute___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_5);
lean_dec(x_5);
x_10 = l_Lean_ParserCompiler_registerCombinatorAttribute___lambda__1(x_1, x_2, x_3, x_4, x_9, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
return x_10;
}
}
lean_object* _init_l_Lean_ParserCompiler_CombinatorAttribute_Inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_EnvExtension_Inhabited___rarg___closed__1;
x_3 = l_Lean_registerEnvExtensionUnsafe___at_Lean_ParserCompiler_registerCombinatorAttribute___spec__7___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_ParserCompiler_CombinatorAttribute_Inhabited___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_Lean_ParserCompiler_CombinatorAttribute_Inhabited___closed__1;
x_2 = lean_box(0);
x_3 = l_Lean_PersistentEnvExtension_inhabited___rarg___closed__1;
x_4 = l_Lean_PersistentEnvExtension_inhabited___rarg___closed__2;
x_5 = l_Lean_PersistentEnvExtension_inhabited___rarg___closed__3;
x_6 = l_Lean_PersistentEnvExtension_inhabited___rarg___closed__4;
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
lean_object* _init_l_Lean_ParserCompiler_CombinatorAttribute_Inhabited___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_AttributeImpl_inhabited___closed__2;
x_2 = l_Lean_ParserCompiler_CombinatorAttribute_Inhabited___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_ParserCompiler_CombinatorAttribute_Inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_ParserCompiler_CombinatorAttribute_Inhabited___closed__3;
return x_1;
}
}
lean_object* l_Lean_ParserCompiler_CombinatorAttribute_getDeclFor(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_Lean_SimplePersistentEnvExtension_getState___rarg(x_4, x_2);
x_6 = l_Std_RBNode_find___main___at_Lean_isIOUnitInitFn___spec__2(x_5, x_3);
lean_dec(x_5);
return x_6;
}
}
lean_object* l_Lean_ParserCompiler_CombinatorAttribute_getDeclFor___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_ParserCompiler_CombinatorAttribute_getDeclFor(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_ParserCompiler_CombinatorAttribute_setDeclFor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_4);
x_7 = l_Lean_PersistentEnvExtension_addEntry___rarg(x_5, x_2, x_6);
return x_7;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Attributes(lean_object*);
lean_object* initialize_Lean_Compiler_InitAttr(lean_object*);
lean_object* initialize_Lean_ToExpr(lean_object*);
lean_object* initialize_Lean_Meta_Message(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_ParserCompiler_Attribute(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Attributes(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_InitAttr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ToExpr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Message(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_registerEnvExtensionUnsafe___at_Lean_ParserCompiler_registerCombinatorAttribute___spec__7___closed__1 = _init_l_Lean_registerEnvExtensionUnsafe___at_Lean_ParserCompiler_registerCombinatorAttribute___spec__7___closed__1();
lean_mark_persistent(l_Lean_registerEnvExtensionUnsafe___at_Lean_ParserCompiler_registerCombinatorAttribute___spec__7___closed__1);
l_Lean_registerEnvExtensionUnsafe___at_Lean_ParserCompiler_registerCombinatorAttribute___spec__7___closed__2 = _init_l_Lean_registerEnvExtensionUnsafe___at_Lean_ParserCompiler_registerCombinatorAttribute___spec__7___closed__2();
lean_mark_persistent(l_Lean_registerEnvExtensionUnsafe___at_Lean_ParserCompiler_registerCombinatorAttribute___spec__7___closed__2);
l_Lean_ParserCompiler_registerCombinatorAttribute___lambda__1___closed__1 = _init_l_Lean_ParserCompiler_registerCombinatorAttribute___lambda__1___closed__1();
lean_mark_persistent(l_Lean_ParserCompiler_registerCombinatorAttribute___lambda__1___closed__1);
l_Lean_ParserCompiler_registerCombinatorAttribute___lambda__1___closed__2 = _init_l_Lean_ParserCompiler_registerCombinatorAttribute___lambda__1___closed__2();
lean_mark_persistent(l_Lean_ParserCompiler_registerCombinatorAttribute___lambda__1___closed__2);
l_Lean_ParserCompiler_registerCombinatorAttribute___lambda__1___closed__3 = _init_l_Lean_ParserCompiler_registerCombinatorAttribute___lambda__1___closed__3();
lean_mark_persistent(l_Lean_ParserCompiler_registerCombinatorAttribute___lambda__1___closed__3);
l_Lean_ParserCompiler_registerCombinatorAttribute___lambda__1___closed__4 = _init_l_Lean_ParserCompiler_registerCombinatorAttribute___lambda__1___closed__4();
lean_mark_persistent(l_Lean_ParserCompiler_registerCombinatorAttribute___lambda__1___closed__4);
l_Lean_ParserCompiler_registerCombinatorAttribute___lambda__1___closed__5 = _init_l_Lean_ParserCompiler_registerCombinatorAttribute___lambda__1___closed__5();
lean_mark_persistent(l_Lean_ParserCompiler_registerCombinatorAttribute___lambda__1___closed__5);
l_Lean_ParserCompiler_registerCombinatorAttribute___lambda__1___closed__6 = _init_l_Lean_ParserCompiler_registerCombinatorAttribute___lambda__1___closed__6();
lean_mark_persistent(l_Lean_ParserCompiler_registerCombinatorAttribute___lambda__1___closed__6);
l_Lean_ParserCompiler_registerCombinatorAttribute___closed__1 = _init_l_Lean_ParserCompiler_registerCombinatorAttribute___closed__1();
lean_mark_persistent(l_Lean_ParserCompiler_registerCombinatorAttribute___closed__1);
l_Lean_ParserCompiler_CombinatorAttribute_Inhabited___closed__1 = _init_l_Lean_ParserCompiler_CombinatorAttribute_Inhabited___closed__1();
lean_mark_persistent(l_Lean_ParserCompiler_CombinatorAttribute_Inhabited___closed__1);
l_Lean_ParserCompiler_CombinatorAttribute_Inhabited___closed__2 = _init_l_Lean_ParserCompiler_CombinatorAttribute_Inhabited___closed__2();
lean_mark_persistent(l_Lean_ParserCompiler_CombinatorAttribute_Inhabited___closed__2);
l_Lean_ParserCompiler_CombinatorAttribute_Inhabited___closed__3 = _init_l_Lean_ParserCompiler_CombinatorAttribute_Inhabited___closed__3();
lean_mark_persistent(l_Lean_ParserCompiler_CombinatorAttribute_Inhabited___closed__3);
l_Lean_ParserCompiler_CombinatorAttribute_Inhabited = _init_l_Lean_ParserCompiler_CombinatorAttribute_Inhabited();
lean_mark_persistent(l_Lean_ParserCompiler_CombinatorAttribute_Inhabited);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
