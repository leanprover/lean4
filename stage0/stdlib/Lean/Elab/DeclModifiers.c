// Lean compiler output
// Module: Lean.Elab.DeclModifiers
// Imports: Init Lean.Elab.Command
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
lean_object* l_Lean_Elab_Command_checkNotAlreadyDeclared___closed__9;
lean_object* l_Lean_Elab_Command_checkNotAlreadyDeclared(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Core_getConstInfo___closed__5;
extern lean_object* l_Lean_Name_toString___closed__1;
lean_object* l_Lean_Elab_Command_checkNotAlreadyDeclared___closed__4;
lean_object* l_Lean_Elab_Command_checkNotAlreadyDeclared___closed__8;
extern lean_object* l_Lean_List_format___rarg___closed__4;
lean_object* l_Lean_Elab_Command_Modifiers_hasFormat___closed__6;
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
lean_object* l_Lean_Format_pretty(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_List_map___main___at_Lean_Elab_Command_Modifiers_hasFormat___spec__2(lean_object*);
lean_object* l_Lean_fmt___at_Lean_Elab_Command_Modifiers_hasFormat___spec__1(lean_object*);
lean_object* l_Lean_Elab_Command_Modifiers_hasFormat___closed__8;
lean_object* l_Lean_Core_getEnv___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_applyAttributes___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_Elab_Command_Modifiers_hasFormat___boxed(lean_object*);
lean_object* l_Lean_Elab_Command_elabModifiers___closed__6;
lean_object* l_Lean_Elab_Command_Modifiers_hasFormat___closed__2;
lean_object* l_List_append___rarg(lean_object*, lean_object*);
lean_object* lean_private_to_user_name(lean_object*);
extern lean_object* l_Lean_MessageData_arrayExpr_toMessageData___main___closed__1;
lean_object* l_Lean_Elab_Command_Modifiers_hasFormat___closed__1;
lean_object* l_Lean_Elab_Command_Modifiers_hasFormat___closed__3;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_MessageData_formatAux___main(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_Modifiers_hasFormat___closed__15;
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_applyAttributes(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lean_Elab_Command_Modifiers_hasFormat(lean_object*);
lean_object* l_Lean_Elab_Command_throwErrorAt___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_applyVisibility(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_Modifiers_hasFormat___closed__11;
lean_object* l_Lean_Elab_Command_Attribute_inhabited___closed__1;
lean_object* l_Lean_Elab_Command_checkNotAlreadyDeclared___closed__2;
lean_object* l_Lean_Elab_Command_mkDeclName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_AttributeApplicationTime_beq(uint8_t, uint8_t);
lean_object* l_Lean_Elab_Command_Modifiers_hasFormat___closed__4;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_Visibility_hasToString(uint8_t);
lean_object* l_Lean_Elab_Command_Modifiers_hasToString;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_forM___at_Lean_Core_runCore___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Format_joinSep___main___at___private_Lean_Data_Trie_6__toStringAux___main___spec__1(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_Modifiers_hasToString___lambda__1___boxed(lean_object*);
lean_object* l_Lean_Name_append___main(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__5;
lean_object* l_Lean_KernelException_toMessageData(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabModifiers___closed__4;
lean_object* l_Lean_Elab_Command_Modifiers_hasFormat___closed__9;
extern lean_object* l_Lean_Format_join___closed__1;
extern lean_object* l_Std_PersistentArray_Stats_toString___closed__4;
lean_object* l_Lean_Core_getTraceState___at_Lean_Core_runCore___spec__1___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Command_1__ioErrorToMessage(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlStepMAux___main___at_Lean_Elab_Command_elabAttrs___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_Modifiers_hasFormat___closed__13;
lean_object* l_Lean_Elab_Command_Visibility_hasToString___boxed(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_Modifiers_hasToString___lambda__1(lean_object*);
lean_object* l_Function_comp___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_throwError___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkNotAlreadyDeclared___closed__1;
extern lean_object* l_Lean_protectedExt;
extern lean_object* l_Lean_Parser_Command_docComment___elambda__1___closed__2;
extern lean_object* l_Lean_Options_empty;
extern lean_object* l_Lean_Parser_Command_attributes___elambda__1___closed__5;
lean_object* l_Lean_Elab_Command_elabModifiers___closed__1;
lean_object* l_Lean_Elab_Command_elabAttr___closed__4;
lean_object* l_IO_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkNotAlreadyDeclared___closed__7;
lean_object* l_Lean_Elab_Command_elabModifiers___closed__2;
lean_object* l_Lean_Elab_Command_elabAttr___closed__6;
lean_object* l_Lean_Elab_Command_elabAttrs(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabAttr___closed__1;
lean_object* l_Lean_Elab_Command_elabAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_Modifiers_hasToString___closed__2;
lean_object* l_Lean_Elab_Command_Modifiers_hasFormat___closed__12;
lean_object* l_Lean_Elab_Command_Attribute_hasFormat___closed__1;
lean_object* l_Lean_PersistentEnvExtension_addEntry___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getCurrNamespace___rarg(lean_object*, lean_object*);
extern lean_object* l_Lean_Format_sbracket___closed__3;
lean_object* l_Lean_Elab_Command_Modifiers_hasFormat___closed__10;
uint8_t l_Lean_Syntax_isMissing(lean_object*);
lean_object* l_Lean_Syntax_isIdOrAtom_x3f(lean_object*);
lean_object* l_Lean_Elab_Command_elabModifiers___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_HasRepr___closed__1;
extern lean_object* l_Lean_Environment_addAttribute___closed__2;
lean_object* l_Lean_Elab_Command_Visibility_hasToString___closed__1;
extern lean_object* l_Lean_Parser_Command_noncomputable___elambda__1___closed__1;
uint8_t l_Lean_isAttribute(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getNumArgs(lean_object*);
lean_object* l_Array_foldlStepMAux___main___at_Lean_Elab_Command_elabAttrs___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabAttr___closed__3;
lean_object* l_Lean_Elab_Command_elabAttr___closed__2;
lean_object* l_Lean_Elab_Command_Modifiers_hasToString___closed__1;
extern lean_object* l_Lean_Parser_Command_private___elambda__1___closed__1;
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
extern lean_object* l_Lean_Core_MonadIO;
lean_object* l_Lean_Elab_Command_Attribute_inhabited;
lean_object* l_Lean_Elab_Command_Modifiers_addAttribute(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getEnv___rarg(lean_object*, lean_object*);
lean_object* lean_format_group(lean_object*);
lean_object* l_Lean_Elab_Command_Attribute_hasFormat___closed__2;
lean_object* l_Lean_Elab_Command_elabAttr___closed__5;
lean_object* l_Array_forMAux___main___at_Lean_Elab_Command_applyAttributes___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
extern lean_object* l_Lean_TraceState_Inhabited___closed__1;
lean_object* l_Lean_Elab_Command_Modifiers_hasFormat___closed__7;
lean_object* l_Array_forMAux___main___at_Lean_Elab_Command_applyAttributes___spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabAttrs___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_Modifiers_hasFormat___closed__16;
lean_object* l_Lean_Elab_Command_elabModifiers(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_Modifiers_hasFormat___closed__14;
lean_object* l_Lean_Elab_Command_Modifiers_hasFormat___closed__5;
lean_object* l_Lean_Elab_Command_checkNotAlreadyDeclared___closed__6;
lean_object* l_Array_toList___rarg(lean_object*);
lean_object* l_Lean_Elab_Command_applyVisibility___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_unsafe___elambda__1___closed__1;
lean_object* l_Lean_Elab_Command_setEnv(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
uint8_t l_Lean_Elab_Command_Modifiers_isProtected(lean_object*);
lean_object* l_Lean_Elab_Command_Modifiers_isPrivate___boxed(lean_object*);
uint8_t l_Lean_Elab_Command_Modifiers_isPrivate(lean_object*);
lean_object* l_Lean_Elab_Command_Attribute_hasFormat(lean_object*);
extern lean_object* l_Lean_Parser_Command_private___elambda__1___closed__2;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_partial___elambda__1___closed__1;
lean_object* l_Lean_Elab_Command_checkNotAlreadyDeclared___closed__3;
lean_object* l_Lean_Syntax_formatStxAux___main(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabModifiers___closed__7;
lean_object* l_IO_Prim_mkRef___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabAttr(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkNotAlreadyDeclared___closed__5;
lean_object* l_Lean_getAttributeImpl(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabModifiers___closed__5;
extern lean_object* l_addParenHeuristic___closed__1;
extern lean_object* l_Lean_Parser_Command_docComment___elambda__1___closed__7;
lean_object* l_Lean_Elab_Command_mkDeclName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_Modifiers_isProtected___boxed(lean_object*);
extern lean_object* l_Lean_NameGenerator_Inhabited___closed__3;
lean_object* l_Lean_Elab_Command_elabModifiers___closed__3;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Elab_replaceRef(lean_object*, lean_object*);
extern lean_object* l_Lean_mkProtectedExtension___closed__1;
lean_object* _init_l_Lean_Elab_Command_Attribute_hasFormat___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Command_attributes___elambda__1___closed__5;
x_2 = lean_string_length(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_Attribute_hasFormat___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Command_attributes___elambda__1___closed__5;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_Attribute_hasFormat(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Name_toString___closed__1;
x_4 = l_Lean_Name_toStringWithSep___main(x_3, x_2);
x_5 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = l_Lean_Syntax_isMissing(x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_8 = lean_box(0);
x_9 = 0;
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Lean_Syntax_formatStxAux___main(x_8, x_9, x_10, x_6);
x_12 = l_Lean_Options_empty;
x_13 = l_Lean_Format_pretty(x_11, x_12);
x_14 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_15, 0, x_5);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set_uint8(x_15, sizeof(void*)*2, x_9);
x_16 = l_Lean_Elab_Command_Attribute_hasFormat___closed__2;
x_17 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*2, x_9);
x_18 = l_Lean_Format_sbracket___closed__3;
x_19 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set_uint8(x_19, sizeof(void*)*2, x_9);
x_20 = l_Lean_Elab_Command_Attribute_hasFormat___closed__1;
x_21 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_format_group(x_21);
return x_22;
}
else
{
uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_6);
x_23 = 0;
x_24 = l_Lean_Format_join___closed__1;
x_25 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_25, 0, x_5);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set_uint8(x_25, sizeof(void*)*2, x_23);
x_26 = l_Lean_Elab_Command_Attribute_hasFormat___closed__2;
x_27 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
lean_ctor_set_uint8(x_27, sizeof(void*)*2, x_23);
x_28 = l_Lean_Format_sbracket___closed__3;
x_29 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set_uint8(x_29, sizeof(void*)*2, x_23);
x_30 = l_Lean_Elab_Command_Attribute_hasFormat___closed__1;
x_31 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
x_32 = lean_format_group(x_31);
return x_32;
}
}
}
lean_object* _init_l_Lean_Elab_Command_Attribute_inhabited___closed__1() {
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
lean_object* _init_l_Lean_Elab_Command_Attribute_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_Attribute_inhabited___closed__1;
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_Visibility_hasToString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("regular");
return x_1;
}
}
lean_object* l_Lean_Elab_Command_Visibility_hasToString(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Command_Visibility_hasToString___closed__1;
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = l_Lean_mkProtectedExtension___closed__1;
return x_3;
}
default: 
{
lean_object* x_4; 
x_4 = l_Lean_Parser_Command_private___elambda__1___closed__1;
return x_4;
}
}
}
}
lean_object* l_Lean_Elab_Command_Visibility_hasToString___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Elab_Command_Visibility_hasToString(x_2);
return x_3;
}
}
uint8_t l_Lean_Elab_Command_Modifiers_isPrivate(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
x_3 = lean_box(x_2);
if (lean_obj_tag(x_3) == 2)
{
uint8_t x_4; 
x_4 = 1;
return x_4;
}
else
{
uint8_t x_5; 
lean_dec(x_3);
x_5 = 0;
return x_5;
}
}
}
lean_object* l_Lean_Elab_Command_Modifiers_isPrivate___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Command_Modifiers_isPrivate(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t l_Lean_Elab_Command_Modifiers_isProtected(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
x_3 = lean_box(x_2);
if (lean_obj_tag(x_3) == 1)
{
uint8_t x_4; 
x_4 = 1;
return x_4;
}
else
{
uint8_t x_5; 
lean_dec(x_3);
x_5 = 0;
return x_5;
}
}
}
lean_object* l_Lean_Elab_Command_Modifiers_isProtected___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Command_Modifiers_isProtected(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_Modifiers_addAttribute(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_array_push(x_4, x_2);
lean_ctor_set(x_1, 1, x_5);
return x_1;
}
else
{
lean_object* x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 1);
x_9 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 2);
x_10 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 3);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_inc(x_6);
lean_dec(x_1);
x_12 = lean_array_push(x_11, x_2);
x_13 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_12);
lean_ctor_set_uint8(x_13, sizeof(void*)*2, x_7);
lean_ctor_set_uint8(x_13, sizeof(void*)*2 + 1, x_8);
lean_ctor_set_uint8(x_13, sizeof(void*)*2 + 2, x_9);
lean_ctor_set_uint8(x_13, sizeof(void*)*2 + 3, x_10);
return x_13;
}
}
}
lean_object* l_Lean_fmt___at_Lean_Elab_Command_Modifiers_hasFormat___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_Name_toString___closed__1;
x_4 = l_Lean_Name_toStringWithSep___main(x_3, x_2);
x_5 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = l_Lean_Syntax_isMissing(x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_8 = lean_box(0);
x_9 = 0;
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Lean_Syntax_formatStxAux___main(x_8, x_9, x_10, x_6);
x_12 = l_Lean_Options_empty;
x_13 = l_Lean_Format_pretty(x_11, x_12);
x_14 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_15, 0, x_5);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set_uint8(x_15, sizeof(void*)*2, x_9);
x_16 = l_Lean_Elab_Command_Attribute_hasFormat___closed__2;
x_17 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*2, x_9);
x_18 = l_Lean_Format_sbracket___closed__3;
x_19 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set_uint8(x_19, sizeof(void*)*2, x_9);
x_20 = l_Lean_Elab_Command_Attribute_hasFormat___closed__1;
x_21 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_format_group(x_21);
return x_22;
}
else
{
uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_6);
x_23 = 0;
x_24 = l_Lean_Format_join___closed__1;
x_25 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_25, 0, x_5);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set_uint8(x_25, sizeof(void*)*2, x_23);
x_26 = l_Lean_Elab_Command_Attribute_hasFormat___closed__2;
x_27 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
lean_ctor_set_uint8(x_27, sizeof(void*)*2, x_23);
x_28 = l_Lean_Format_sbracket___closed__3;
x_29 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set_uint8(x_29, sizeof(void*)*2, x_23);
x_30 = l_Lean_Elab_Command_Attribute_hasFormat___closed__1;
x_31 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
x_32 = lean_format_group(x_31);
return x_32;
}
}
}
lean_object* l_List_map___main___at_Lean_Elab_Command_Modifiers_hasFormat___spec__2(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_Lean_fmt___at_Lean_Elab_Command_Modifiers_hasFormat___spec__1(x_4);
x_7 = l_List_map___main___at_Lean_Elab_Command_Modifiers_hasFormat___spec__2(x_5);
lean_ctor_set(x_1, 1, x_7);
lean_ctor_set(x_1, 0, x_6);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_10 = l_Lean_fmt___at_Lean_Elab_Command_Modifiers_hasFormat___spec__1(x_8);
x_11 = l_List_map___main___at_Lean_Elab_Command_Modifiers_hasFormat___spec__2(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
lean_object* _init_l_Lean_Elab_Command_Modifiers_hasFormat___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_addParenHeuristic___closed__1;
x_2 = lean_string_length(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_Modifiers_hasFormat___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_addParenHeuristic___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_Modifiers_hasFormat___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_PersistentArray_Stats_toString___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_Modifiers_hasFormat___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Command_unsafe___elambda__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_Modifiers_hasFormat___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_Modifiers_hasFormat___closed__4;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_Modifiers_hasFormat___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Command_partial___elambda__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_Modifiers_hasFormat___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_Modifiers_hasFormat___closed__6;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_Modifiers_hasFormat___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Command_noncomputable___elambda__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_Modifiers_hasFormat___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_Modifiers_hasFormat___closed__8;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_Modifiers_hasFormat___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_mkProtectedExtension___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_Modifiers_hasFormat___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_Modifiers_hasFormat___closed__10;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_Modifiers_hasFormat___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Command_private___elambda__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_Modifiers_hasFormat___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_Modifiers_hasFormat___closed__12;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_Modifiers_hasFormat___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Command_docComment___elambda__1___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_Modifiers_hasFormat___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("-/");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_Modifiers_hasFormat___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_Modifiers_hasFormat___closed__15;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_Modifiers_hasFormat(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; uint8_t x_4; uint8_t x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
x_4 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 1);
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 2);
x_6 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 3);
x_7 = lean_ctor_get(x_1, 1);
x_8 = l_Array_toList___rarg(x_7);
x_9 = l_List_map___main___at_Lean_Elab_Command_Modifiers_hasFormat___spec__2(x_8);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_78; 
x_78 = lean_box(0);
x_10 = x_78;
goto block_77;
}
else
{
lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_79 = lean_ctor_get(x_2, 0);
lean_inc(x_79);
x_80 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_80, 0, x_79);
x_81 = 0;
x_82 = l_Lean_Elab_Command_Modifiers_hasFormat___closed__14;
x_83 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_80);
lean_ctor_set_uint8(x_83, sizeof(void*)*2, x_81);
x_84 = l_Lean_Elab_Command_Modifiers_hasFormat___closed__16;
x_85 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
lean_ctor_set_uint8(x_85, sizeof(void*)*2, x_81);
x_86 = lean_box(0);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
x_10 = x_87;
goto block_77;
}
block_77:
{
lean_object* x_11; 
switch (x_3) {
case 0:
{
lean_object* x_74; 
x_74 = lean_box(0);
x_11 = x_74;
goto block_73;
}
case 1:
{
lean_object* x_75; 
x_75 = l_Lean_Elab_Command_Modifiers_hasFormat___closed__11;
x_11 = x_75;
goto block_73;
}
default: 
{
lean_object* x_76; 
x_76 = l_Lean_Elab_Command_Modifiers_hasFormat___closed__13;
x_11 = x_76;
goto block_73;
}
}
block_73:
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_List_append___rarg(x_10, x_11);
if (x_4 == 0)
{
lean_object* x_71; 
x_71 = lean_box(0);
x_13 = x_71;
goto block_70;
}
else
{
lean_object* x_72; 
x_72 = l_Lean_Elab_Command_Modifiers_hasFormat___closed__9;
x_13 = x_72;
goto block_70;
}
block_70:
{
lean_object* x_14; 
x_14 = l_List_append___rarg(x_12, x_13);
if (x_5 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_box(0);
x_16 = l_List_append___rarg(x_14, x_15);
if (x_6 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_17 = l_List_append___rarg(x_16, x_15);
x_18 = l_List_append___rarg(x_17, x_9);
x_19 = l_Lean_List_format___rarg___closed__4;
x_20 = l_Lean_Format_joinSep___main___at___private_Lean_Data_Trie_6__toStringAux___main___spec__1(x_18, x_19);
lean_dec(x_18);
x_21 = 0;
x_22 = l_Lean_Elab_Command_Modifiers_hasFormat___closed__2;
x_23 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_20);
lean_ctor_set_uint8(x_23, sizeof(void*)*2, x_21);
x_24 = l_Lean_Elab_Command_Modifiers_hasFormat___closed__3;
x_25 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set_uint8(x_25, sizeof(void*)*2, x_21);
x_26 = l_Lean_Elab_Command_Modifiers_hasFormat___closed__1;
x_27 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_28 = lean_format_group(x_27);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_29 = l_Lean_Elab_Command_Modifiers_hasFormat___closed__5;
x_30 = l_List_append___rarg(x_16, x_29);
x_31 = l_List_append___rarg(x_30, x_9);
x_32 = l_Lean_List_format___rarg___closed__4;
x_33 = l_Lean_Format_joinSep___main___at___private_Lean_Data_Trie_6__toStringAux___main___spec__1(x_31, x_32);
lean_dec(x_31);
x_34 = 0;
x_35 = l_Lean_Elab_Command_Modifiers_hasFormat___closed__2;
x_36 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
lean_ctor_set_uint8(x_36, sizeof(void*)*2, x_34);
x_37 = l_Lean_Elab_Command_Modifiers_hasFormat___closed__3;
x_38 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set_uint8(x_38, sizeof(void*)*2, x_34);
x_39 = l_Lean_Elab_Command_Modifiers_hasFormat___closed__1;
x_40 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
x_41 = lean_format_group(x_40);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_box(0);
x_43 = l_Lean_Elab_Command_Modifiers_hasFormat___closed__7;
x_44 = l_List_append___rarg(x_14, x_43);
if (x_6 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_45 = l_List_append___rarg(x_44, x_42);
x_46 = l_List_append___rarg(x_45, x_9);
x_47 = l_Lean_List_format___rarg___closed__4;
x_48 = l_Lean_Format_joinSep___main___at___private_Lean_Data_Trie_6__toStringAux___main___spec__1(x_46, x_47);
lean_dec(x_46);
x_49 = 0;
x_50 = l_Lean_Elab_Command_Modifiers_hasFormat___closed__2;
x_51 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_48);
lean_ctor_set_uint8(x_51, sizeof(void*)*2, x_49);
x_52 = l_Lean_Elab_Command_Modifiers_hasFormat___closed__3;
x_53 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set_uint8(x_53, sizeof(void*)*2, x_49);
x_54 = l_Lean_Elab_Command_Modifiers_hasFormat___closed__1;
x_55 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
x_56 = lean_format_group(x_55);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_57 = l_Lean_Elab_Command_Modifiers_hasFormat___closed__5;
x_58 = l_List_append___rarg(x_44, x_57);
x_59 = l_List_append___rarg(x_58, x_9);
x_60 = l_Lean_List_format___rarg___closed__4;
x_61 = l_Lean_Format_joinSep___main___at___private_Lean_Data_Trie_6__toStringAux___main___spec__1(x_59, x_60);
lean_dec(x_59);
x_62 = 0;
x_63 = l_Lean_Elab_Command_Modifiers_hasFormat___closed__2;
x_64 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_61);
lean_ctor_set_uint8(x_64, sizeof(void*)*2, x_62);
x_65 = l_Lean_Elab_Command_Modifiers_hasFormat___closed__3;
x_66 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
lean_ctor_set_uint8(x_66, sizeof(void*)*2, x_62);
x_67 = l_Lean_Elab_Command_Modifiers_hasFormat___closed__1;
x_68 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_66);
x_69 = lean_format_group(x_68);
return x_69;
}
}
}
}
}
}
}
lean_object* l_Lean_Elab_Command_Modifiers_hasFormat___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Command_Modifiers_hasFormat(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_Modifiers_hasToString___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; uint8_t x_4; uint8_t x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
x_4 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 1);
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 2);
x_6 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 3);
x_7 = lean_ctor_get(x_1, 1);
x_8 = l_Array_toList___rarg(x_7);
x_9 = l_List_map___main___at_Lean_Elab_Command_Modifiers_hasFormat___spec__2(x_8);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_78; 
x_78 = lean_box(0);
x_10 = x_78;
goto block_77;
}
else
{
lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_79 = lean_ctor_get(x_2, 0);
lean_inc(x_79);
x_80 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_80, 0, x_79);
x_81 = 0;
x_82 = l_Lean_Elab_Command_Modifiers_hasFormat___closed__14;
x_83 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_80);
lean_ctor_set_uint8(x_83, sizeof(void*)*2, x_81);
x_84 = l_Lean_Elab_Command_Modifiers_hasFormat___closed__16;
x_85 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
lean_ctor_set_uint8(x_85, sizeof(void*)*2, x_81);
x_86 = lean_box(0);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
x_10 = x_87;
goto block_77;
}
block_77:
{
lean_object* x_11; 
switch (x_3) {
case 0:
{
lean_object* x_74; 
x_74 = lean_box(0);
x_11 = x_74;
goto block_73;
}
case 1:
{
lean_object* x_75; 
x_75 = l_Lean_Elab_Command_Modifiers_hasFormat___closed__11;
x_11 = x_75;
goto block_73;
}
default: 
{
lean_object* x_76; 
x_76 = l_Lean_Elab_Command_Modifiers_hasFormat___closed__13;
x_11 = x_76;
goto block_73;
}
}
block_73:
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_List_append___rarg(x_10, x_11);
if (x_4 == 0)
{
lean_object* x_71; 
x_71 = lean_box(0);
x_13 = x_71;
goto block_70;
}
else
{
lean_object* x_72; 
x_72 = l_Lean_Elab_Command_Modifiers_hasFormat___closed__9;
x_13 = x_72;
goto block_70;
}
block_70:
{
lean_object* x_14; 
x_14 = l_List_append___rarg(x_12, x_13);
if (x_5 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_box(0);
x_16 = l_List_append___rarg(x_14, x_15);
if (x_6 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_17 = l_List_append___rarg(x_16, x_15);
x_18 = l_List_append___rarg(x_17, x_9);
x_19 = l_Lean_List_format___rarg___closed__4;
x_20 = l_Lean_Format_joinSep___main___at___private_Lean_Data_Trie_6__toStringAux___main___spec__1(x_18, x_19);
lean_dec(x_18);
x_21 = 0;
x_22 = l_Lean_Elab_Command_Modifiers_hasFormat___closed__2;
x_23 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_20);
lean_ctor_set_uint8(x_23, sizeof(void*)*2, x_21);
x_24 = l_Lean_Elab_Command_Modifiers_hasFormat___closed__3;
x_25 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set_uint8(x_25, sizeof(void*)*2, x_21);
x_26 = l_Lean_Elab_Command_Modifiers_hasFormat___closed__1;
x_27 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_28 = lean_format_group(x_27);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_29 = l_Lean_Elab_Command_Modifiers_hasFormat___closed__5;
x_30 = l_List_append___rarg(x_16, x_29);
x_31 = l_List_append___rarg(x_30, x_9);
x_32 = l_Lean_List_format___rarg___closed__4;
x_33 = l_Lean_Format_joinSep___main___at___private_Lean_Data_Trie_6__toStringAux___main___spec__1(x_31, x_32);
lean_dec(x_31);
x_34 = 0;
x_35 = l_Lean_Elab_Command_Modifiers_hasFormat___closed__2;
x_36 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
lean_ctor_set_uint8(x_36, sizeof(void*)*2, x_34);
x_37 = l_Lean_Elab_Command_Modifiers_hasFormat___closed__3;
x_38 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set_uint8(x_38, sizeof(void*)*2, x_34);
x_39 = l_Lean_Elab_Command_Modifiers_hasFormat___closed__1;
x_40 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
x_41 = lean_format_group(x_40);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_box(0);
x_43 = l_Lean_Elab_Command_Modifiers_hasFormat___closed__7;
x_44 = l_List_append___rarg(x_14, x_43);
if (x_6 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_45 = l_List_append___rarg(x_44, x_42);
x_46 = l_List_append___rarg(x_45, x_9);
x_47 = l_Lean_List_format___rarg___closed__4;
x_48 = l_Lean_Format_joinSep___main___at___private_Lean_Data_Trie_6__toStringAux___main___spec__1(x_46, x_47);
lean_dec(x_46);
x_49 = 0;
x_50 = l_Lean_Elab_Command_Modifiers_hasFormat___closed__2;
x_51 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_48);
lean_ctor_set_uint8(x_51, sizeof(void*)*2, x_49);
x_52 = l_Lean_Elab_Command_Modifiers_hasFormat___closed__3;
x_53 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set_uint8(x_53, sizeof(void*)*2, x_49);
x_54 = l_Lean_Elab_Command_Modifiers_hasFormat___closed__1;
x_55 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
x_56 = lean_format_group(x_55);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_57 = l_Lean_Elab_Command_Modifiers_hasFormat___closed__5;
x_58 = l_List_append___rarg(x_44, x_57);
x_59 = l_List_append___rarg(x_58, x_9);
x_60 = l_Lean_List_format___rarg___closed__4;
x_61 = l_Lean_Format_joinSep___main___at___private_Lean_Data_Trie_6__toStringAux___main___spec__1(x_59, x_60);
lean_dec(x_59);
x_62 = 0;
x_63 = l_Lean_Elab_Command_Modifiers_hasFormat___closed__2;
x_64 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_61);
lean_ctor_set_uint8(x_64, sizeof(void*)*2, x_62);
x_65 = l_Lean_Elab_Command_Modifiers_hasFormat___closed__3;
x_66 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
lean_ctor_set_uint8(x_66, sizeof(void*)*2, x_62);
x_67 = l_Lean_Elab_Command_Modifiers_hasFormat___closed__1;
x_68 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_66);
x_69 = lean_format_group(x_68);
return x_69;
}
}
}
}
}
}
}
lean_object* _init_l_Lean_Elab_Command_Modifiers_hasToString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_Modifiers_hasToString___lambda__1___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_Modifiers_hasToString___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_HasRepr___closed__1;
x_2 = l_Lean_Elab_Command_Modifiers_hasToString___closed__1;
x_3 = lean_alloc_closure((void*)(l_Function_comp___rarg), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_Modifiers_hasToString() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_Modifiers_hasToString___closed__2;
return x_1;
}
}
lean_object* l_Lean_Elab_Command_Modifiers_hasToString___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Command_Modifiers_hasToString___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_elabAttr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unknown attribute [");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_elabAttr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabAttr___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_elabAttr___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabAttr___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_elabAttr___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("identifier expected");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_elabAttr___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabAttr___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_elabAttr___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabAttr___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_elabAttr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_unsigned_to_nat(0u);
x_59 = l_Lean_Syntax_getArg(x_1, x_58);
x_60 = l_Lean_Syntax_isIdOrAtom_x3f(x_59);
if (lean_obj_tag(x_60) == 0)
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_2);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_62 = lean_ctor_get(x_2, 6);
x_63 = l_Lean_Elab_replaceRef(x_59, x_62);
lean_dec(x_62);
lean_dec(x_59);
lean_ctor_set(x_2, 6, x_63);
x_64 = l_Lean_Elab_Command_elabAttr___closed__6;
x_65 = l_Lean_Elab_Command_throwError___rarg(x_64, x_2, x_3, x_4);
x_66 = !lean_is_exclusive(x_65);
if (x_66 == 0)
{
return x_65;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_65, 0);
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_65);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_70 = lean_ctor_get(x_2, 0);
x_71 = lean_ctor_get(x_2, 1);
x_72 = lean_ctor_get(x_2, 2);
x_73 = lean_ctor_get(x_2, 3);
x_74 = lean_ctor_get(x_2, 4);
x_75 = lean_ctor_get(x_2, 5);
x_76 = lean_ctor_get(x_2, 6);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_2);
x_77 = l_Lean_Elab_replaceRef(x_59, x_76);
lean_dec(x_76);
lean_dec(x_59);
x_78 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_78, 0, x_70);
lean_ctor_set(x_78, 1, x_71);
lean_ctor_set(x_78, 2, x_72);
lean_ctor_set(x_78, 3, x_73);
lean_ctor_set(x_78, 4, x_74);
lean_ctor_set(x_78, 5, x_75);
lean_ctor_set(x_78, 6, x_77);
x_79 = l_Lean_Elab_Command_elabAttr___closed__6;
x_80 = l_Lean_Elab_Command_throwError___rarg(x_79, x_78, x_3, x_4);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_83 = x_80;
} else {
 lean_dec_ref(x_80);
 x_83 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(1, 2, 0);
} else {
 x_84 = x_83;
}
lean_ctor_set(x_84, 0, x_81);
lean_ctor_set(x_84, 1, x_82);
return x_84;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_59);
x_85 = lean_ctor_get(x_60, 0);
lean_inc(x_85);
lean_dec(x_60);
x_86 = lean_box(0);
x_87 = lean_name_mk_string(x_86, x_85);
x_5 = x_87;
x_6 = x_4;
goto block_57;
}
block_57:
{
lean_object* x_7; 
lean_inc(x_3);
x_7 = l_Lean_Elab_Command_getEnv___rarg(x_3, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = l_Lean_isAttribute(x_9, x_5);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_free_object(x_7);
x_12 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_12, 0, x_5);
x_13 = l_Lean_Elab_Command_elabAttr___closed__3;
x_14 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = l_Lean_MessageData_arrayExpr_toMessageData___main___closed__1;
x_16 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_Elab_Command_throwError___rarg(x_16, x_2, x_3, x_10);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
return x_17;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_17);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
lean_dec(x_3);
lean_dec(x_2);
x_22 = lean_unsigned_to_nat(1u);
x_23 = l_Lean_Syntax_getArg(x_1, x_22);
x_24 = l_Lean_Syntax_getNumArgs(x_23);
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_nat_dec_eq(x_24, x_25);
lean_dec(x_24);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_5);
lean_ctor_set(x_27, 1, x_23);
lean_ctor_set(x_7, 0, x_27);
return x_7;
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_23);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_5);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_7, 0, x_29);
return x_7;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_ctor_get(x_7, 0);
x_31 = lean_ctor_get(x_7, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_7);
x_32 = l_Lean_isAttribute(x_30, x_5);
lean_dec(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_33 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_33, 0, x_5);
x_34 = l_Lean_Elab_Command_elabAttr___closed__3;
x_35 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
x_36 = l_Lean_MessageData_arrayExpr_toMessageData___main___closed__1;
x_37 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Lean_Elab_Command_throwError___rarg(x_37, x_2, x_3, x_31);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_41 = x_38;
} else {
 lean_dec_ref(x_38);
 x_41 = lean_box(0);
}
if (lean_is_scalar(x_41)) {
 x_42 = lean_alloc_ctor(1, 2, 0);
} else {
 x_42 = x_41;
}
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
lean_dec(x_3);
lean_dec(x_2);
x_43 = lean_unsigned_to_nat(1u);
x_44 = l_Lean_Syntax_getArg(x_1, x_43);
x_45 = l_Lean_Syntax_getNumArgs(x_44);
x_46 = lean_unsigned_to_nat(0u);
x_47 = lean_nat_dec_eq(x_45, x_46);
lean_dec(x_45);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_5);
lean_ctor_set(x_48, 1, x_44);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_31);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_44);
x_50 = lean_box(0);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_5);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_31);
return x_52;
}
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_53 = !lean_is_exclusive(x_7);
if (x_53 == 0)
{
return x_7;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_7, 0);
x_55 = lean_ctor_get(x_7, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_7);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
}
lean_object* l_Lean_Elab_Command_elabAttr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabAttr(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_foldlStepMAux___main___at_Lean_Elab_Command_elabAttrs___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_2);
x_9 = lean_nat_dec_lt(x_3, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_array_fget(x_2, x_3);
lean_inc(x_6);
lean_inc(x_5);
x_12 = l_Lean_Elab_Command_elabAttr(x_11, x_5, x_6, x_7);
lean_dec(x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_array_push(x_4, x_13);
x_16 = lean_nat_add(x_3, x_1);
lean_dec(x_3);
x_3 = x_16;
x_4 = x_15;
x_7 = x_14;
goto _start;
}
else
{
uint8_t x_18; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_18 = !lean_is_exclusive(x_12);
if (x_18 == 0)
{
return x_12;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_12, 0);
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_12);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
}
lean_object* l_Lean_Elab_Command_elabAttrs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = l_Lean_Syntax_getArgs(x_6);
lean_dec(x_6);
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_empty___closed__1;
x_11 = l_Array_foldlStepMAux___main___at_Lean_Elab_Command_elabAttrs___spec__1(x_8, x_7, x_9, x_10, x_2, x_3, x_4);
lean_dec(x_7);
return x_11;
}
}
lean_object* l_Array_foldlStepMAux___main___at_Lean_Elab_Command_elabAttrs___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_foldlStepMAux___main___at_Lean_Elab_Command_elabAttrs___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_Elab_Command_elabAttrs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabAttrs(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* _init_l_Lean_Elab_Command_elabModifiers___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Command_docComment___elambda__1___closed__2;
x_2 = l_Lean_mkProtectedExtension___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_elabModifiers___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected visibility modifier");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_elabModifiers___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabModifiers___closed__2;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_elabModifiers___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabModifiers___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_elabModifiers___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected doc string ");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_elabModifiers___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabModifiers___closed__5;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_elabModifiers___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabModifiers___closed__6;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_elabModifiers(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_85; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = lean_unsigned_to_nat(1u);
x_8 = l_Lean_Syntax_getArg(x_1, x_7);
x_9 = lean_unsigned_to_nat(2u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
x_11 = lean_unsigned_to_nat(3u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = lean_unsigned_to_nat(4u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
x_15 = lean_unsigned_to_nat(5u);
x_16 = l_Lean_Syntax_getArg(x_1, x_15);
x_85 = l_Lean_Syntax_getOptional_x3f(x_6);
lean_dec(x_6);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; 
x_86 = lean_box(0);
x_17 = x_86;
x_18 = x_4;
goto block_84;
}
else
{
uint8_t x_87; 
x_87 = !lean_is_exclusive(x_85);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_106; 
x_88 = lean_ctor_get(x_85, 0);
x_106 = l_Lean_Syntax_getArg(x_88, x_7);
if (lean_obj_tag(x_106) == 2)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_88);
x_107 = lean_ctor_get(x_106, 1);
lean_inc(x_107);
lean_dec(x_106);
x_108 = lean_string_utf8_byte_size(x_107);
x_109 = lean_nat_sub(x_108, x_9);
lean_dec(x_108);
x_110 = lean_string_utf8_extract(x_107, x_5, x_109);
lean_dec(x_109);
lean_dec(x_107);
lean_ctor_set(x_85, 0, x_110);
x_17 = x_85;
x_18 = x_4;
goto block_84;
}
else
{
lean_object* x_111; 
lean_dec(x_106);
lean_free_object(x_85);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
x_111 = lean_box(0);
x_89 = x_111;
goto block_105;
}
block_105:
{
lean_object* x_90; lean_object* x_91; uint8_t x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
lean_dec(x_89);
x_90 = l_Lean_Syntax_getArg(x_88, x_7);
x_91 = lean_box(0);
x_92 = 0;
x_93 = l_Lean_Syntax_formatStxAux___main(x_91, x_92, x_5, x_90);
x_94 = l_Lean_Options_empty;
x_95 = l_Lean_Format_pretty(x_93, x_94);
x_96 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_96, 0, x_95);
x_97 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_97, 0, x_96);
x_98 = l_Lean_Elab_Command_elabModifiers___closed__7;
x_99 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_97);
x_100 = l_Lean_Elab_Command_throwErrorAt___rarg(x_88, x_99, x_2, x_3, x_4);
lean_dec(x_88);
x_101 = !lean_is_exclusive(x_100);
if (x_101 == 0)
{
return x_100;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_100, 0);
x_103 = lean_ctor_get(x_100, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_100);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_130; 
x_112 = lean_ctor_get(x_85, 0);
lean_inc(x_112);
lean_dec(x_85);
x_130 = l_Lean_Syntax_getArg(x_112, x_7);
if (lean_obj_tag(x_130) == 2)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_112);
x_131 = lean_ctor_get(x_130, 1);
lean_inc(x_131);
lean_dec(x_130);
x_132 = lean_string_utf8_byte_size(x_131);
x_133 = lean_nat_sub(x_132, x_9);
lean_dec(x_132);
x_134 = lean_string_utf8_extract(x_131, x_5, x_133);
lean_dec(x_133);
lean_dec(x_131);
x_135 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_135, 0, x_134);
x_17 = x_135;
x_18 = x_4;
goto block_84;
}
else
{
lean_object* x_136; 
lean_dec(x_130);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
x_136 = lean_box(0);
x_113 = x_136;
goto block_129;
}
block_129:
{
lean_object* x_114; lean_object* x_115; uint8_t x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec(x_113);
x_114 = l_Lean_Syntax_getArg(x_112, x_7);
x_115 = lean_box(0);
x_116 = 0;
x_117 = l_Lean_Syntax_formatStxAux___main(x_115, x_116, x_5, x_114);
x_118 = l_Lean_Options_empty;
x_119 = l_Lean_Format_pretty(x_117, x_118);
x_120 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_120, 0, x_119);
x_121 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_121, 0, x_120);
x_122 = l_Lean_Elab_Command_elabModifiers___closed__7;
x_123 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_121);
x_124 = l_Lean_Elab_Command_throwErrorAt___rarg(x_112, x_123, x_2, x_3, x_4);
lean_dec(x_112);
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_127 = x_124;
} else {
 lean_dec_ref(x_124);
 x_127 = lean_box(0);
}
if (lean_is_scalar(x_127)) {
 x_128 = lean_alloc_ctor(1, 2, 0);
} else {
 x_128 = x_127;
}
lean_ctor_set(x_128, 0, x_125);
lean_ctor_set(x_128, 1, x_126);
return x_128;
}
}
}
block_84:
{
uint8_t x_19; lean_object* x_20; lean_object* x_68; 
x_68 = l_Lean_Syntax_getOptional_x3f(x_10);
lean_dec(x_10);
if (lean_obj_tag(x_68) == 0)
{
uint8_t x_69; 
x_69 = 0;
x_19 = x_69;
x_20 = x_18;
goto block_67;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_70 = lean_ctor_get(x_68, 0);
lean_inc(x_70);
lean_dec(x_68);
lean_inc(x_70);
x_71 = l_Lean_Syntax_getKind(x_70);
x_72 = l_Lean_Parser_Command_private___elambda__1___closed__2;
x_73 = lean_name_eq(x_71, x_72);
if (x_73 == 0)
{
lean_object* x_74; uint8_t x_75; 
x_74 = l_Lean_Elab_Command_elabModifiers___closed__1;
x_75 = lean_name_eq(x_71, x_74);
lean_dec(x_71);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; uint8_t x_78; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_8);
x_76 = l_Lean_Elab_Command_elabModifiers___closed__4;
x_77 = l_Lean_Elab_Command_throwErrorAt___rarg(x_70, x_76, x_2, x_3, x_18);
lean_dec(x_70);
x_78 = !lean_is_exclusive(x_77);
if (x_78 == 0)
{
return x_77;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_77, 0);
x_80 = lean_ctor_get(x_77, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_77);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
else
{
uint8_t x_82; 
lean_dec(x_70);
x_82 = 1;
x_19 = x_82;
x_20 = x_18;
goto block_67;
}
}
else
{
uint8_t x_83; 
lean_dec(x_71);
lean_dec(x_70);
x_83 = 2;
x_19 = x_83;
x_20 = x_18;
goto block_67;
}
}
block_67:
{
lean_object* x_21; lean_object* x_22; lean_object* x_57; 
x_57 = l_Lean_Syntax_getOptional_x3f(x_8);
lean_dec(x_8);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; 
lean_dec(x_3);
lean_dec(x_2);
x_58 = l_Array_empty___closed__1;
x_21 = x_58;
x_22 = x_20;
goto block_56;
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_57, 0);
lean_inc(x_59);
lean_dec(x_57);
x_60 = l_Lean_Elab_Command_elabAttrs(x_59, x_2, x_3, x_20);
lean_dec(x_59);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_21 = x_61;
x_22 = x_62;
goto block_56;
}
else
{
uint8_t x_63; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_12);
x_63 = !lean_is_exclusive(x_60);
if (x_63 == 0)
{
return x_60;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_60, 0);
x_65 = lean_ctor_get(x_60, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_60);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
block_56:
{
uint8_t x_23; uint8_t x_24; uint8_t x_25; 
x_23 = l_Lean_Syntax_isNone(x_12);
lean_dec(x_12);
x_24 = l_Lean_Syntax_isNone(x_16);
lean_dec(x_16);
x_25 = l_Lean_Syntax_isNone(x_14);
lean_dec(x_14);
if (x_23 == 0)
{
if (x_24 == 0)
{
if (x_25 == 0)
{
uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_26 = 1;
x_27 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_27, 0, x_17);
lean_ctor_set(x_27, 1, x_21);
lean_ctor_set_uint8(x_27, sizeof(void*)*2, x_19);
lean_ctor_set_uint8(x_27, sizeof(void*)*2 + 1, x_26);
lean_ctor_set_uint8(x_27, sizeof(void*)*2 + 2, x_26);
lean_ctor_set_uint8(x_27, sizeof(void*)*2 + 3, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_22);
return x_28;
}
else
{
uint8_t x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; 
x_29 = 1;
x_30 = 0;
x_31 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_31, 0, x_17);
lean_ctor_set(x_31, 1, x_21);
lean_ctor_set_uint8(x_31, sizeof(void*)*2, x_19);
lean_ctor_set_uint8(x_31, sizeof(void*)*2 + 1, x_29);
lean_ctor_set_uint8(x_31, sizeof(void*)*2 + 2, x_29);
lean_ctor_set_uint8(x_31, sizeof(void*)*2 + 3, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_22);
return x_32;
}
}
else
{
if (x_25 == 0)
{
uint8_t x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; 
x_33 = 1;
x_34 = 0;
x_35 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_35, 0, x_17);
lean_ctor_set(x_35, 1, x_21);
lean_ctor_set_uint8(x_35, sizeof(void*)*2, x_19);
lean_ctor_set_uint8(x_35, sizeof(void*)*2 + 1, x_33);
lean_ctor_set_uint8(x_35, sizeof(void*)*2 + 2, x_34);
lean_ctor_set_uint8(x_35, sizeof(void*)*2 + 3, x_33);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_22);
return x_36;
}
else
{
uint8_t x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; 
x_37 = 1;
x_38 = 0;
x_39 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_39, 0, x_17);
lean_ctor_set(x_39, 1, x_21);
lean_ctor_set_uint8(x_39, sizeof(void*)*2, x_19);
lean_ctor_set_uint8(x_39, sizeof(void*)*2 + 1, x_37);
lean_ctor_set_uint8(x_39, sizeof(void*)*2 + 2, x_38);
lean_ctor_set_uint8(x_39, sizeof(void*)*2 + 3, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_22);
return x_40;
}
}
}
else
{
if (x_24 == 0)
{
if (x_25 == 0)
{
uint8_t x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; 
x_41 = 0;
x_42 = 1;
x_43 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_43, 0, x_17);
lean_ctor_set(x_43, 1, x_21);
lean_ctor_set_uint8(x_43, sizeof(void*)*2, x_19);
lean_ctor_set_uint8(x_43, sizeof(void*)*2 + 1, x_41);
lean_ctor_set_uint8(x_43, sizeof(void*)*2 + 2, x_42);
lean_ctor_set_uint8(x_43, sizeof(void*)*2 + 3, x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_22);
return x_44;
}
else
{
uint8_t x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; 
x_45 = 0;
x_46 = 1;
x_47 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_47, 0, x_17);
lean_ctor_set(x_47, 1, x_21);
lean_ctor_set_uint8(x_47, sizeof(void*)*2, x_19);
lean_ctor_set_uint8(x_47, sizeof(void*)*2 + 1, x_45);
lean_ctor_set_uint8(x_47, sizeof(void*)*2 + 2, x_46);
lean_ctor_set_uint8(x_47, sizeof(void*)*2 + 3, x_45);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_22);
return x_48;
}
}
else
{
if (x_25 == 0)
{
uint8_t x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; 
x_49 = 0;
x_50 = 1;
x_51 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_51, 0, x_17);
lean_ctor_set(x_51, 1, x_21);
lean_ctor_set_uint8(x_51, sizeof(void*)*2, x_19);
lean_ctor_set_uint8(x_51, sizeof(void*)*2 + 1, x_49);
lean_ctor_set_uint8(x_51, sizeof(void*)*2 + 2, x_49);
lean_ctor_set_uint8(x_51, sizeof(void*)*2 + 3, x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_22);
return x_52;
}
else
{
uint8_t x_53; lean_object* x_54; lean_object* x_55; 
x_53 = 0;
x_54 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_54, 0, x_17);
lean_ctor_set(x_54, 1, x_21);
lean_ctor_set_uint8(x_54, sizeof(void*)*2, x_19);
lean_ctor_set_uint8(x_54, sizeof(void*)*2 + 1, x_53);
lean_ctor_set_uint8(x_54, sizeof(void*)*2 + 2, x_53);
lean_ctor_set_uint8(x_54, sizeof(void*)*2 + 3, x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_22);
return x_55;
}
}
}
}
}
}
}
}
lean_object* l_Lean_Elab_Command_elabModifiers___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabModifiers(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* _init_l_Lean_Elab_Command_checkNotAlreadyDeclared___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("a non-private declaration '");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_checkNotAlreadyDeclared___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_checkNotAlreadyDeclared___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_checkNotAlreadyDeclared___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_checkNotAlreadyDeclared___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_checkNotAlreadyDeclared___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("a private declaration '");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_checkNotAlreadyDeclared___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_checkNotAlreadyDeclared___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_checkNotAlreadyDeclared___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_checkNotAlreadyDeclared___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_checkNotAlreadyDeclared___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("private declaration '");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_checkNotAlreadyDeclared___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_checkNotAlreadyDeclared___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_checkNotAlreadyDeclared___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_checkNotAlreadyDeclared___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_checkNotAlreadyDeclared(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
x_5 = l_Lean_Elab_Command_getEnv___rarg(x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_36; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_8 = x_5;
} else {
 lean_dec_ref(x_5);
 x_8 = lean_box(0);
}
lean_inc(x_6);
x_36 = l_Lean_Environment_contains(x_6, x_1);
if (x_36 == 0)
{
x_9 = x_7;
goto block_35;
}
else
{
lean_object* x_37; 
lean_dec(x_8);
lean_dec(x_6);
lean_inc(x_1);
x_37 = lean_private_to_user_name(x_1);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_38 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_38, 0, x_1);
x_39 = l_Lean_Core_getConstInfo___closed__5;
x_40 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
x_41 = l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__5;
x_42 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_Lean_Elab_Command_throwError___rarg(x_42, x_2, x_3, x_7);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
return x_43;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_43, 0);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_43);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
lean_dec(x_1);
x_48 = lean_ctor_get(x_37, 0);
lean_inc(x_48);
lean_dec(x_37);
x_49 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_50 = l_Lean_Elab_Command_checkNotAlreadyDeclared___closed__9;
x_51 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
x_52 = l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__5;
x_53 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = l_Lean_Elab_Command_throwError___rarg(x_53, x_2, x_3, x_7);
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
return x_54;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_54, 0);
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_54);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
block_35:
{
lean_object* x_10; uint8_t x_11; 
lean_inc(x_1);
lean_inc(x_6);
x_10 = l_Lean_mkPrivateName(x_6, x_1);
lean_inc(x_6);
x_11 = l_Lean_Environment_contains(x_6, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_private_to_user_name(x_1);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_box(0);
if (lean_is_scalar(x_8)) {
 x_14 = lean_alloc_ctor(0, 2, 0);
} else {
 x_14 = x_8;
}
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_9);
return x_14;
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec(x_12);
x_16 = l_Lean_Environment_contains(x_6, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_2);
x_17 = lean_box(0);
if (lean_is_scalar(x_8)) {
 x_18 = lean_alloc_ctor(0, 2, 0);
} else {
 x_18 = x_8;
}
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_9);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_8);
x_19 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_19, 0, x_15);
x_20 = l_Lean_Elab_Command_checkNotAlreadyDeclared___closed__3;
x_21 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__5;
x_23 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_Elab_Command_throwError___rarg(x_23, x_2, x_3, x_9);
return x_24;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
lean_dec(x_8);
lean_dec(x_6);
x_25 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_25, 0, x_1);
x_26 = l_Lean_Elab_Command_checkNotAlreadyDeclared___closed__6;
x_27 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_28 = l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__5;
x_29 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_Elab_Command_throwError___rarg(x_29, x_2, x_3, x_9);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
return x_30;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_30);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_5);
if (x_59 == 0)
{
return x_5;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_5, 0);
x_61 = lean_ctor_get(x_5, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_5);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
}
lean_object* l_Lean_Elab_Command_applyVisibility(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_6; 
lean_inc(x_2);
x_6 = l_Lean_Elab_Command_checkNotAlreadyDeclared(x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_6, 0);
lean_dec(x_8);
lean_ctor_set(x_6, 0, x_2);
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
else
{
uint8_t x_11; 
lean_dec(x_2);
x_11 = !lean_is_exclusive(x_6);
if (x_11 == 0)
{
return x_6;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_6, 0);
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_6);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
case 1:
{
lean_object* x_15; 
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_15 = l_Lean_Elab_Command_checkNotAlreadyDeclared(x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
lean_inc(x_4);
x_17 = l_Lean_Elab_Command_getEnv___rarg(x_4, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_protectedExt;
lean_inc(x_2);
x_21 = l_Lean_PersistentEnvExtension_addEntry___rarg(x_20, x_18, x_2);
x_22 = l_Lean_Elab_Command_setEnv(x_21, x_3, x_4, x_19);
lean_dec(x_3);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
lean_ctor_set(x_22, 0, x_2);
return x_22;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_2);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_2);
x_27 = !lean_is_exclusive(x_22);
if (x_27 == 0)
{
return x_22;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_22, 0);
x_29 = lean_ctor_get(x_22, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_22);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
uint8_t x_31; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_31 = !lean_is_exclusive(x_17);
if (x_31 == 0)
{
return x_17;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_17, 0);
x_33 = lean_ctor_get(x_17, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_17);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_35 = !lean_is_exclusive(x_15);
if (x_35 == 0)
{
return x_15;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_15, 0);
x_37 = lean_ctor_get(x_15, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_15);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
default: 
{
lean_object* x_39; 
lean_inc(x_4);
x_39 = l_Lean_Elab_Command_getEnv___rarg(x_4, x_5);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Lean_mkPrivateName(x_40, x_2);
lean_inc(x_42);
x_43 = l_Lean_Elab_Command_checkNotAlreadyDeclared(x_42, x_3, x_4, x_41);
if (lean_obj_tag(x_43) == 0)
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_43, 0);
lean_dec(x_45);
lean_ctor_set(x_43, 0, x_42);
return x_43;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_dec(x_43);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_42);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
else
{
uint8_t x_48; 
lean_dec(x_42);
x_48 = !lean_is_exclusive(x_43);
if (x_48 == 0)
{
return x_43;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_43, 0);
x_50 = lean_ctor_get(x_43, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_43);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_52 = !lean_is_exclusive(x_39);
if (x_52 == 0)
{
return x_39;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_39, 0);
x_54 = lean_ctor_get(x_39, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_39);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
}
}
lean_object* l_Lean_Elab_Command_applyVisibility___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l_Lean_Elab_Command_applyVisibility(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
lean_object* l_Lean_Elab_Command_mkDeclName(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_4);
x_6 = l_Lean_Elab_Command_getCurrNamespace___rarg(x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_Name_append___main(x_7, x_2);
lean_dec(x_7);
x_10 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
x_11 = l_Lean_Elab_Command_applyVisibility(x_10, x_9, x_3, x_4, x_8);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_12 = !lean_is_exclusive(x_6);
if (x_12 == 0)
{
return x_6;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_6, 0);
x_14 = lean_ctor_get(x_6, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_6);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
lean_object* l_Lean_Elab_Command_mkDeclName___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Command_mkDeclName(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Array_forMAux___main___at_Lean_Elab_Command_applyAttributes___spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_38; uint8_t x_39; 
x_38 = lean_array_get_size(x_3);
x_39 = lean_nat_dec_lt(x_4, x_38);
lean_dec(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_7);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_array_fget(x_3, x_4);
lean_inc(x_6);
x_43 = l_Lean_Elab_Command_getEnv___rarg(x_6, x_7);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_ctor_get(x_42, 0);
lean_inc(x_46);
x_47 = l_Lean_getAttributeImpl(x_44, x_46);
lean_dec(x_44);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
lean_dec(x_42);
lean_dec(x_4);
lean_dec(x_1);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_50 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_50, 0, x_49);
x_51 = l_Lean_Elab_Command_throwError___rarg(x_50, x_5, x_6, x_45);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
return x_51;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_51, 0);
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_51);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
else
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_47);
if (x_56 == 0)
{
lean_object* x_57; uint8_t x_58; uint8_t x_59; 
x_57 = lean_ctor_get(x_47, 0);
x_58 = lean_ctor_get_uint8(x_57, sizeof(void*)*3);
x_59 = l_Lean_AttributeApplicationTime_beq(x_58, x_2);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
lean_free_object(x_47);
lean_dec(x_57);
lean_dec(x_42);
x_60 = lean_unsigned_to_nat(1u);
x_61 = lean_nat_add(x_4, x_60);
lean_dec(x_4);
x_4 = x_61;
x_7 = x_45;
goto _start;
}
else
{
lean_object* x_63; 
lean_inc(x_6);
x_63 = l_Lean_Elab_Command_getEnv___rarg(x_6, x_45);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = lean_ctor_get(x_57, 2);
lean_inc(x_66);
lean_dec(x_57);
x_67 = lean_ctor_get(x_42, 1);
lean_inc(x_67);
lean_dec(x_42);
x_68 = l_Lean_NameGenerator_Inhabited___closed__3;
x_69 = l_Lean_TraceState_Inhabited___closed__1;
x_70 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_70, 0, x_64);
lean_ctor_set(x_70, 1, x_68);
lean_ctor_set(x_70, 2, x_69);
x_71 = lean_alloc_closure((void*)(l_IO_Prim_mkRef___boxed), 3, 2);
lean_closure_set(x_71, 0, lean_box(0));
lean_closure_set(x_71, 1, x_70);
x_72 = l_Lean_Core_MonadIO;
x_73 = lean_apply_3(x_72, lean_box(0), x_71, x_65);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_121 = 1;
x_122 = l_Lean_Environment_addAttribute___closed__2;
x_123 = lean_box(x_121);
lean_inc(x_74);
lean_inc(x_1);
x_124 = lean_apply_6(x_66, x_1, x_67, x_123, x_122, x_74, x_75);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
lean_dec(x_124);
lean_inc(x_74);
x_127 = l_Lean_Core_getEnv___rarg(x_74, x_126);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_125);
lean_ctor_set(x_47, 0, x_130);
x_76 = x_47;
x_77 = x_129;
goto block_120;
}
else
{
lean_object* x_131; lean_object* x_132; 
lean_dec(x_125);
x_131 = lean_ctor_get(x_127, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_127, 1);
lean_inc(x_132);
lean_dec(x_127);
lean_ctor_set_tag(x_47, 0);
lean_ctor_set(x_47, 0, x_131);
x_76 = x_47;
x_77 = x_132;
goto block_120;
}
}
else
{
lean_object* x_133; lean_object* x_134; 
x_133 = lean_ctor_get(x_124, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_124, 1);
lean_inc(x_134);
lean_dec(x_124);
lean_ctor_set_tag(x_47, 0);
lean_ctor_set(x_47, 0, x_133);
x_76 = x_47;
x_77 = x_134;
goto block_120;
}
block_120:
{
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_78; lean_object* x_79; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_78 = lean_ctor_get(x_76, 0);
lean_inc(x_78);
lean_dec(x_76);
lean_inc(x_74);
x_79 = l_Lean_Core_getTraceState___at_Lean_Core_runCore___spec__1___rarg(x_74, x_77);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = lean_ctor_get(x_80, 0);
lean_inc(x_82);
lean_dec(x_80);
x_83 = l_Lean_Core_MonadIO;
x_84 = l_Lean_Environment_addAttribute___closed__2;
x_85 = l_Std_PersistentArray_forM___at_Lean_Core_runCore___spec__4(x_83, x_82, x_84, x_74, x_81);
lean_dec(x_74);
lean_dec(x_82);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; 
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
lean_dec(x_85);
x_8 = x_78;
x_9 = x_86;
goto block_37;
}
else
{
lean_object* x_87; lean_object* x_88; 
lean_dec(x_78);
x_87 = lean_ctor_get(x_85, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_85, 1);
lean_inc(x_88);
lean_dec(x_85);
x_8 = x_87;
x_9 = x_88;
goto block_37;
}
}
else
{
lean_object* x_89; lean_object* x_90; 
lean_dec(x_78);
lean_dec(x_74);
x_89 = lean_ctor_get(x_79, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_79, 1);
lean_inc(x_90);
lean_dec(x_79);
x_8 = x_89;
x_9 = x_90;
goto block_37;
}
}
else
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_76, 0);
lean_inc(x_91);
lean_dec(x_76);
lean_inc(x_74);
x_92 = l_Lean_Core_getTraceState___at_Lean_Core_runCore___spec__1___rarg(x_74, x_77);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
x_95 = lean_ctor_get(x_93, 0);
lean_inc(x_95);
lean_dec(x_93);
x_96 = l_Lean_Core_MonadIO;
x_97 = l_Lean_Environment_addAttribute___closed__2;
x_98 = l_Std_PersistentArray_forM___at_Lean_Core_runCore___spec__4(x_96, x_95, x_97, x_74, x_94);
lean_dec(x_95);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
lean_dec(x_98);
x_100 = lean_alloc_closure((void*)(l_IO_Prim_Ref_get___boxed), 3, 2);
lean_closure_set(x_100, 0, lean_box(0));
lean_closure_set(x_100, 1, x_74);
x_101 = l_Lean_Core_MonadIO;
x_102 = lean_apply_3(x_101, lean_box(0), x_100, x_99);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
lean_dec(x_102);
x_104 = lean_ctor_get(x_91, 0);
lean_inc(x_104);
lean_dec(x_91);
lean_inc(x_6);
x_105 = l_Lean_Elab_Command_setEnv(x_104, x_5, x_6, x_103);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_105, 1);
lean_inc(x_106);
lean_dec(x_105);
x_107 = lean_unsigned_to_nat(1u);
x_108 = lean_nat_add(x_4, x_107);
lean_dec(x_4);
x_4 = x_108;
x_7 = x_106;
goto _start;
}
else
{
uint8_t x_110; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_110 = !lean_is_exclusive(x_105);
if (x_110 == 0)
{
return x_105;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_105, 0);
x_112 = lean_ctor_get(x_105, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_105);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
else
{
lean_object* x_114; lean_object* x_115; 
lean_dec(x_91);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_114 = lean_ctor_get(x_102, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_102, 1);
lean_inc(x_115);
lean_dec(x_102);
x_8 = x_114;
x_9 = x_115;
goto block_37;
}
}
else
{
lean_object* x_116; lean_object* x_117; 
lean_dec(x_91);
lean_dec(x_74);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_116 = lean_ctor_get(x_98, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_98, 1);
lean_inc(x_117);
lean_dec(x_98);
x_8 = x_116;
x_9 = x_117;
goto block_37;
}
}
else
{
lean_object* x_118; lean_object* x_119; 
lean_dec(x_91);
lean_dec(x_74);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_118 = lean_ctor_get(x_92, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_92, 1);
lean_inc(x_119);
lean_dec(x_92);
x_8 = x_118;
x_9 = x_119;
goto block_37;
}
}
}
}
else
{
lean_object* x_135; lean_object* x_136; 
lean_dec(x_67);
lean_dec(x_66);
lean_free_object(x_47);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_135 = lean_ctor_get(x_73, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_73, 1);
lean_inc(x_136);
lean_dec(x_73);
x_8 = x_135;
x_9 = x_136;
goto block_37;
}
}
else
{
uint8_t x_137; 
lean_free_object(x_47);
lean_dec(x_57);
lean_dec(x_42);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_137 = !lean_is_exclusive(x_63);
if (x_137 == 0)
{
return x_63;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_63, 0);
x_139 = lean_ctor_get(x_63, 1);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_63);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
return x_140;
}
}
}
}
else
{
lean_object* x_141; uint8_t x_142; uint8_t x_143; 
x_141 = lean_ctor_get(x_47, 0);
lean_inc(x_141);
lean_dec(x_47);
x_142 = lean_ctor_get_uint8(x_141, sizeof(void*)*3);
x_143 = l_Lean_AttributeApplicationTime_beq(x_142, x_2);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; 
lean_dec(x_141);
lean_dec(x_42);
x_144 = lean_unsigned_to_nat(1u);
x_145 = lean_nat_add(x_4, x_144);
lean_dec(x_4);
x_4 = x_145;
x_7 = x_45;
goto _start;
}
else
{
lean_object* x_147; 
lean_inc(x_6);
x_147 = l_Lean_Elab_Command_getEnv___rarg(x_6, x_45);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
lean_dec(x_147);
x_150 = lean_ctor_get(x_141, 2);
lean_inc(x_150);
lean_dec(x_141);
x_151 = lean_ctor_get(x_42, 1);
lean_inc(x_151);
lean_dec(x_42);
x_152 = l_Lean_NameGenerator_Inhabited___closed__3;
x_153 = l_Lean_TraceState_Inhabited___closed__1;
x_154 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_154, 0, x_148);
lean_ctor_set(x_154, 1, x_152);
lean_ctor_set(x_154, 2, x_153);
x_155 = lean_alloc_closure((void*)(l_IO_Prim_mkRef___boxed), 3, 2);
lean_closure_set(x_155, 0, lean_box(0));
lean_closure_set(x_155, 1, x_154);
x_156 = l_Lean_Core_MonadIO;
x_157 = lean_apply_3(x_156, lean_box(0), x_155, x_149);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
lean_dec(x_157);
x_205 = 1;
x_206 = l_Lean_Environment_addAttribute___closed__2;
x_207 = lean_box(x_205);
lean_inc(x_158);
lean_inc(x_1);
x_208 = lean_apply_6(x_150, x_1, x_151, x_207, x_206, x_158, x_159);
if (lean_obj_tag(x_208) == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_209 = lean_ctor_get(x_208, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_208, 1);
lean_inc(x_210);
lean_dec(x_208);
lean_inc(x_158);
x_211 = l_Lean_Core_getEnv___rarg(x_158, x_210);
if (lean_obj_tag(x_211) == 0)
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_212 = lean_ctor_get(x_211, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_211, 1);
lean_inc(x_213);
lean_dec(x_211);
x_214 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_214, 0, x_212);
lean_ctor_set(x_214, 1, x_209);
x_215 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_215, 0, x_214);
x_160 = x_215;
x_161 = x_213;
goto block_204;
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; 
lean_dec(x_209);
x_216 = lean_ctor_get(x_211, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_211, 1);
lean_inc(x_217);
lean_dec(x_211);
x_218 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_218, 0, x_216);
x_160 = x_218;
x_161 = x_217;
goto block_204;
}
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_219 = lean_ctor_get(x_208, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_208, 1);
lean_inc(x_220);
lean_dec(x_208);
x_221 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_221, 0, x_219);
x_160 = x_221;
x_161 = x_220;
goto block_204;
}
block_204:
{
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_162; lean_object* x_163; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_162 = lean_ctor_get(x_160, 0);
lean_inc(x_162);
lean_dec(x_160);
lean_inc(x_158);
x_163 = l_Lean_Core_getTraceState___at_Lean_Core_runCore___spec__1___rarg(x_158, x_161);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
lean_dec(x_163);
x_166 = lean_ctor_get(x_164, 0);
lean_inc(x_166);
lean_dec(x_164);
x_167 = l_Lean_Core_MonadIO;
x_168 = l_Lean_Environment_addAttribute___closed__2;
x_169 = l_Std_PersistentArray_forM___at_Lean_Core_runCore___spec__4(x_167, x_166, x_168, x_158, x_165);
lean_dec(x_158);
lean_dec(x_166);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_170; 
x_170 = lean_ctor_get(x_169, 1);
lean_inc(x_170);
lean_dec(x_169);
x_8 = x_162;
x_9 = x_170;
goto block_37;
}
else
{
lean_object* x_171; lean_object* x_172; 
lean_dec(x_162);
x_171 = lean_ctor_get(x_169, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_169, 1);
lean_inc(x_172);
lean_dec(x_169);
x_8 = x_171;
x_9 = x_172;
goto block_37;
}
}
else
{
lean_object* x_173; lean_object* x_174; 
lean_dec(x_162);
lean_dec(x_158);
x_173 = lean_ctor_get(x_163, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_163, 1);
lean_inc(x_174);
lean_dec(x_163);
x_8 = x_173;
x_9 = x_174;
goto block_37;
}
}
else
{
lean_object* x_175; lean_object* x_176; 
x_175 = lean_ctor_get(x_160, 0);
lean_inc(x_175);
lean_dec(x_160);
lean_inc(x_158);
x_176 = l_Lean_Core_getTraceState___at_Lean_Core_runCore___spec__1___rarg(x_158, x_161);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_176, 1);
lean_inc(x_178);
lean_dec(x_176);
x_179 = lean_ctor_get(x_177, 0);
lean_inc(x_179);
lean_dec(x_177);
x_180 = l_Lean_Core_MonadIO;
x_181 = l_Lean_Environment_addAttribute___closed__2;
x_182 = l_Std_PersistentArray_forM___at_Lean_Core_runCore___spec__4(x_180, x_179, x_181, x_158, x_178);
lean_dec(x_179);
if (lean_obj_tag(x_182) == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_183 = lean_ctor_get(x_182, 1);
lean_inc(x_183);
lean_dec(x_182);
x_184 = lean_alloc_closure((void*)(l_IO_Prim_Ref_get___boxed), 3, 2);
lean_closure_set(x_184, 0, lean_box(0));
lean_closure_set(x_184, 1, x_158);
x_185 = l_Lean_Core_MonadIO;
x_186 = lean_apply_3(x_185, lean_box(0), x_184, x_183);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_187 = lean_ctor_get(x_186, 1);
lean_inc(x_187);
lean_dec(x_186);
x_188 = lean_ctor_get(x_175, 0);
lean_inc(x_188);
lean_dec(x_175);
lean_inc(x_6);
x_189 = l_Lean_Elab_Command_setEnv(x_188, x_5, x_6, x_187);
if (lean_obj_tag(x_189) == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_190 = lean_ctor_get(x_189, 1);
lean_inc(x_190);
lean_dec(x_189);
x_191 = lean_unsigned_to_nat(1u);
x_192 = lean_nat_add(x_4, x_191);
lean_dec(x_4);
x_4 = x_192;
x_7 = x_190;
goto _start;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_194 = lean_ctor_get(x_189, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_189, 1);
lean_inc(x_195);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 x_196 = x_189;
} else {
 lean_dec_ref(x_189);
 x_196 = lean_box(0);
}
if (lean_is_scalar(x_196)) {
 x_197 = lean_alloc_ctor(1, 2, 0);
} else {
 x_197 = x_196;
}
lean_ctor_set(x_197, 0, x_194);
lean_ctor_set(x_197, 1, x_195);
return x_197;
}
}
else
{
lean_object* x_198; lean_object* x_199; 
lean_dec(x_175);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_198 = lean_ctor_get(x_186, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_186, 1);
lean_inc(x_199);
lean_dec(x_186);
x_8 = x_198;
x_9 = x_199;
goto block_37;
}
}
else
{
lean_object* x_200; lean_object* x_201; 
lean_dec(x_175);
lean_dec(x_158);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_200 = lean_ctor_get(x_182, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_182, 1);
lean_inc(x_201);
lean_dec(x_182);
x_8 = x_200;
x_9 = x_201;
goto block_37;
}
}
else
{
lean_object* x_202; lean_object* x_203; 
lean_dec(x_175);
lean_dec(x_158);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_202 = lean_ctor_get(x_176, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_176, 1);
lean_inc(x_203);
lean_dec(x_176);
x_8 = x_202;
x_9 = x_203;
goto block_37;
}
}
}
}
else
{
lean_object* x_222; lean_object* x_223; 
lean_dec(x_151);
lean_dec(x_150);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_222 = lean_ctor_get(x_157, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_157, 1);
lean_inc(x_223);
lean_dec(x_157);
x_8 = x_222;
x_9 = x_223;
goto block_37;
}
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
lean_dec(x_141);
lean_dec(x_42);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_224 = lean_ctor_get(x_147, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_147, 1);
lean_inc(x_225);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 x_226 = x_147;
} else {
 lean_dec_ref(x_147);
 x_226 = lean_box(0);
}
if (lean_is_scalar(x_226)) {
 x_227 = lean_alloc_ctor(1, 2, 0);
} else {
 x_227 = x_226;
}
lean_ctor_set(x_227, 0, x_224);
lean_ctor_set(x_227, 1, x_225);
return x_227;
}
}
}
}
}
else
{
uint8_t x_228; 
lean_dec(x_42);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_228 = !lean_is_exclusive(x_43);
if (x_228 == 0)
{
return x_43;
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_229 = lean_ctor_get(x_43, 0);
x_230 = lean_ctor_get(x_43, 1);
lean_inc(x_230);
lean_inc(x_229);
lean_dec(x_43);
x_231 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_231, 0, x_229);
lean_ctor_set(x_231, 1, x_230);
return x_231;
}
}
}
block_37:
{
switch (lean_obj_tag(x_8)) {
case 0:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_5, 6);
lean_inc(x_11);
x_12 = l___private_Lean_Elab_Command_1__ioErrorToMessage(x_5, x_11, x_10);
lean_dec(x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_9);
return x_14;
}
case 1:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_15 = lean_ctor_get(x_8, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_8, 1);
lean_inc(x_16);
lean_dec(x_8);
x_17 = l_Lean_KernelException_toMessageData(x_15, x_16);
x_18 = lean_box(0);
x_19 = l_Lean_MessageData_formatAux___main(x_18, x_17);
x_20 = l_Lean_Options_empty;
x_21 = l_Lean_Format_pretty(x_19, x_20);
x_22 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_ctor_get(x_5, 6);
lean_inc(x_23);
x_24 = l___private_Lean_Elab_Command_1__ioErrorToMessage(x_5, x_23, x_22);
lean_dec(x_23);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_9);
return x_26;
}
default: 
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_27 = lean_ctor_get(x_8, 1);
lean_inc(x_27);
lean_dec(x_8);
x_28 = lean_box(0);
x_29 = l_Lean_MessageData_formatAux___main(x_28, x_27);
x_30 = l_Lean_Options_empty;
x_31 = l_Lean_Format_pretty(x_29, x_30);
x_32 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_ctor_get(x_5, 6);
lean_inc(x_33);
x_34 = l___private_Lean_Elab_Command_1__ioErrorToMessage(x_5, x_33, x_32);
lean_dec(x_33);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_9);
return x_36;
}
}
}
}
}
lean_object* l_Lean_Elab_Command_applyAttributes(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_forMAux___main___at_Lean_Elab_Command_applyAttributes___spec__1(x_1, x_3, x_2, x_7, x_4, x_5, x_6);
return x_8;
}
}
lean_object* l_Array_forMAux___main___at_Lean_Elab_Command_applyAttributes___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Array_forMAux___main___at_Lean_Elab_Command_applyAttributes___spec__1(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Lean_Elab_Command_applyAttributes___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_Lean_Elab_Command_applyAttributes(x_1, x_2, x_7, x_4, x_5, x_6);
lean_dec(x_2);
return x_8;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Elab_Command(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Elab_DeclModifiers(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Command(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Command_Attribute_hasFormat___closed__1 = _init_l_Lean_Elab_Command_Attribute_hasFormat___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_Attribute_hasFormat___closed__1);
l_Lean_Elab_Command_Attribute_hasFormat___closed__2 = _init_l_Lean_Elab_Command_Attribute_hasFormat___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_Attribute_hasFormat___closed__2);
l_Lean_Elab_Command_Attribute_inhabited___closed__1 = _init_l_Lean_Elab_Command_Attribute_inhabited___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_Attribute_inhabited___closed__1);
l_Lean_Elab_Command_Attribute_inhabited = _init_l_Lean_Elab_Command_Attribute_inhabited();
lean_mark_persistent(l_Lean_Elab_Command_Attribute_inhabited);
l_Lean_Elab_Command_Visibility_hasToString___closed__1 = _init_l_Lean_Elab_Command_Visibility_hasToString___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_Visibility_hasToString___closed__1);
l_Lean_Elab_Command_Modifiers_hasFormat___closed__1 = _init_l_Lean_Elab_Command_Modifiers_hasFormat___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_Modifiers_hasFormat___closed__1);
l_Lean_Elab_Command_Modifiers_hasFormat___closed__2 = _init_l_Lean_Elab_Command_Modifiers_hasFormat___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_Modifiers_hasFormat___closed__2);
l_Lean_Elab_Command_Modifiers_hasFormat___closed__3 = _init_l_Lean_Elab_Command_Modifiers_hasFormat___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_Modifiers_hasFormat___closed__3);
l_Lean_Elab_Command_Modifiers_hasFormat___closed__4 = _init_l_Lean_Elab_Command_Modifiers_hasFormat___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_Modifiers_hasFormat___closed__4);
l_Lean_Elab_Command_Modifiers_hasFormat___closed__5 = _init_l_Lean_Elab_Command_Modifiers_hasFormat___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_Modifiers_hasFormat___closed__5);
l_Lean_Elab_Command_Modifiers_hasFormat___closed__6 = _init_l_Lean_Elab_Command_Modifiers_hasFormat___closed__6();
lean_mark_persistent(l_Lean_Elab_Command_Modifiers_hasFormat___closed__6);
l_Lean_Elab_Command_Modifiers_hasFormat___closed__7 = _init_l_Lean_Elab_Command_Modifiers_hasFormat___closed__7();
lean_mark_persistent(l_Lean_Elab_Command_Modifiers_hasFormat___closed__7);
l_Lean_Elab_Command_Modifiers_hasFormat___closed__8 = _init_l_Lean_Elab_Command_Modifiers_hasFormat___closed__8();
lean_mark_persistent(l_Lean_Elab_Command_Modifiers_hasFormat___closed__8);
l_Lean_Elab_Command_Modifiers_hasFormat___closed__9 = _init_l_Lean_Elab_Command_Modifiers_hasFormat___closed__9();
lean_mark_persistent(l_Lean_Elab_Command_Modifiers_hasFormat___closed__9);
l_Lean_Elab_Command_Modifiers_hasFormat___closed__10 = _init_l_Lean_Elab_Command_Modifiers_hasFormat___closed__10();
lean_mark_persistent(l_Lean_Elab_Command_Modifiers_hasFormat___closed__10);
l_Lean_Elab_Command_Modifiers_hasFormat___closed__11 = _init_l_Lean_Elab_Command_Modifiers_hasFormat___closed__11();
lean_mark_persistent(l_Lean_Elab_Command_Modifiers_hasFormat___closed__11);
l_Lean_Elab_Command_Modifiers_hasFormat___closed__12 = _init_l_Lean_Elab_Command_Modifiers_hasFormat___closed__12();
lean_mark_persistent(l_Lean_Elab_Command_Modifiers_hasFormat___closed__12);
l_Lean_Elab_Command_Modifiers_hasFormat___closed__13 = _init_l_Lean_Elab_Command_Modifiers_hasFormat___closed__13();
lean_mark_persistent(l_Lean_Elab_Command_Modifiers_hasFormat___closed__13);
l_Lean_Elab_Command_Modifiers_hasFormat___closed__14 = _init_l_Lean_Elab_Command_Modifiers_hasFormat___closed__14();
lean_mark_persistent(l_Lean_Elab_Command_Modifiers_hasFormat___closed__14);
l_Lean_Elab_Command_Modifiers_hasFormat___closed__15 = _init_l_Lean_Elab_Command_Modifiers_hasFormat___closed__15();
lean_mark_persistent(l_Lean_Elab_Command_Modifiers_hasFormat___closed__15);
l_Lean_Elab_Command_Modifiers_hasFormat___closed__16 = _init_l_Lean_Elab_Command_Modifiers_hasFormat___closed__16();
lean_mark_persistent(l_Lean_Elab_Command_Modifiers_hasFormat___closed__16);
l_Lean_Elab_Command_Modifiers_hasToString___closed__1 = _init_l_Lean_Elab_Command_Modifiers_hasToString___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_Modifiers_hasToString___closed__1);
l_Lean_Elab_Command_Modifiers_hasToString___closed__2 = _init_l_Lean_Elab_Command_Modifiers_hasToString___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_Modifiers_hasToString___closed__2);
l_Lean_Elab_Command_Modifiers_hasToString = _init_l_Lean_Elab_Command_Modifiers_hasToString();
lean_mark_persistent(l_Lean_Elab_Command_Modifiers_hasToString);
l_Lean_Elab_Command_elabAttr___closed__1 = _init_l_Lean_Elab_Command_elabAttr___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabAttr___closed__1);
l_Lean_Elab_Command_elabAttr___closed__2 = _init_l_Lean_Elab_Command_elabAttr___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabAttr___closed__2);
l_Lean_Elab_Command_elabAttr___closed__3 = _init_l_Lean_Elab_Command_elabAttr___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabAttr___closed__3);
l_Lean_Elab_Command_elabAttr___closed__4 = _init_l_Lean_Elab_Command_elabAttr___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_elabAttr___closed__4);
l_Lean_Elab_Command_elabAttr___closed__5 = _init_l_Lean_Elab_Command_elabAttr___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_elabAttr___closed__5);
l_Lean_Elab_Command_elabAttr___closed__6 = _init_l_Lean_Elab_Command_elabAttr___closed__6();
lean_mark_persistent(l_Lean_Elab_Command_elabAttr___closed__6);
l_Lean_Elab_Command_elabModifiers___closed__1 = _init_l_Lean_Elab_Command_elabModifiers___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabModifiers___closed__1);
l_Lean_Elab_Command_elabModifiers___closed__2 = _init_l_Lean_Elab_Command_elabModifiers___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabModifiers___closed__2);
l_Lean_Elab_Command_elabModifiers___closed__3 = _init_l_Lean_Elab_Command_elabModifiers___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabModifiers___closed__3);
l_Lean_Elab_Command_elabModifiers___closed__4 = _init_l_Lean_Elab_Command_elabModifiers___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_elabModifiers___closed__4);
l_Lean_Elab_Command_elabModifiers___closed__5 = _init_l_Lean_Elab_Command_elabModifiers___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_elabModifiers___closed__5);
l_Lean_Elab_Command_elabModifiers___closed__6 = _init_l_Lean_Elab_Command_elabModifiers___closed__6();
lean_mark_persistent(l_Lean_Elab_Command_elabModifiers___closed__6);
l_Lean_Elab_Command_elabModifiers___closed__7 = _init_l_Lean_Elab_Command_elabModifiers___closed__7();
lean_mark_persistent(l_Lean_Elab_Command_elabModifiers___closed__7);
l_Lean_Elab_Command_checkNotAlreadyDeclared___closed__1 = _init_l_Lean_Elab_Command_checkNotAlreadyDeclared___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_checkNotAlreadyDeclared___closed__1);
l_Lean_Elab_Command_checkNotAlreadyDeclared___closed__2 = _init_l_Lean_Elab_Command_checkNotAlreadyDeclared___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_checkNotAlreadyDeclared___closed__2);
l_Lean_Elab_Command_checkNotAlreadyDeclared___closed__3 = _init_l_Lean_Elab_Command_checkNotAlreadyDeclared___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_checkNotAlreadyDeclared___closed__3);
l_Lean_Elab_Command_checkNotAlreadyDeclared___closed__4 = _init_l_Lean_Elab_Command_checkNotAlreadyDeclared___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_checkNotAlreadyDeclared___closed__4);
l_Lean_Elab_Command_checkNotAlreadyDeclared___closed__5 = _init_l_Lean_Elab_Command_checkNotAlreadyDeclared___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_checkNotAlreadyDeclared___closed__5);
l_Lean_Elab_Command_checkNotAlreadyDeclared___closed__6 = _init_l_Lean_Elab_Command_checkNotAlreadyDeclared___closed__6();
lean_mark_persistent(l_Lean_Elab_Command_checkNotAlreadyDeclared___closed__6);
l_Lean_Elab_Command_checkNotAlreadyDeclared___closed__7 = _init_l_Lean_Elab_Command_checkNotAlreadyDeclared___closed__7();
lean_mark_persistent(l_Lean_Elab_Command_checkNotAlreadyDeclared___closed__7);
l_Lean_Elab_Command_checkNotAlreadyDeclared___closed__8 = _init_l_Lean_Elab_Command_checkNotAlreadyDeclared___closed__8();
lean_mark_persistent(l_Lean_Elab_Command_checkNotAlreadyDeclared___closed__8);
l_Lean_Elab_Command_checkNotAlreadyDeclared___closed__9 = _init_l_Lean_Elab_Command_checkNotAlreadyDeclared___closed__9();
lean_mark_persistent(l_Lean_Elab_Command_checkNotAlreadyDeclared___closed__9);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
