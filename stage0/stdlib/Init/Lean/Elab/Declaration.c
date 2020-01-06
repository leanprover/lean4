// Lean compiler output
// Module: Init.Lean.Elab.Declaration
// Imports: Init.Lean.Util.CollectLevelParams Init.Lean.Elab.Definition
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
lean_object* l_Lean_Elab_Command_elabDeclaration(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabConstant___closed__9;
lean_object* l_Lean_Elab_Term_mkForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Command_10__addScopes___main(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_abbrev___elambda__1___closed__2;
lean_object* l_Lean_Elab_Command_addDecl(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instantiateMVars(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabAxiom___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabConstant___closed__4;
lean_object* l_unreachable_x21___rarg(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_elabAxiom___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabDeclaration(lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
lean_object* l_Lean_Elab_throwError___at_Lean_Elab_Command_elabCommand___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_mkEqTrans___closed__3;
lean_object* l_Lean_Elab_Command_elabConstant___closed__2;
lean_object* l_Lean_Elab_Command_elabDeclaration___closed__4;
lean_object* l_Lean_Syntax_getIdAt(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabExample(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabAbbrev(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_runTermElabM___rarg___closed__1;
lean_object* l_Lean_Elab_Command_elabExample___closed__1;
lean_object* l_Lean_Elab_Command_elabConstant___closed__1;
extern lean_object* l_Lean_stxInh;
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_elabAxiom___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_expandDeclSig(lean_object*);
lean_object* l_Lean_Elab_Command_elabExample___closed__2;
uint8_t lean_name_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_declaration___elambda__1___closed__2;
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Command_7__getVarDecls(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Elab_Term_mkForallUsedOnly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabDeclaration___closed__2;
lean_object* lean_string_utf8_byte_size(lean_object*);
extern lean_object* l_Lean_Parser_Command_example___elambda__1___closed__2;
lean_object* l_Lean_Elab_Command_elabAxiom___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_getNumParts___main(lean_object*);
lean_object* l_Lean_Elab_Command_elabInductive___rarg(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_addBuiltinCommandElab(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_classInductive___elambda__1___closed__2;
lean_object* l_Lean_Elab_Command_mkDeclName(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabDeclaration___closed__1;
lean_object* l_Lean_Elab_Command_expandOptDeclSig___boxed(lean_object*);
lean_object* l_Lean_Elab_mkMessage___at_Lean_Elab_Command_elabCommand___spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_Name_appendIndexAfter___closed__1;
lean_object* l_Lean_Elab_Term_levelMVarToParam(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_id___elambda__1___closed__2;
lean_object* l_Lean_Elab_Command_elabStructure___rarg(lean_object*);
lean_object* l_Lean_Elab_Command_elabAxiom(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabInstance___closed__1;
extern lean_object* l_Lean_Parser_Command_def___elambda__1___closed__2;
extern lean_object* l_Lean_Meta_registerInstanceAttr___closed__1;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabConstant(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabAxiom___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_expandOptDeclSig(lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabDeclaration___closed__3;
extern lean_object* l_Lean_Meta_registerInstanceAttr___closed__2;
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_Elab_Command_elabClassInductive(lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabAxiom___spec__4(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_namespace___elambda__1___closed__1;
extern lean_object* l___regBuiltinParser_Lean_Parser_Command_antiquot___closed__2;
lean_object* l_Lean_Elab_Command_elabConstant___closed__7;
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabAxiom___spec__3(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_hole___elambda__1___closed__1;
lean_object* l_Lean_Elab_Command_elabTheorem(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_modifyScope___closed__1;
uint8_t l_List_elem___main___at_Lean_Parser_addLeadingParser___spec__4(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabDef(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_withDeclId___closed__3;
lean_object* l_Lean_Elab_Command_elabAxiom___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_sortDeclLevelParams(lean_object*, lean_object*);
extern lean_object* l___private_Init_Lean_Elab_Term_16__synthesizeSyntheticMVar___closed__3;
lean_object* l_Lean_Elab_Command_elabClassInductive___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkReducibilityAttrs___closed__4;
lean_object* l___private_Init_Lean_Elab_Command_2__getState(lean_object*, lean_object*);
lean_object* l_List_drop___main___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabAbbrev___closed__3;
lean_object* l_Lean_Elab_Command_elabStructure___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabInstance(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_axiom___elambda__1___closed__2;
lean_object* l_Lean_Elab_Command_getCurrMacroScope(lean_object*, lean_object*);
extern lean_object* l_Lean_Syntax_asNode___closed__1;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Elab_Command_elabInductive___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_app___elambda__1___closed__2;
lean_object* l_Lean_Elab_Command_elabAbbrev___closed__2;
lean_object* l_Lean_Elab_Command_elabStructure(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_Modifiers_addAttribute(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabType(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_structure___elambda__1___closed__2;
extern lean_object* l_Lean_Elab_Command_declareBuiltinCommandElab___closed__3;
lean_object* l_Lean_Elab_Command_elabConstant___closed__6;
extern lean_object* l_Lean_Parser_Command_inductive___elambda__1___closed__2;
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_Elab_Command_applyAttributes___spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__1;
lean_object* l_Lean_Elab_Command_getLevelNames(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabModifiers(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabDefLike(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_foldArgsAuxM___main___at_Lean_Syntax_foldSepRevArgsM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_expandDeclSig___boxed(lean_object*);
lean_object* l_Lean_Elab_throwError___at_Lean_Elab_Command_elabInstance___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabDeclaration___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabBinders___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Init_Lean_Elab_Term_8__expandCDot___closed__5;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabDeclaration___closed__2;
lean_object* l_Lean_Elab_Command_elabAxiom___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabConstant___closed__5;
lean_object* l_Lean_Elab_Command_elabInductive(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_collectLevelParams(lean_object*);
lean_object* l_Lean_Elab_Command_elabDeclaration___closed__1;
lean_object* l___private_Init_Lean_Elab_Term_19__synthesizeSyntheticMVarsAux___main(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabDeclaration___closed__3;
lean_object* l_Lean_Elab_Command_elabConstant___closed__3;
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabAxiom___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabAbbrev___closed__1;
lean_object* l_Lean_Elab_Command_elabAbbrev___closed__4;
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabAxiom___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_numeral(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_constant___elambda__1___closed__2;
lean_object* l___private_Init_Lean_Elab_Command_5__mkTermContext(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabConstant___closed__8;
extern lean_object* l_Lean_Parser_Command_theorem___elambda__1___closed__2;
lean_object* l_Lean_Elab_Command_elabClassInductive___rarg(lean_object*);
lean_object* l___private_Init_Lean_Elab_Command_3__setState(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Command_6__mkTermState(lean_object*);
lean_object* l_Lean_Elab_throwError___at_Lean_Elab_Command_elabInstance___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_declId___elambda__1___closed__2;
lean_object* l_Lean_Elab_Command_expandOptDeclSig(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Syntax_getArg(x_1, x_2);
x_4 = lean_unsigned_to_nat(1u);
x_5 = l_Lean_Syntax_getArg(x_1, x_4);
x_6 = l_Lean_Syntax_isNone(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_Lean_Syntax_getArg(x_5, x_2);
lean_dec(x_5);
x_8 = l_Lean_Syntax_getArg(x_7, x_4);
lean_dec(x_7);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
lean_object* l_Lean_Elab_Command_expandOptDeclSig___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Command_expandOptDeclSig(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_expandDeclSig(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Syntax_getArg(x_1, x_2);
x_4 = lean_unsigned_to_nat(1u);
x_5 = l_Lean_Syntax_getArg(x_1, x_4);
x_6 = l_Lean_Syntax_getArg(x_5, x_4);
lean_dec(x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
lean_object* l_Lean_Elab_Command_expandDeclSig___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Command_expandDeclSig(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_elabAbbrev___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("inline");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_elabAbbrev___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabAbbrev___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_elabAbbrev___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabAbbrev___closed__2;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_elabAbbrev___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkReducibilityAttrs___closed__4;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_elabAbbrev(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_5 = lean_unsigned_to_nat(2u);
x_6 = l_Lean_Syntax_getArg(x_2, x_5);
x_7 = l_Lean_Elab_Command_expandOptDeclSig(x_6);
lean_dec(x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Elab_Command_elabAbbrev___closed__3;
x_11 = l_Lean_Elab_Command_Modifiers_addAttribute(x_1, x_10);
x_12 = l_Lean_Elab_Command_elabAbbrev___closed__4;
x_13 = l_Lean_Elab_Command_Modifiers_addAttribute(x_11, x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = l_Lean_Syntax_getArg(x_2, x_14);
x_16 = lean_unsigned_to_nat(3u);
x_17 = l_Lean_Syntax_getArg(x_2, x_16);
x_18 = 0;
x_19 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_19, 0, x_2);
lean_ctor_set(x_19, 1, x_13);
lean_ctor_set(x_19, 2, x_15);
lean_ctor_set(x_19, 3, x_8);
lean_ctor_set(x_19, 4, x_9);
lean_ctor_set(x_19, 5, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*6, x_18);
x_20 = l_Lean_Elab_Command_elabDefLike(x_19, x_3, x_4);
return x_20;
}
}
lean_object* l_Lean_Elab_Command_elabDef(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_5 = lean_unsigned_to_nat(2u);
x_6 = l_Lean_Syntax_getArg(x_2, x_5);
x_7 = l_Lean_Elab_Command_expandOptDeclSig(x_6);
lean_dec(x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_unsigned_to_nat(1u);
x_11 = l_Lean_Syntax_getArg(x_2, x_10);
x_12 = lean_unsigned_to_nat(3u);
x_13 = l_Lean_Syntax_getArg(x_2, x_12);
x_14 = 0;
x_15 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_1);
lean_ctor_set(x_15, 2, x_11);
lean_ctor_set(x_15, 3, x_8);
lean_ctor_set(x_15, 4, x_9);
lean_ctor_set(x_15, 5, x_13);
lean_ctor_set_uint8(x_15, sizeof(void*)*6, x_14);
x_16 = l_Lean_Elab_Command_elabDefLike(x_15, x_3, x_4);
return x_16;
}
}
lean_object* l_Lean_Elab_Command_elabTheorem(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_5 = lean_unsigned_to_nat(2u);
x_6 = l_Lean_Syntax_getArg(x_2, x_5);
x_7 = l_Lean_Elab_Command_expandDeclSig(x_6);
lean_dec(x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_unsigned_to_nat(1u);
x_11 = l_Lean_Syntax_getArg(x_2, x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_9);
x_13 = lean_unsigned_to_nat(3u);
x_14 = l_Lean_Syntax_getArg(x_2, x_13);
x_15 = 1;
x_16 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_1);
lean_ctor_set(x_16, 2, x_11);
lean_ctor_set(x_16, 3, x_8);
lean_ctor_set(x_16, 4, x_12);
lean_ctor_set(x_16, 5, x_14);
lean_ctor_set_uint8(x_16, sizeof(void*)*6, x_15);
x_17 = l_Lean_Elab_Command_elabDefLike(x_16, x_3, x_4);
return x_17;
}
}
lean_object* _init_l_Lean_Elab_Command_elabConstant___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("arbitrary");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_elabConstant___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabConstant___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_elabConstant___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Command_elabConstant___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Command_elabConstant___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Elab_Command_elabConstant___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabConstant___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_elabConstant___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabConstant___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_elabConstant___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabConstant___closed__5;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_elabConstant___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Name_appendIndexAfter___closed__1;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_elabConstant___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkOptionalNode___closed__1;
x_2 = l_Lean_Elab_Command_elabConstant___closed__7;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_elabConstant___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_hole___elambda__1___closed__1;
x_2 = l_Lean_Elab_Command_elabConstant___closed__8;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_elabConstant(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_unsigned_to_nat(2u);
x_6 = l_Lean_Syntax_getArg(x_2, x_5);
x_7 = l_Lean_Elab_Command_expandDeclSig(x_6);
lean_dec(x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_unsigned_to_nat(3u);
x_11 = l_Lean_Syntax_getArg(x_2, x_10);
x_12 = l_Lean_Syntax_getOptional_x3f(x_11);
lean_dec(x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; 
x_13 = l_Lean_Elab_Command_getCurrMacroScope(x_3, x_4);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_box(0);
x_17 = l_Lean_Elab_Command_elabConstant___closed__4;
x_18 = lean_name_mk_numeral(x_17, x_14);
x_19 = l_Lean_Elab_Command_elabConstant___closed__3;
x_20 = l_Lean_Elab_Command_elabConstant___closed__6;
x_21 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_21, 0, x_16);
lean_ctor_set(x_21, 1, x_19);
lean_ctor_set(x_21, 2, x_18);
lean_ctor_set(x_21, 3, x_20);
x_22 = l_Lean_Meta_mkEqTrans___closed__3;
x_23 = lean_array_push(x_22, x_21);
x_24 = l___private_Init_Lean_Elab_Term_8__expandCDot___closed__5;
x_25 = lean_array_push(x_23, x_24);
x_26 = l_Lean_Parser_Term_id___elambda__1___closed__2;
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_28 = lean_array_push(x_22, x_27);
x_29 = l_Lean_Elab_Command_elabConstant___closed__9;
x_30 = lean_array_push(x_28, x_29);
x_31 = l_Lean_Parser_Term_app___elambda__1___closed__2;
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
x_33 = lean_unsigned_to_nat(1u);
x_34 = l_Lean_Syntax_getArg(x_2, x_33);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_9);
x_36 = 3;
x_37 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_37, 0, x_2);
lean_ctor_set(x_37, 1, x_1);
lean_ctor_set(x_37, 2, x_34);
lean_ctor_set(x_37, 3, x_8);
lean_ctor_set(x_37, 4, x_35);
lean_ctor_set(x_37, 5, x_32);
lean_ctor_set_uint8(x_37, sizeof(void*)*6, x_36);
x_38 = l_Lean_Elab_Command_elabDefLike(x_37, x_3, x_15);
return x_38;
}
else
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_12);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_12, 0);
x_41 = lean_unsigned_to_nat(1u);
x_42 = l_Lean_Syntax_getArg(x_2, x_41);
lean_ctor_set(x_12, 0, x_9);
x_43 = 3;
x_44 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_44, 0, x_2);
lean_ctor_set(x_44, 1, x_1);
lean_ctor_set(x_44, 2, x_42);
lean_ctor_set(x_44, 3, x_8);
lean_ctor_set(x_44, 4, x_12);
lean_ctor_set(x_44, 5, x_40);
lean_ctor_set_uint8(x_44, sizeof(void*)*6, x_43);
x_45 = l_Lean_Elab_Command_elabDefLike(x_44, x_3, x_4);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; 
x_46 = lean_ctor_get(x_12, 0);
lean_inc(x_46);
lean_dec(x_12);
x_47 = lean_unsigned_to_nat(1u);
x_48 = l_Lean_Syntax_getArg(x_2, x_47);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_9);
x_50 = 3;
x_51 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_51, 0, x_2);
lean_ctor_set(x_51, 1, x_1);
lean_ctor_set(x_51, 2, x_48);
lean_ctor_set(x_51, 3, x_8);
lean_ctor_set(x_51, 4, x_49);
lean_ctor_set(x_51, 5, x_46);
lean_ctor_set_uint8(x_51, sizeof(void*)*6, x_50);
x_52 = l_Lean_Elab_Command_elabDefLike(x_51, x_3, x_4);
return x_52;
}
}
}
}
lean_object* l_Lean_Elab_throwError___at_Lean_Elab_Command_elabInstance___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; uint8_t x_7; 
x_5 = 2;
x_6 = l_Lean_Elab_mkMessage___at_Lean_Elab_Command_elabCommand___spec__2(x_2, x_5, x_1, x_3, x_4);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_ctor_set_tag(x_6, 1);
return x_6;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_6);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
}
lean_object* _init_l_Lean_Elab_Command_elabInstance___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_registerInstanceAttr___closed__2;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_elabInstance(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_5 = lean_unsigned_to_nat(2u);
x_6 = l_Lean_Syntax_getArg(x_2, x_5);
x_7 = l_Lean_Elab_Command_expandDeclSig(x_6);
lean_dec(x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Elab_Command_elabInstance___closed__1;
x_11 = l_Lean_Elab_Command_Modifiers_addAttribute(x_1, x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = l_Lean_Syntax_getArg(x_2, x_12);
x_14 = l_Lean_Syntax_getOptional_x3f(x_13);
lean_dec(x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
x_15 = l___private_Init_Lean_Elab_Term_16__synthesizeSyntheticMVar___closed__3;
x_16 = l_Lean_Elab_throwError___at_Lean_Elab_Command_elabInstance___spec__1(x_2, x_15, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
return x_16;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_16);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_14);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_14, 0);
lean_ctor_set(x_14, 0, x_9);
x_23 = lean_unsigned_to_nat(3u);
x_24 = l_Lean_Syntax_getArg(x_2, x_23);
x_25 = 0;
x_26 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_26, 0, x_2);
lean_ctor_set(x_26, 1, x_11);
lean_ctor_set(x_26, 2, x_22);
lean_ctor_set(x_26, 3, x_8);
lean_ctor_set(x_26, 4, x_14);
lean_ctor_set(x_26, 5, x_24);
lean_ctor_set_uint8(x_26, sizeof(void*)*6, x_25);
x_27 = l_Lean_Elab_Command_elabDefLike(x_26, x_3, x_4);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; 
x_28 = lean_ctor_get(x_14, 0);
lean_inc(x_28);
lean_dec(x_14);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_9);
x_30 = lean_unsigned_to_nat(3u);
x_31 = l_Lean_Syntax_getArg(x_2, x_30);
x_32 = 0;
x_33 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_33, 0, x_2);
lean_ctor_set(x_33, 1, x_11);
lean_ctor_set(x_33, 2, x_28);
lean_ctor_set(x_33, 3, x_8);
lean_ctor_set(x_33, 4, x_29);
lean_ctor_set(x_33, 5, x_31);
lean_ctor_set_uint8(x_33, sizeof(void*)*6, x_32);
x_34 = l_Lean_Elab_Command_elabDefLike(x_33, x_3, x_4);
return x_34;
}
}
}
}
lean_object* l_Lean_Elab_throwError___at_Lean_Elab_Command_elabInstance___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_throwError___at_Lean_Elab_Command_elabInstance___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* _init_l_Lean_Elab_Command_elabExample___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_example");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_elabExample___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabExample___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_elabExample(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Lean_Syntax_getArg(x_2, x_5);
x_7 = l_Lean_Elab_Command_expandDeclSig(x_6);
lean_dec(x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Elab_Command_elabExample___closed__2;
x_11 = l_Lean_mkIdentFrom(x_2, x_10);
x_12 = l_Lean_Meta_mkEqTrans___closed__3;
x_13 = lean_array_push(x_12, x_11);
x_14 = l_Lean_Syntax_asNode___closed__1;
x_15 = lean_array_push(x_13, x_14);
x_16 = l_Lean_Parser_Command_declId___elambda__1___closed__2;
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_9);
x_19 = lean_unsigned_to_nat(2u);
x_20 = l_Lean_Syntax_getArg(x_2, x_19);
x_21 = 2;
x_22 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_22, 0, x_2);
lean_ctor_set(x_22, 1, x_1);
lean_ctor_set(x_22, 2, x_17);
lean_ctor_set(x_22, 3, x_8);
lean_ctor_set(x_22, 4, x_18);
lean_ctor_set(x_22, 5, x_20);
lean_ctor_set_uint8(x_22, sizeof(void*)*6, x_21);
x_23 = l_Lean_Elab_Command_elabDefLike(x_22, x_3, x_4);
return x_23;
}
}
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabAxiom___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = l___private_Init_Lean_Elab_Command_2__getState(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; uint8_t x_8; 
lean_dec(x_1);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_5, 2);
lean_dec(x_9);
x_10 = l_Lean_Elab_Command_modifyScope___closed__1;
x_11 = l_unreachable_x21___rarg(x_10);
lean_ctor_set(x_5, 2, x_11);
x_12 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_7);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
x_15 = lean_box(0);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_12);
if (x_19 == 0)
{
return x_12;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_12, 0);
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_12);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_23 = lean_ctor_get(x_5, 0);
x_24 = lean_ctor_get(x_5, 1);
x_25 = lean_ctor_get(x_5, 3);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_5);
x_26 = l_Lean_Elab_Command_modifyScope___closed__1;
x_27 = l_unreachable_x21___rarg(x_26);
x_28 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_24);
lean_ctor_set(x_28, 2, x_27);
lean_ctor_set(x_28, 3, x_25);
x_29 = l___private_Init_Lean_Elab_Command_3__setState(x_28, x_2, x_7);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_31 = x_29;
} else {
 lean_dec_ref(x_29);
 x_31 = lean_box(0);
}
x_32 = lean_box(0);
if (lean_is_scalar(x_31)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_31;
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_29, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_36 = x_29;
} else {
 lean_dec_ref(x_29);
 x_36 = lean_box(0);
}
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(1, 2, 0);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_ctor_get(x_6, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_4, 1);
lean_inc(x_39);
lean_dec(x_4);
x_40 = !lean_is_exclusive(x_5);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_5, 2);
lean_dec(x_41);
x_42 = !lean_is_exclusive(x_6);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_6, 0);
lean_dec(x_43);
x_44 = !lean_is_exclusive(x_38);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_38, 5);
lean_dec(x_45);
lean_ctor_set(x_38, 5, x_1);
x_46 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_39);
if (lean_obj_tag(x_46) == 0)
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_46, 0);
lean_dec(x_48);
x_49 = lean_box(0);
lean_ctor_set(x_46, 0, x_49);
return x_46;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_46, 1);
lean_inc(x_50);
lean_dec(x_46);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
}
else
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_46);
if (x_53 == 0)
{
return x_46;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_46, 0);
x_55 = lean_ctor_get(x_46, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_46);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_57 = lean_ctor_get(x_38, 0);
x_58 = lean_ctor_get(x_38, 1);
x_59 = lean_ctor_get(x_38, 2);
x_60 = lean_ctor_get(x_38, 3);
x_61 = lean_ctor_get(x_38, 4);
x_62 = lean_ctor_get(x_38, 6);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_38);
x_63 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_63, 0, x_57);
lean_ctor_set(x_63, 1, x_58);
lean_ctor_set(x_63, 2, x_59);
lean_ctor_set(x_63, 3, x_60);
lean_ctor_set(x_63, 4, x_61);
lean_ctor_set(x_63, 5, x_1);
lean_ctor_set(x_63, 6, x_62);
lean_ctor_set(x_6, 0, x_63);
x_64 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_39);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_66 = x_64;
} else {
 lean_dec_ref(x_64);
 x_66 = lean_box(0);
}
x_67 = lean_box(0);
if (lean_is_scalar(x_66)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_66;
}
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_65);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_ctor_get(x_64, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_64, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_71 = x_64;
} else {
 lean_dec_ref(x_64);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(1, 2, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_73 = lean_ctor_get(x_6, 1);
lean_inc(x_73);
lean_dec(x_6);
x_74 = lean_ctor_get(x_38, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_38, 1);
lean_inc(x_75);
x_76 = lean_ctor_get(x_38, 2);
lean_inc(x_76);
x_77 = lean_ctor_get(x_38, 3);
lean_inc(x_77);
x_78 = lean_ctor_get(x_38, 4);
lean_inc(x_78);
x_79 = lean_ctor_get(x_38, 6);
lean_inc(x_79);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 lean_ctor_release(x_38, 2);
 lean_ctor_release(x_38, 3);
 lean_ctor_release(x_38, 4);
 lean_ctor_release(x_38, 5);
 lean_ctor_release(x_38, 6);
 x_80 = x_38;
} else {
 lean_dec_ref(x_38);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(0, 7, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_74);
lean_ctor_set(x_81, 1, x_75);
lean_ctor_set(x_81, 2, x_76);
lean_ctor_set(x_81, 3, x_77);
lean_ctor_set(x_81, 4, x_78);
lean_ctor_set(x_81, 5, x_1);
lean_ctor_set(x_81, 6, x_79);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_73);
lean_ctor_set(x_5, 2, x_82);
x_83 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_39);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_85 = x_83;
} else {
 lean_dec_ref(x_83);
 x_85 = lean_box(0);
}
x_86 = lean_box(0);
if (lean_is_scalar(x_85)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_85;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_84);
return x_87;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = lean_ctor_get(x_83, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_83, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_90 = x_83;
} else {
 lean_dec_ref(x_83);
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
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_92 = lean_ctor_get(x_5, 0);
x_93 = lean_ctor_get(x_5, 1);
x_94 = lean_ctor_get(x_5, 3);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_5);
x_95 = lean_ctor_get(x_6, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_96 = x_6;
} else {
 lean_dec_ref(x_6);
 x_96 = lean_box(0);
}
x_97 = lean_ctor_get(x_38, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_38, 1);
lean_inc(x_98);
x_99 = lean_ctor_get(x_38, 2);
lean_inc(x_99);
x_100 = lean_ctor_get(x_38, 3);
lean_inc(x_100);
x_101 = lean_ctor_get(x_38, 4);
lean_inc(x_101);
x_102 = lean_ctor_get(x_38, 6);
lean_inc(x_102);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 lean_ctor_release(x_38, 2);
 lean_ctor_release(x_38, 3);
 lean_ctor_release(x_38, 4);
 lean_ctor_release(x_38, 5);
 lean_ctor_release(x_38, 6);
 x_103 = x_38;
} else {
 lean_dec_ref(x_38);
 x_103 = lean_box(0);
}
if (lean_is_scalar(x_103)) {
 x_104 = lean_alloc_ctor(0, 7, 0);
} else {
 x_104 = x_103;
}
lean_ctor_set(x_104, 0, x_97);
lean_ctor_set(x_104, 1, x_98);
lean_ctor_set(x_104, 2, x_99);
lean_ctor_set(x_104, 3, x_100);
lean_ctor_set(x_104, 4, x_101);
lean_ctor_set(x_104, 5, x_1);
lean_ctor_set(x_104, 6, x_102);
if (lean_is_scalar(x_96)) {
 x_105 = lean_alloc_ctor(1, 2, 0);
} else {
 x_105 = x_96;
}
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_95);
x_106 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_106, 0, x_92);
lean_ctor_set(x_106, 1, x_93);
lean_ctor_set(x_106, 2, x_105);
lean_ctor_set(x_106, 3, x_94);
x_107 = l___private_Init_Lean_Elab_Command_3__setState(x_106, x_2, x_39);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_108 = lean_ctor_get(x_107, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_109 = x_107;
} else {
 lean_dec_ref(x_107);
 x_109 = lean_box(0);
}
x_110 = lean_box(0);
if (lean_is_scalar(x_109)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_109;
}
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_108);
return x_111;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_112 = lean_ctor_get(x_107, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_107, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_114 = x_107;
} else {
 lean_dec_ref(x_107);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(1, 2, 0);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_113);
return x_115;
}
}
}
}
else
{
uint8_t x_116; 
lean_dec(x_2);
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
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabAxiom___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = l___private_Init_Lean_Elab_Command_2__getState(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; uint8_t x_8; 
lean_dec(x_1);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_5, 2);
lean_dec(x_9);
x_10 = l_Lean_Elab_Command_modifyScope___closed__1;
x_11 = l_unreachable_x21___rarg(x_10);
lean_ctor_set(x_5, 2, x_11);
x_12 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_7);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
x_15 = lean_box(0);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_12);
if (x_19 == 0)
{
return x_12;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_12, 0);
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_12);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_23 = lean_ctor_get(x_5, 0);
x_24 = lean_ctor_get(x_5, 1);
x_25 = lean_ctor_get(x_5, 3);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_5);
x_26 = l_Lean_Elab_Command_modifyScope___closed__1;
x_27 = l_unreachable_x21___rarg(x_26);
x_28 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_24);
lean_ctor_set(x_28, 2, x_27);
lean_ctor_set(x_28, 3, x_25);
x_29 = l___private_Init_Lean_Elab_Command_3__setState(x_28, x_2, x_7);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_31 = x_29;
} else {
 lean_dec_ref(x_29);
 x_31 = lean_box(0);
}
x_32 = lean_box(0);
if (lean_is_scalar(x_31)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_31;
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_29, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_36 = x_29;
} else {
 lean_dec_ref(x_29);
 x_36 = lean_box(0);
}
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(1, 2, 0);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_ctor_get(x_6, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_4, 1);
lean_inc(x_39);
lean_dec(x_4);
x_40 = !lean_is_exclusive(x_5);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_5, 2);
lean_dec(x_41);
x_42 = !lean_is_exclusive(x_6);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_6, 0);
lean_dec(x_43);
x_44 = !lean_is_exclusive(x_38);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_38, 5);
lean_dec(x_45);
lean_ctor_set(x_38, 5, x_1);
x_46 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_39);
if (lean_obj_tag(x_46) == 0)
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_46, 0);
lean_dec(x_48);
x_49 = lean_box(0);
lean_ctor_set(x_46, 0, x_49);
return x_46;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_46, 1);
lean_inc(x_50);
lean_dec(x_46);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
}
else
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_46);
if (x_53 == 0)
{
return x_46;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_46, 0);
x_55 = lean_ctor_get(x_46, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_46);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_57 = lean_ctor_get(x_38, 0);
x_58 = lean_ctor_get(x_38, 1);
x_59 = lean_ctor_get(x_38, 2);
x_60 = lean_ctor_get(x_38, 3);
x_61 = lean_ctor_get(x_38, 4);
x_62 = lean_ctor_get(x_38, 6);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_38);
x_63 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_63, 0, x_57);
lean_ctor_set(x_63, 1, x_58);
lean_ctor_set(x_63, 2, x_59);
lean_ctor_set(x_63, 3, x_60);
lean_ctor_set(x_63, 4, x_61);
lean_ctor_set(x_63, 5, x_1);
lean_ctor_set(x_63, 6, x_62);
lean_ctor_set(x_6, 0, x_63);
x_64 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_39);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_66 = x_64;
} else {
 lean_dec_ref(x_64);
 x_66 = lean_box(0);
}
x_67 = lean_box(0);
if (lean_is_scalar(x_66)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_66;
}
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_65);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_ctor_get(x_64, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_64, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_71 = x_64;
} else {
 lean_dec_ref(x_64);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(1, 2, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_73 = lean_ctor_get(x_6, 1);
lean_inc(x_73);
lean_dec(x_6);
x_74 = lean_ctor_get(x_38, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_38, 1);
lean_inc(x_75);
x_76 = lean_ctor_get(x_38, 2);
lean_inc(x_76);
x_77 = lean_ctor_get(x_38, 3);
lean_inc(x_77);
x_78 = lean_ctor_get(x_38, 4);
lean_inc(x_78);
x_79 = lean_ctor_get(x_38, 6);
lean_inc(x_79);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 lean_ctor_release(x_38, 2);
 lean_ctor_release(x_38, 3);
 lean_ctor_release(x_38, 4);
 lean_ctor_release(x_38, 5);
 lean_ctor_release(x_38, 6);
 x_80 = x_38;
} else {
 lean_dec_ref(x_38);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(0, 7, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_74);
lean_ctor_set(x_81, 1, x_75);
lean_ctor_set(x_81, 2, x_76);
lean_ctor_set(x_81, 3, x_77);
lean_ctor_set(x_81, 4, x_78);
lean_ctor_set(x_81, 5, x_1);
lean_ctor_set(x_81, 6, x_79);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_73);
lean_ctor_set(x_5, 2, x_82);
x_83 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_39);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_85 = x_83;
} else {
 lean_dec_ref(x_83);
 x_85 = lean_box(0);
}
x_86 = lean_box(0);
if (lean_is_scalar(x_85)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_85;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_84);
return x_87;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = lean_ctor_get(x_83, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_83, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_90 = x_83;
} else {
 lean_dec_ref(x_83);
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
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_92 = lean_ctor_get(x_5, 0);
x_93 = lean_ctor_get(x_5, 1);
x_94 = lean_ctor_get(x_5, 3);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_5);
x_95 = lean_ctor_get(x_6, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_96 = x_6;
} else {
 lean_dec_ref(x_6);
 x_96 = lean_box(0);
}
x_97 = lean_ctor_get(x_38, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_38, 1);
lean_inc(x_98);
x_99 = lean_ctor_get(x_38, 2);
lean_inc(x_99);
x_100 = lean_ctor_get(x_38, 3);
lean_inc(x_100);
x_101 = lean_ctor_get(x_38, 4);
lean_inc(x_101);
x_102 = lean_ctor_get(x_38, 6);
lean_inc(x_102);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 lean_ctor_release(x_38, 2);
 lean_ctor_release(x_38, 3);
 lean_ctor_release(x_38, 4);
 lean_ctor_release(x_38, 5);
 lean_ctor_release(x_38, 6);
 x_103 = x_38;
} else {
 lean_dec_ref(x_38);
 x_103 = lean_box(0);
}
if (lean_is_scalar(x_103)) {
 x_104 = lean_alloc_ctor(0, 7, 0);
} else {
 x_104 = x_103;
}
lean_ctor_set(x_104, 0, x_97);
lean_ctor_set(x_104, 1, x_98);
lean_ctor_set(x_104, 2, x_99);
lean_ctor_set(x_104, 3, x_100);
lean_ctor_set(x_104, 4, x_101);
lean_ctor_set(x_104, 5, x_1);
lean_ctor_set(x_104, 6, x_102);
if (lean_is_scalar(x_96)) {
 x_105 = lean_alloc_ctor(1, 2, 0);
} else {
 x_105 = x_96;
}
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_95);
x_106 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_106, 0, x_92);
lean_ctor_set(x_106, 1, x_93);
lean_ctor_set(x_106, 2, x_105);
lean_ctor_set(x_106, 3, x_94);
x_107 = l___private_Init_Lean_Elab_Command_3__setState(x_106, x_2, x_39);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_108 = lean_ctor_get(x_107, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_109 = x_107;
} else {
 lean_dec_ref(x_107);
 x_109 = lean_box(0);
}
x_110 = lean_box(0);
if (lean_is_scalar(x_109)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_109;
}
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_108);
return x_111;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_112 = lean_ctor_get(x_107, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_107, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_114 = x_107;
} else {
 lean_dec_ref(x_107);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(1, 2, 0);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_113);
return x_115;
}
}
}
}
else
{
uint8_t x_116; 
lean_dec(x_2);
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
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabAxiom___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = l___private_Init_Lean_Elab_Command_2__getState(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; uint8_t x_8; 
lean_dec(x_1);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_5, 2);
lean_dec(x_9);
x_10 = l_Lean_Elab_Command_modifyScope___closed__1;
x_11 = l_unreachable_x21___rarg(x_10);
lean_ctor_set(x_5, 2, x_11);
x_12 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_7);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
x_15 = lean_box(0);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_12);
if (x_19 == 0)
{
return x_12;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_12, 0);
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_12);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_23 = lean_ctor_get(x_5, 0);
x_24 = lean_ctor_get(x_5, 1);
x_25 = lean_ctor_get(x_5, 3);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_5);
x_26 = l_Lean_Elab_Command_modifyScope___closed__1;
x_27 = l_unreachable_x21___rarg(x_26);
x_28 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_24);
lean_ctor_set(x_28, 2, x_27);
lean_ctor_set(x_28, 3, x_25);
x_29 = l___private_Init_Lean_Elab_Command_3__setState(x_28, x_2, x_7);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_31 = x_29;
} else {
 lean_dec_ref(x_29);
 x_31 = lean_box(0);
}
x_32 = lean_box(0);
if (lean_is_scalar(x_31)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_31;
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_29, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_36 = x_29;
} else {
 lean_dec_ref(x_29);
 x_36 = lean_box(0);
}
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(1, 2, 0);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_ctor_get(x_6, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_4, 1);
lean_inc(x_39);
lean_dec(x_4);
x_40 = !lean_is_exclusive(x_5);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_5, 2);
lean_dec(x_41);
x_42 = !lean_is_exclusive(x_6);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_6, 0);
lean_dec(x_43);
x_44 = !lean_is_exclusive(x_38);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_38, 5);
lean_dec(x_45);
lean_ctor_set(x_38, 5, x_1);
x_46 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_39);
if (lean_obj_tag(x_46) == 0)
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_46, 0);
lean_dec(x_48);
x_49 = lean_box(0);
lean_ctor_set(x_46, 0, x_49);
return x_46;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_46, 1);
lean_inc(x_50);
lean_dec(x_46);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
}
else
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_46);
if (x_53 == 0)
{
return x_46;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_46, 0);
x_55 = lean_ctor_get(x_46, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_46);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_57 = lean_ctor_get(x_38, 0);
x_58 = lean_ctor_get(x_38, 1);
x_59 = lean_ctor_get(x_38, 2);
x_60 = lean_ctor_get(x_38, 3);
x_61 = lean_ctor_get(x_38, 4);
x_62 = lean_ctor_get(x_38, 6);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_38);
x_63 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_63, 0, x_57);
lean_ctor_set(x_63, 1, x_58);
lean_ctor_set(x_63, 2, x_59);
lean_ctor_set(x_63, 3, x_60);
lean_ctor_set(x_63, 4, x_61);
lean_ctor_set(x_63, 5, x_1);
lean_ctor_set(x_63, 6, x_62);
lean_ctor_set(x_6, 0, x_63);
x_64 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_39);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_66 = x_64;
} else {
 lean_dec_ref(x_64);
 x_66 = lean_box(0);
}
x_67 = lean_box(0);
if (lean_is_scalar(x_66)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_66;
}
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_65);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_ctor_get(x_64, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_64, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_71 = x_64;
} else {
 lean_dec_ref(x_64);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(1, 2, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_73 = lean_ctor_get(x_6, 1);
lean_inc(x_73);
lean_dec(x_6);
x_74 = lean_ctor_get(x_38, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_38, 1);
lean_inc(x_75);
x_76 = lean_ctor_get(x_38, 2);
lean_inc(x_76);
x_77 = lean_ctor_get(x_38, 3);
lean_inc(x_77);
x_78 = lean_ctor_get(x_38, 4);
lean_inc(x_78);
x_79 = lean_ctor_get(x_38, 6);
lean_inc(x_79);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 lean_ctor_release(x_38, 2);
 lean_ctor_release(x_38, 3);
 lean_ctor_release(x_38, 4);
 lean_ctor_release(x_38, 5);
 lean_ctor_release(x_38, 6);
 x_80 = x_38;
} else {
 lean_dec_ref(x_38);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(0, 7, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_74);
lean_ctor_set(x_81, 1, x_75);
lean_ctor_set(x_81, 2, x_76);
lean_ctor_set(x_81, 3, x_77);
lean_ctor_set(x_81, 4, x_78);
lean_ctor_set(x_81, 5, x_1);
lean_ctor_set(x_81, 6, x_79);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_73);
lean_ctor_set(x_5, 2, x_82);
x_83 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_39);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_85 = x_83;
} else {
 lean_dec_ref(x_83);
 x_85 = lean_box(0);
}
x_86 = lean_box(0);
if (lean_is_scalar(x_85)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_85;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_84);
return x_87;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = lean_ctor_get(x_83, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_83, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_90 = x_83;
} else {
 lean_dec_ref(x_83);
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
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_92 = lean_ctor_get(x_5, 0);
x_93 = lean_ctor_get(x_5, 1);
x_94 = lean_ctor_get(x_5, 3);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_5);
x_95 = lean_ctor_get(x_6, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_96 = x_6;
} else {
 lean_dec_ref(x_6);
 x_96 = lean_box(0);
}
x_97 = lean_ctor_get(x_38, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_38, 1);
lean_inc(x_98);
x_99 = lean_ctor_get(x_38, 2);
lean_inc(x_99);
x_100 = lean_ctor_get(x_38, 3);
lean_inc(x_100);
x_101 = lean_ctor_get(x_38, 4);
lean_inc(x_101);
x_102 = lean_ctor_get(x_38, 6);
lean_inc(x_102);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 lean_ctor_release(x_38, 2);
 lean_ctor_release(x_38, 3);
 lean_ctor_release(x_38, 4);
 lean_ctor_release(x_38, 5);
 lean_ctor_release(x_38, 6);
 x_103 = x_38;
} else {
 lean_dec_ref(x_38);
 x_103 = lean_box(0);
}
if (lean_is_scalar(x_103)) {
 x_104 = lean_alloc_ctor(0, 7, 0);
} else {
 x_104 = x_103;
}
lean_ctor_set(x_104, 0, x_97);
lean_ctor_set(x_104, 1, x_98);
lean_ctor_set(x_104, 2, x_99);
lean_ctor_set(x_104, 3, x_100);
lean_ctor_set(x_104, 4, x_101);
lean_ctor_set(x_104, 5, x_1);
lean_ctor_set(x_104, 6, x_102);
if (lean_is_scalar(x_96)) {
 x_105 = lean_alloc_ctor(1, 2, 0);
} else {
 x_105 = x_96;
}
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_95);
x_106 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_106, 0, x_92);
lean_ctor_set(x_106, 1, x_93);
lean_ctor_set(x_106, 2, x_105);
lean_ctor_set(x_106, 3, x_94);
x_107 = l___private_Init_Lean_Elab_Command_3__setState(x_106, x_2, x_39);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_108 = lean_ctor_get(x_107, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_109 = x_107;
} else {
 lean_dec_ref(x_107);
 x_109 = lean_box(0);
}
x_110 = lean_box(0);
if (lean_is_scalar(x_109)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_109;
}
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_108);
return x_111;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_112 = lean_ctor_get(x_107, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_107, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_114 = x_107;
} else {
 lean_dec_ref(x_107);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(1, 2, 0);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_113);
return x_115;
}
}
}
}
else
{
uint8_t x_116; 
lean_dec(x_2);
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
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabAxiom___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = l___private_Init_Lean_Elab_Command_2__getState(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; uint8_t x_8; 
lean_dec(x_1);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_5, 2);
lean_dec(x_9);
x_10 = l_Lean_Elab_Command_modifyScope___closed__1;
x_11 = l_unreachable_x21___rarg(x_10);
lean_ctor_set(x_5, 2, x_11);
x_12 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_7);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
x_15 = lean_box(0);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_12);
if (x_19 == 0)
{
return x_12;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_12, 0);
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_12);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_23 = lean_ctor_get(x_5, 0);
x_24 = lean_ctor_get(x_5, 1);
x_25 = lean_ctor_get(x_5, 3);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_5);
x_26 = l_Lean_Elab_Command_modifyScope___closed__1;
x_27 = l_unreachable_x21___rarg(x_26);
x_28 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_24);
lean_ctor_set(x_28, 2, x_27);
lean_ctor_set(x_28, 3, x_25);
x_29 = l___private_Init_Lean_Elab_Command_3__setState(x_28, x_2, x_7);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_31 = x_29;
} else {
 lean_dec_ref(x_29);
 x_31 = lean_box(0);
}
x_32 = lean_box(0);
if (lean_is_scalar(x_31)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_31;
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_29, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_36 = x_29;
} else {
 lean_dec_ref(x_29);
 x_36 = lean_box(0);
}
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(1, 2, 0);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_ctor_get(x_6, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_4, 1);
lean_inc(x_39);
lean_dec(x_4);
x_40 = !lean_is_exclusive(x_5);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_5, 2);
lean_dec(x_41);
x_42 = !lean_is_exclusive(x_6);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_6, 0);
lean_dec(x_43);
x_44 = !lean_is_exclusive(x_38);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_38, 5);
lean_dec(x_45);
lean_ctor_set(x_38, 5, x_1);
x_46 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_39);
if (lean_obj_tag(x_46) == 0)
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_46, 0);
lean_dec(x_48);
x_49 = lean_box(0);
lean_ctor_set(x_46, 0, x_49);
return x_46;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_46, 1);
lean_inc(x_50);
lean_dec(x_46);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
}
else
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_46);
if (x_53 == 0)
{
return x_46;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_46, 0);
x_55 = lean_ctor_get(x_46, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_46);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_57 = lean_ctor_get(x_38, 0);
x_58 = lean_ctor_get(x_38, 1);
x_59 = lean_ctor_get(x_38, 2);
x_60 = lean_ctor_get(x_38, 3);
x_61 = lean_ctor_get(x_38, 4);
x_62 = lean_ctor_get(x_38, 6);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_38);
x_63 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_63, 0, x_57);
lean_ctor_set(x_63, 1, x_58);
lean_ctor_set(x_63, 2, x_59);
lean_ctor_set(x_63, 3, x_60);
lean_ctor_set(x_63, 4, x_61);
lean_ctor_set(x_63, 5, x_1);
lean_ctor_set(x_63, 6, x_62);
lean_ctor_set(x_6, 0, x_63);
x_64 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_39);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_66 = x_64;
} else {
 lean_dec_ref(x_64);
 x_66 = lean_box(0);
}
x_67 = lean_box(0);
if (lean_is_scalar(x_66)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_66;
}
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_65);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_ctor_get(x_64, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_64, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_71 = x_64;
} else {
 lean_dec_ref(x_64);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(1, 2, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_73 = lean_ctor_get(x_6, 1);
lean_inc(x_73);
lean_dec(x_6);
x_74 = lean_ctor_get(x_38, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_38, 1);
lean_inc(x_75);
x_76 = lean_ctor_get(x_38, 2);
lean_inc(x_76);
x_77 = lean_ctor_get(x_38, 3);
lean_inc(x_77);
x_78 = lean_ctor_get(x_38, 4);
lean_inc(x_78);
x_79 = lean_ctor_get(x_38, 6);
lean_inc(x_79);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 lean_ctor_release(x_38, 2);
 lean_ctor_release(x_38, 3);
 lean_ctor_release(x_38, 4);
 lean_ctor_release(x_38, 5);
 lean_ctor_release(x_38, 6);
 x_80 = x_38;
} else {
 lean_dec_ref(x_38);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(0, 7, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_74);
lean_ctor_set(x_81, 1, x_75);
lean_ctor_set(x_81, 2, x_76);
lean_ctor_set(x_81, 3, x_77);
lean_ctor_set(x_81, 4, x_78);
lean_ctor_set(x_81, 5, x_1);
lean_ctor_set(x_81, 6, x_79);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_73);
lean_ctor_set(x_5, 2, x_82);
x_83 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_39);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_85 = x_83;
} else {
 lean_dec_ref(x_83);
 x_85 = lean_box(0);
}
x_86 = lean_box(0);
if (lean_is_scalar(x_85)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_85;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_84);
return x_87;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = lean_ctor_get(x_83, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_83, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_90 = x_83;
} else {
 lean_dec_ref(x_83);
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
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_92 = lean_ctor_get(x_5, 0);
x_93 = lean_ctor_get(x_5, 1);
x_94 = lean_ctor_get(x_5, 3);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_5);
x_95 = lean_ctor_get(x_6, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_96 = x_6;
} else {
 lean_dec_ref(x_6);
 x_96 = lean_box(0);
}
x_97 = lean_ctor_get(x_38, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_38, 1);
lean_inc(x_98);
x_99 = lean_ctor_get(x_38, 2);
lean_inc(x_99);
x_100 = lean_ctor_get(x_38, 3);
lean_inc(x_100);
x_101 = lean_ctor_get(x_38, 4);
lean_inc(x_101);
x_102 = lean_ctor_get(x_38, 6);
lean_inc(x_102);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 lean_ctor_release(x_38, 2);
 lean_ctor_release(x_38, 3);
 lean_ctor_release(x_38, 4);
 lean_ctor_release(x_38, 5);
 lean_ctor_release(x_38, 6);
 x_103 = x_38;
} else {
 lean_dec_ref(x_38);
 x_103 = lean_box(0);
}
if (lean_is_scalar(x_103)) {
 x_104 = lean_alloc_ctor(0, 7, 0);
} else {
 x_104 = x_103;
}
lean_ctor_set(x_104, 0, x_97);
lean_ctor_set(x_104, 1, x_98);
lean_ctor_set(x_104, 2, x_99);
lean_ctor_set(x_104, 3, x_100);
lean_ctor_set(x_104, 4, x_101);
lean_ctor_set(x_104, 5, x_1);
lean_ctor_set(x_104, 6, x_102);
if (lean_is_scalar(x_96)) {
 x_105 = lean_alloc_ctor(1, 2, 0);
} else {
 x_105 = x_96;
}
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_95);
x_106 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_106, 0, x_92);
lean_ctor_set(x_106, 1, x_93);
lean_ctor_set(x_106, 2, x_105);
lean_ctor_set(x_106, 3, x_94);
x_107 = l___private_Init_Lean_Elab_Command_3__setState(x_106, x_2, x_39);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_108 = lean_ctor_get(x_107, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_109 = x_107;
} else {
 lean_dec_ref(x_107);
 x_109 = lean_box(0);
}
x_110 = lean_box(0);
if (lean_is_scalar(x_109)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_109;
}
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_108);
return x_111;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_112 = lean_ctor_get(x_107, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_107, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_114 = x_107;
} else {
 lean_dec_ref(x_107);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(1, 2, 0);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_113);
return x_115;
}
}
}
}
else
{
uint8_t x_116; 
lean_dec(x_2);
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
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_elabAxiom___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_3, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_3);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_array_fget(x_2, x_3);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_3, x_11);
lean_dec(x_3);
x_13 = l_Lean_Syntax_getId(x_10);
x_14 = l_List_elem___main___at_Lean_Parser_addLeadingParser___spec__4(x_13, x_4);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_10);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_4);
x_3 = x_12;
x_4 = x_15;
goto _start;
}
else
{
lean_object* x_17; uint8_t x_18; 
lean_dec(x_12);
lean_dec(x_4);
x_17 = l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg(x_10, x_13, x_5, x_6);
lean_dec(x_10);
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
}
}
}
lean_object* l_Lean_Elab_Command_elabAxiom___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_1);
x_9 = l_Lean_Elab_Term_elabType(x_1, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = 0;
x_13 = lean_box(0);
lean_inc(x_7);
x_14 = l___private_Init_Lean_Elab_Term_19__synthesizeSyntheticMVarsAux___main(x_12, x_13, x_7, x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
lean_inc(x_7);
x_16 = l_Lean_Elab_Term_instantiateMVars(x_1, x_10, x_7, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_7);
x_19 = l_Lean_Elab_Term_mkForall(x_1, x_6, x_17, x_7, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_7);
x_22 = l_Lean_Elab_Term_mkForallUsedOnly(x_1, x_2, x_20, x_7, x_21);
lean_dec(x_1);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_Elab_Term_levelMVarToParam(x_25, x_7, x_24);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; 
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
x_29 = l_Lean_collectLevelParams(x_28);
x_30 = l_Lean_Elab_Command_sortDeclLevelParams(x_3, x_29);
x_31 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_31, 0, x_4);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_31, 2, x_28);
x_32 = lean_ctor_get_uint8(x_5, sizeof(void*)*2 + 3);
x_33 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set_uint8(x_33, sizeof(void*)*1, x_32);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_26, 0, x_34);
return x_26;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_35 = lean_ctor_get(x_26, 0);
x_36 = lean_ctor_get(x_26, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_26);
lean_inc(x_35);
x_37 = l_Lean_collectLevelParams(x_35);
x_38 = l_Lean_Elab_Command_sortDeclLevelParams(x_3, x_37);
x_39 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_39, 0, x_4);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set(x_39, 2, x_35);
x_40 = lean_ctor_get_uint8(x_5, sizeof(void*)*2 + 3);
x_41 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set_uint8(x_41, sizeof(void*)*1, x_40);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_36);
return x_43;
}
}
else
{
uint8_t x_44; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_44 = !lean_is_exclusive(x_22);
if (x_44 == 0)
{
return x_22;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_22, 0);
x_46 = lean_ctor_get(x_22, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_22);
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
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_19);
if (x_48 == 0)
{
return x_19;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_19, 0);
x_50 = lean_ctor_get(x_19, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_19);
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
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_52 = !lean_is_exclusive(x_14);
if (x_52 == 0)
{
return x_14;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_14, 0);
x_54 = lean_ctor_get(x_14, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_14);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_9);
if (x_56 == 0)
{
return x_9;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_9, 0);
x_58 = lean_ctor_get(x_9, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_9);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
}
lean_object* l_Lean_Elab_Command_elabAxiom___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_Lean_Syntax_getArgs(x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabAxiom___lambda__1___boxed), 8, 5);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_6);
lean_closure_set(x_10, 2, x_3);
lean_closure_set(x_10, 3, x_4);
lean_closure_set(x_10, 4, x_5);
x_11 = l_Lean_Elab_Term_elabBinders___rarg(x_9, x_10, x_7, x_8);
lean_dec(x_9);
return x_11;
}
}
lean_object* l_Lean_Elab_Command_elabAxiom(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Lean_Syntax_getArg(x_2, x_5);
x_7 = lean_unsigned_to_nat(2u);
x_8 = l_Lean_Syntax_getArg(x_2, x_7);
x_9 = l_Lean_Elab_Command_expandDeclSig(x_8);
lean_dec(x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Lean_Syntax_getIdAt(x_6, x_12);
x_14 = l_Lean_Syntax_getArg(x_6, x_5);
lean_inc(x_3);
x_15 = l_Lean_Elab_Command_getLevelNames(x_3, x_4);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_201; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_201 = l_Lean_Syntax_isNone(x_14);
if (x_201 == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_202 = l_Lean_Syntax_getArg(x_14, x_5);
lean_dec(x_14);
x_203 = l_Lean_Syntax_getArgs(x_202);
lean_dec(x_202);
x_204 = l_Array_empty___closed__1;
x_205 = l_Lean_Syntax_foldArgsAuxM___main___at_Lean_Syntax_foldSepRevArgsM___spec__1(x_7, x_203, x_12, x_204);
lean_dec(x_203);
lean_inc(x_16);
x_206 = l_Array_iterateMAux___main___at_Lean_Elab_Command_elabAxiom___spec__5(x_2, x_205, x_12, x_16, x_3, x_17);
lean_dec(x_205);
if (lean_obj_tag(x_206) == 0)
{
lean_object* x_207; lean_object* x_208; 
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_206, 1);
lean_inc(x_208);
lean_dec(x_206);
x_18 = x_207;
x_19 = x_208;
goto block_200;
}
else
{
uint8_t x_209; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_209 = !lean_is_exclusive(x_206);
if (x_209 == 0)
{
return x_206;
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_210 = lean_ctor_get(x_206, 0);
x_211 = lean_ctor_get(x_206, 1);
lean_inc(x_211);
lean_inc(x_210);
lean_dec(x_206);
x_212 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_212, 0, x_210);
lean_ctor_set(x_212, 1, x_211);
return x_212;
}
}
}
else
{
lean_dec(x_14);
lean_inc(x_16);
x_18 = x_16;
x_19 = x_17;
goto block_200;
}
block_200:
{
if (lean_obj_tag(x_13) == 1)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_13, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_dec(x_13);
x_22 = l_Lean_Parser_Command_namespace___elambda__1___closed__1;
x_23 = 1;
lean_inc(x_3);
lean_inc(x_20);
x_24 = l___private_Init_Lean_Elab_Command_10__addScopes___main(x_6, x_22, x_23, x_20, x_3, x_19);
lean_dec(x_6);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
lean_inc(x_3);
x_26 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabAxiom___spec__1(x_18, x_3, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_42; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_box(0);
x_29 = lean_name_mk_string(x_28, x_21);
lean_inc(x_3);
x_42 = l_Lean_Elab_Command_mkDeclName(x_1, x_29, x_3, x_27);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_112; lean_object* x_113; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_ctor_get(x_1, 1);
lean_inc(x_45);
x_112 = 2;
lean_inc(x_3);
lean_inc(x_43);
x_113 = l_Array_forMAux___main___at_Lean_Elab_Command_applyAttributes___spec__1(x_2, x_43, x_112, x_45, x_12, x_3, x_44);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; 
x_114 = lean_ctor_get(x_113, 1);
lean_inc(x_114);
lean_dec(x_113);
lean_inc(x_3);
x_115 = l_Lean_Elab_Command_getLevelNames(x_3, x_114);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
lean_dec(x_115);
lean_inc(x_43);
x_118 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabAxiom___lambda__2___boxed), 8, 5);
lean_closure_set(x_118, 0, x_10);
lean_closure_set(x_118, 1, x_11);
lean_closure_set(x_118, 2, x_116);
lean_closure_set(x_118, 3, x_43);
lean_closure_set(x_118, 4, x_1);
lean_inc(x_3);
x_119 = l___private_Init_Lean_Elab_Command_2__getState(x_3, x_117);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec(x_119);
x_122 = l___private_Init_Lean_Elab_Command_7__getVarDecls(x_120);
x_123 = l___private_Init_Lean_Elab_Command_5__mkTermContext(x_3, x_120);
x_124 = l___private_Init_Lean_Elab_Command_6__mkTermState(x_120);
lean_dec(x_120);
x_125 = l_Lean_Elab_Term_elabBinders___rarg(x_122, x_118, x_123, x_124);
lean_dec(x_122);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
lean_dec(x_125);
lean_inc(x_3);
x_128 = l___private_Init_Lean_Elab_Command_2__getState(x_3, x_121);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; 
x_129 = lean_ctor_get(x_127, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_128, 1);
lean_inc(x_131);
lean_dec(x_128);
x_132 = lean_ctor_get(x_129, 0);
lean_inc(x_132);
lean_dec(x_129);
x_133 = lean_ctor_get(x_127, 2);
lean_inc(x_133);
lean_dec(x_127);
x_134 = !lean_is_exclusive(x_130);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_135 = lean_ctor_get(x_130, 1);
lean_dec(x_135);
x_136 = lean_ctor_get(x_130, 0);
lean_dec(x_136);
lean_ctor_set(x_130, 1, x_133);
lean_ctor_set(x_130, 0, x_132);
lean_inc(x_3);
x_137 = l___private_Init_Lean_Elab_Command_3__setState(x_130, x_3, x_131);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; 
x_138 = lean_ctor_get(x_137, 1);
lean_inc(x_138);
lean_dec(x_137);
x_46 = x_126;
x_47 = x_138;
goto block_111;
}
else
{
lean_object* x_139; lean_object* x_140; 
lean_dec(x_126);
lean_dec(x_45);
lean_dec(x_43);
lean_dec(x_20);
x_139 = lean_ctor_get(x_137, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_137, 1);
lean_inc(x_140);
lean_dec(x_137);
x_30 = x_139;
x_31 = x_140;
goto block_41;
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_141 = lean_ctor_get(x_130, 2);
x_142 = lean_ctor_get(x_130, 3);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_130);
x_143 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_143, 0, x_132);
lean_ctor_set(x_143, 1, x_133);
lean_ctor_set(x_143, 2, x_141);
lean_ctor_set(x_143, 3, x_142);
lean_inc(x_3);
x_144 = l___private_Init_Lean_Elab_Command_3__setState(x_143, x_3, x_131);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; 
x_145 = lean_ctor_get(x_144, 1);
lean_inc(x_145);
lean_dec(x_144);
x_46 = x_126;
x_47 = x_145;
goto block_111;
}
else
{
lean_object* x_146; lean_object* x_147; 
lean_dec(x_126);
lean_dec(x_45);
lean_dec(x_43);
lean_dec(x_20);
x_146 = lean_ctor_get(x_144, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_144, 1);
lean_inc(x_147);
lean_dec(x_144);
x_30 = x_146;
x_31 = x_147;
goto block_41;
}
}
}
else
{
lean_object* x_148; lean_object* x_149; 
lean_dec(x_127);
lean_dec(x_126);
lean_dec(x_45);
lean_dec(x_43);
lean_dec(x_20);
x_148 = lean_ctor_get(x_128, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_128, 1);
lean_inc(x_149);
lean_dec(x_128);
x_30 = x_148;
x_31 = x_149;
goto block_41;
}
}
else
{
lean_object* x_150; 
x_150 = lean_ctor_get(x_125, 0);
lean_inc(x_150);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec(x_45);
lean_dec(x_43);
lean_dec(x_20);
x_151 = lean_ctor_get(x_125, 1);
lean_inc(x_151);
lean_dec(x_125);
x_152 = lean_ctor_get(x_150, 0);
lean_inc(x_152);
lean_dec(x_150);
lean_inc(x_3);
x_153 = l___private_Init_Lean_Elab_Command_2__getState(x_3, x_121);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; 
x_154 = lean_ctor_get(x_151, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_153, 1);
lean_inc(x_156);
lean_dec(x_153);
x_157 = lean_ctor_get(x_154, 0);
lean_inc(x_157);
lean_dec(x_154);
x_158 = lean_ctor_get(x_151, 2);
lean_inc(x_158);
lean_dec(x_151);
x_159 = !lean_is_exclusive(x_155);
if (x_159 == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_160 = lean_ctor_get(x_155, 1);
lean_dec(x_160);
x_161 = lean_ctor_get(x_155, 0);
lean_dec(x_161);
lean_ctor_set(x_155, 1, x_158);
lean_ctor_set(x_155, 0, x_157);
lean_inc(x_3);
x_162 = l___private_Init_Lean_Elab_Command_3__setState(x_155, x_3, x_156);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; 
x_163 = lean_ctor_get(x_162, 1);
lean_inc(x_163);
lean_dec(x_162);
x_30 = x_152;
x_31 = x_163;
goto block_41;
}
else
{
lean_object* x_164; lean_object* x_165; 
lean_dec(x_152);
x_164 = lean_ctor_get(x_162, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_162, 1);
lean_inc(x_165);
lean_dec(x_162);
x_30 = x_164;
x_31 = x_165;
goto block_41;
}
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_166 = lean_ctor_get(x_155, 2);
x_167 = lean_ctor_get(x_155, 3);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_155);
x_168 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_168, 0, x_157);
lean_ctor_set(x_168, 1, x_158);
lean_ctor_set(x_168, 2, x_166);
lean_ctor_set(x_168, 3, x_167);
lean_inc(x_3);
x_169 = l___private_Init_Lean_Elab_Command_3__setState(x_168, x_3, x_156);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_170; 
x_170 = lean_ctor_get(x_169, 1);
lean_inc(x_170);
lean_dec(x_169);
x_30 = x_152;
x_31 = x_170;
goto block_41;
}
else
{
lean_object* x_171; lean_object* x_172; 
lean_dec(x_152);
x_171 = lean_ctor_get(x_169, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_169, 1);
lean_inc(x_172);
lean_dec(x_169);
x_30 = x_171;
x_31 = x_172;
goto block_41;
}
}
}
else
{
lean_object* x_173; lean_object* x_174; 
lean_dec(x_152);
lean_dec(x_151);
x_173 = lean_ctor_get(x_153, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_153, 1);
lean_inc(x_174);
lean_dec(x_153);
x_30 = x_173;
x_31 = x_174;
goto block_41;
}
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; 
lean_dec(x_125);
x_175 = l_Lean_Elab_Command_runTermElabM___rarg___closed__1;
x_176 = l_unreachable_x21___rarg(x_175);
lean_inc(x_3);
x_177 = lean_apply_2(x_176, x_3, x_121);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; lean_object* x_179; 
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_177, 1);
lean_inc(x_179);
lean_dec(x_177);
x_46 = x_178;
x_47 = x_179;
goto block_111;
}
else
{
lean_object* x_180; lean_object* x_181; 
lean_dec(x_45);
lean_dec(x_43);
lean_dec(x_20);
x_180 = lean_ctor_get(x_177, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_177, 1);
lean_inc(x_181);
lean_dec(x_177);
x_30 = x_180;
x_31 = x_181;
goto block_41;
}
}
}
}
else
{
lean_object* x_182; lean_object* x_183; 
lean_dec(x_118);
lean_dec(x_45);
lean_dec(x_43);
lean_dec(x_20);
x_182 = lean_ctor_get(x_119, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_119, 1);
lean_inc(x_183);
lean_dec(x_119);
x_30 = x_182;
x_31 = x_183;
goto block_41;
}
}
else
{
lean_object* x_184; lean_object* x_185; 
lean_dec(x_45);
lean_dec(x_43);
lean_dec(x_20);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_1);
x_184 = lean_ctor_get(x_115, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_115, 1);
lean_inc(x_185);
lean_dec(x_115);
x_30 = x_184;
x_31 = x_185;
goto block_41;
}
}
else
{
lean_object* x_186; lean_object* x_187; 
lean_dec(x_45);
lean_dec(x_43);
lean_dec(x_20);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_1);
x_186 = lean_ctor_get(x_113, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_113, 1);
lean_inc(x_187);
lean_dec(x_113);
x_30 = x_186;
x_31 = x_187;
goto block_41;
}
block_111:
{
lean_object* x_48; 
lean_inc(x_3);
x_48 = l_Lean_Elab_Command_addDecl(x_2, x_46, x_3, x_47);
lean_dec(x_46);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; uint8_t x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
x_50 = 0;
lean_inc(x_3);
lean_inc(x_43);
x_51 = l_Array_forMAux___main___at_Lean_Elab_Command_applyAttributes___spec__1(x_2, x_43, x_50, x_45, x_12, x_3, x_49);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; uint8_t x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec(x_51);
x_53 = 1;
lean_inc(x_3);
x_54 = l_Array_forMAux___main___at_Lean_Elab_Command_applyAttributes___spec__1(x_2, x_43, x_53, x_45, x_12, x_3, x_52);
lean_dec(x_45);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
lean_inc(x_3);
lean_inc(x_16);
x_57 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabAxiom___spec__3(x_16, x_3, x_56);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_16);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
lean_inc(x_3);
x_59 = l___private_Init_Lean_Elab_Command_2__getState(x_3, x_58);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = !lean_is_exclusive(x_60);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_ctor_get(x_60, 2);
x_64 = l_Lean_Name_getNumParts___main(x_20);
lean_dec(x_20);
x_65 = l_List_drop___main___rarg(x_64, x_63);
lean_dec(x_63);
lean_ctor_set(x_60, 2, x_65);
x_66 = l___private_Init_Lean_Elab_Command_3__setState(x_60, x_3, x_61);
if (lean_obj_tag(x_66) == 0)
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_66);
if (x_67 == 0)
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_66, 0);
lean_dec(x_68);
lean_ctor_set(x_66, 0, x_55);
return x_66;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_66, 1);
lean_inc(x_69);
lean_dec(x_66);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_55);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
else
{
uint8_t x_71; 
lean_dec(x_55);
x_71 = !lean_is_exclusive(x_66);
if (x_71 == 0)
{
return x_66;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_66, 0);
x_73 = lean_ctor_get(x_66, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_66);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_75 = lean_ctor_get(x_60, 0);
x_76 = lean_ctor_get(x_60, 1);
x_77 = lean_ctor_get(x_60, 2);
x_78 = lean_ctor_get(x_60, 3);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_60);
x_79 = l_Lean_Name_getNumParts___main(x_20);
lean_dec(x_20);
x_80 = l_List_drop___main___rarg(x_79, x_77);
lean_dec(x_77);
x_81 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_81, 0, x_75);
lean_ctor_set(x_81, 1, x_76);
lean_ctor_set(x_81, 2, x_80);
lean_ctor_set(x_81, 3, x_78);
x_82 = l___private_Init_Lean_Elab_Command_3__setState(x_81, x_3, x_61);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_84 = x_82;
} else {
 lean_dec_ref(x_82);
 x_84 = lean_box(0);
}
if (lean_is_scalar(x_84)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_84;
}
lean_ctor_set(x_85, 0, x_55);
lean_ctor_set(x_85, 1, x_83);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_55);
x_86 = lean_ctor_get(x_82, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_82, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_88 = x_82;
} else {
 lean_dec_ref(x_82);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_88)) {
 x_89 = lean_alloc_ctor(1, 2, 0);
} else {
 x_89 = x_88;
}
lean_ctor_set(x_89, 0, x_86);
lean_ctor_set(x_89, 1, x_87);
return x_89;
}
}
}
else
{
uint8_t x_90; 
lean_dec(x_55);
lean_dec(x_20);
lean_dec(x_3);
x_90 = !lean_is_exclusive(x_59);
if (x_90 == 0)
{
return x_59;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_59, 0);
x_92 = lean_ctor_get(x_59, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_59);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_55);
lean_dec(x_20);
x_94 = lean_ctor_get(x_57, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_57, 1);
lean_inc(x_95);
lean_dec(x_57);
x_96 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabAxiom___spec__4(x_16, x_3, x_95);
if (lean_obj_tag(x_96) == 0)
{
uint8_t x_97; 
x_97 = !lean_is_exclusive(x_96);
if (x_97 == 0)
{
lean_object* x_98; 
x_98 = lean_ctor_get(x_96, 0);
lean_dec(x_98);
lean_ctor_set_tag(x_96, 1);
lean_ctor_set(x_96, 0, x_94);
return x_96;
}
else
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_ctor_get(x_96, 1);
lean_inc(x_99);
lean_dec(x_96);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_94);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
else
{
uint8_t x_101; 
lean_dec(x_94);
x_101 = !lean_is_exclusive(x_96);
if (x_101 == 0)
{
return x_96;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_96, 0);
x_103 = lean_ctor_get(x_96, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_96);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
}
}
else
{
lean_object* x_105; lean_object* x_106; 
lean_dec(x_20);
x_105 = lean_ctor_get(x_54, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_54, 1);
lean_inc(x_106);
lean_dec(x_54);
x_30 = x_105;
x_31 = x_106;
goto block_41;
}
}
else
{
lean_object* x_107; lean_object* x_108; 
lean_dec(x_45);
lean_dec(x_43);
lean_dec(x_20);
x_107 = lean_ctor_get(x_51, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_51, 1);
lean_inc(x_108);
lean_dec(x_51);
x_30 = x_107;
x_31 = x_108;
goto block_41;
}
}
else
{
lean_object* x_109; lean_object* x_110; 
lean_dec(x_45);
lean_dec(x_43);
lean_dec(x_20);
x_109 = lean_ctor_get(x_48, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_48, 1);
lean_inc(x_110);
lean_dec(x_48);
x_30 = x_109;
x_31 = x_110;
goto block_41;
}
}
}
else
{
lean_object* x_188; lean_object* x_189; 
lean_dec(x_20);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_1);
x_188 = lean_ctor_get(x_42, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_42, 1);
lean_inc(x_189);
lean_dec(x_42);
x_30 = x_188;
x_31 = x_189;
goto block_41;
}
block_41:
{
lean_object* x_32; 
x_32 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabAxiom___spec__2(x_16, x_3, x_31);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_32, 0);
lean_dec(x_34);
lean_ctor_set_tag(x_32, 1);
lean_ctor_set(x_32, 0, x_30);
return x_32;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_30);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
else
{
uint8_t x_37; 
lean_dec(x_30);
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
}
else
{
uint8_t x_190; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_1);
x_190 = !lean_is_exclusive(x_26);
if (x_190 == 0)
{
return x_26;
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_191 = lean_ctor_get(x_26, 0);
x_192 = lean_ctor_get(x_26, 1);
lean_inc(x_192);
lean_inc(x_191);
lean_dec(x_26);
x_193 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_193, 0, x_191);
lean_ctor_set(x_193, 1, x_192);
return x_193;
}
}
}
else
{
uint8_t x_194; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_1);
x_194 = !lean_is_exclusive(x_24);
if (x_194 == 0)
{
return x_24;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_195 = lean_ctor_get(x_24, 0);
x_196 = lean_ctor_get(x_24, 1);
lean_inc(x_196);
lean_inc(x_195);
lean_dec(x_24);
x_197 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_197, 0, x_195);
lean_ctor_set(x_197, 1, x_196);
return x_197;
}
}
}
else
{
lean_object* x_198; lean_object* x_199; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_1);
x_198 = l_Lean_Elab_Command_withDeclId___closed__3;
x_199 = l_Lean_Elab_throwError___at_Lean_Elab_Command_elabCommand___spec__1(x_6, x_198, x_3, x_19);
lean_dec(x_3);
lean_dec(x_6);
return x_199;
}
}
}
else
{
uint8_t x_213; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_213 = !lean_is_exclusive(x_15);
if (x_213 == 0)
{
return x_15;
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_214 = lean_ctor_get(x_15, 0);
x_215 = lean_ctor_get(x_15, 1);
lean_inc(x_215);
lean_inc(x_214);
lean_dec(x_15);
x_216 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_216, 0, x_214);
lean_ctor_set(x_216, 1, x_215);
return x_216;
}
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_elabAxiom___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_iterateMAux___main___at_Lean_Elab_Command_elabAxiom___spec__5(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Elab_Command_elabAxiom___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Command_elabAxiom___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
return x_9;
}
}
lean_object* l_Lean_Elab_Command_elabAxiom___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Command_elabAxiom___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Lean_Elab_Command_elabAxiom___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabAxiom(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_elabInductive___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_elabInductive(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabInductive___rarg), 1, 0);
return x_4;
}
}
lean_object* l_Lean_Elab_Command_elabInductive___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_elabInductive(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_Command_elabClassInductive___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_elabClassInductive(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabClassInductive___rarg), 1, 0);
return x_4;
}
}
lean_object* l_Lean_Elab_Command_elabClassInductive___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_elabClassInductive(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_Command_elabStructure___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_elabStructure(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabStructure___rarg), 1, 0);
return x_4;
}
}
lean_object* l_Lean_Elab_Command_elabStructure___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_elabStructure(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l_Lean_Elab_Command_elabDeclaration___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltinParser_Lean_Parser_Command_antiquot___closed__2;
x_2 = l_Lean_Meta_registerInstanceAttr___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_elabDeclaration___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected declaration");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_elabDeclaration___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabDeclaration___closed__2;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_elabDeclaration___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabDeclaration___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_elabDeclaration(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_Lean_stxInh;
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_get(x_5, x_4, x_6);
lean_inc(x_2);
x_8 = l_Lean_Elab_Command_elabModifiers(x_7, x_2, x_3);
lean_dec(x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_array_get(x_5, x_4, x_12);
lean_inc(x_13);
x_14 = l_Lean_Syntax_getKind(x_13);
x_15 = l_Lean_Parser_Command_abbrev___elambda__1___closed__2;
x_16 = lean_name_eq(x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Lean_Parser_Command_def___elambda__1___closed__2;
x_18 = lean_name_eq(x_14, x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = l_Lean_Parser_Command_theorem___elambda__1___closed__2;
x_20 = lean_name_eq(x_14, x_19);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = l_Lean_Parser_Command_constant___elambda__1___closed__2;
x_22 = lean_name_eq(x_14, x_21);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = l_Lean_Elab_Command_elabDeclaration___closed__1;
x_24 = lean_name_eq(x_14, x_23);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = l_Lean_Parser_Command_axiom___elambda__1___closed__2;
x_26 = lean_name_eq(x_14, x_25);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = l_Lean_Parser_Command_example___elambda__1___closed__2;
x_28 = lean_name_eq(x_14, x_27);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
lean_dec(x_13);
lean_dec(x_10);
x_29 = l_Lean_Parser_Command_inductive___elambda__1___closed__2;
x_30 = lean_name_eq(x_14, x_29);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = l_Lean_Parser_Command_classInductive___elambda__1___closed__2;
x_32 = lean_name_eq(x_14, x_31);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = l_Lean_Parser_Command_structure___elambda__1___closed__2;
x_34 = lean_name_eq(x_14, x_33);
lean_dec(x_14);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
lean_free_object(x_8);
x_35 = l_Lean_Elab_Command_elabDeclaration___closed__4;
x_36 = l_Lean_Elab_throwError___at_Lean_Elab_Command_elabCommand___spec__1(x_1, x_35, x_2, x_11);
lean_dec(x_2);
return x_36;
}
else
{
lean_object* x_37; 
lean_dec(x_2);
x_37 = lean_box(0);
lean_ctor_set(x_8, 0, x_37);
return x_8;
}
}
else
{
lean_object* x_38; 
lean_dec(x_14);
lean_dec(x_2);
x_38 = lean_box(0);
lean_ctor_set(x_8, 0, x_38);
return x_8;
}
}
else
{
lean_object* x_39; 
lean_dec(x_14);
lean_dec(x_2);
x_39 = lean_box(0);
lean_ctor_set(x_8, 0, x_39);
return x_8;
}
}
else
{
lean_object* x_40; 
lean_dec(x_14);
lean_free_object(x_8);
x_40 = l_Lean_Elab_Command_elabExample(x_10, x_13, x_2, x_11);
return x_40;
}
}
else
{
lean_object* x_41; 
lean_dec(x_14);
lean_free_object(x_8);
x_41 = l_Lean_Elab_Command_elabAxiom(x_10, x_13, x_2, x_11);
lean_dec(x_13);
return x_41;
}
}
else
{
lean_object* x_42; 
lean_dec(x_14);
lean_free_object(x_8);
x_42 = l_Lean_Elab_Command_elabInstance(x_10, x_13, x_2, x_11);
return x_42;
}
}
else
{
lean_object* x_43; 
lean_dec(x_14);
lean_free_object(x_8);
x_43 = l_Lean_Elab_Command_elabConstant(x_10, x_13, x_2, x_11);
return x_43;
}
}
else
{
lean_object* x_44; 
lean_dec(x_14);
lean_free_object(x_8);
x_44 = l_Lean_Elab_Command_elabTheorem(x_10, x_13, x_2, x_11);
return x_44;
}
}
else
{
lean_object* x_45; 
lean_dec(x_14);
lean_free_object(x_8);
x_45 = l_Lean_Elab_Command_elabDef(x_10, x_13, x_2, x_11);
return x_45;
}
}
else
{
lean_object* x_46; 
lean_dec(x_14);
lean_free_object(x_8);
x_46 = l_Lean_Elab_Command_elabAbbrev(x_10, x_13, x_2, x_11);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_47 = lean_ctor_get(x_8, 0);
x_48 = lean_ctor_get(x_8, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_8);
x_49 = lean_unsigned_to_nat(1u);
x_50 = lean_array_get(x_5, x_4, x_49);
lean_inc(x_50);
x_51 = l_Lean_Syntax_getKind(x_50);
x_52 = l_Lean_Parser_Command_abbrev___elambda__1___closed__2;
x_53 = lean_name_eq(x_51, x_52);
if (x_53 == 0)
{
lean_object* x_54; uint8_t x_55; 
x_54 = l_Lean_Parser_Command_def___elambda__1___closed__2;
x_55 = lean_name_eq(x_51, x_54);
if (x_55 == 0)
{
lean_object* x_56; uint8_t x_57; 
x_56 = l_Lean_Parser_Command_theorem___elambda__1___closed__2;
x_57 = lean_name_eq(x_51, x_56);
if (x_57 == 0)
{
lean_object* x_58; uint8_t x_59; 
x_58 = l_Lean_Parser_Command_constant___elambda__1___closed__2;
x_59 = lean_name_eq(x_51, x_58);
if (x_59 == 0)
{
lean_object* x_60; uint8_t x_61; 
x_60 = l_Lean_Elab_Command_elabDeclaration___closed__1;
x_61 = lean_name_eq(x_51, x_60);
if (x_61 == 0)
{
lean_object* x_62; uint8_t x_63; 
x_62 = l_Lean_Parser_Command_axiom___elambda__1___closed__2;
x_63 = lean_name_eq(x_51, x_62);
if (x_63 == 0)
{
lean_object* x_64; uint8_t x_65; 
x_64 = l_Lean_Parser_Command_example___elambda__1___closed__2;
x_65 = lean_name_eq(x_51, x_64);
if (x_65 == 0)
{
lean_object* x_66; uint8_t x_67; 
lean_dec(x_50);
lean_dec(x_47);
x_66 = l_Lean_Parser_Command_inductive___elambda__1___closed__2;
x_67 = lean_name_eq(x_51, x_66);
if (x_67 == 0)
{
lean_object* x_68; uint8_t x_69; 
x_68 = l_Lean_Parser_Command_classInductive___elambda__1___closed__2;
x_69 = lean_name_eq(x_51, x_68);
if (x_69 == 0)
{
lean_object* x_70; uint8_t x_71; 
x_70 = l_Lean_Parser_Command_structure___elambda__1___closed__2;
x_71 = lean_name_eq(x_51, x_70);
lean_dec(x_51);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = l_Lean_Elab_Command_elabDeclaration___closed__4;
x_73 = l_Lean_Elab_throwError___at_Lean_Elab_Command_elabCommand___spec__1(x_1, x_72, x_2, x_48);
lean_dec(x_2);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; 
lean_dec(x_2);
x_74 = lean_box(0);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_48);
return x_75;
}
}
else
{
lean_object* x_76; lean_object* x_77; 
lean_dec(x_51);
lean_dec(x_2);
x_76 = lean_box(0);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_48);
return x_77;
}
}
else
{
lean_object* x_78; lean_object* x_79; 
lean_dec(x_51);
lean_dec(x_2);
x_78 = lean_box(0);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_48);
return x_79;
}
}
else
{
lean_object* x_80; 
lean_dec(x_51);
x_80 = l_Lean_Elab_Command_elabExample(x_47, x_50, x_2, x_48);
return x_80;
}
}
else
{
lean_object* x_81; 
lean_dec(x_51);
x_81 = l_Lean_Elab_Command_elabAxiom(x_47, x_50, x_2, x_48);
lean_dec(x_50);
return x_81;
}
}
else
{
lean_object* x_82; 
lean_dec(x_51);
x_82 = l_Lean_Elab_Command_elabInstance(x_47, x_50, x_2, x_48);
return x_82;
}
}
else
{
lean_object* x_83; 
lean_dec(x_51);
x_83 = l_Lean_Elab_Command_elabConstant(x_47, x_50, x_2, x_48);
return x_83;
}
}
else
{
lean_object* x_84; 
lean_dec(x_51);
x_84 = l_Lean_Elab_Command_elabTheorem(x_47, x_50, x_2, x_48);
return x_84;
}
}
else
{
lean_object* x_85; 
lean_dec(x_51);
x_85 = l_Lean_Elab_Command_elabDef(x_47, x_50, x_2, x_48);
return x_85;
}
}
else
{
lean_object* x_86; 
lean_dec(x_51);
x_86 = l_Lean_Elab_Command_elabAbbrev(x_47, x_50, x_2, x_48);
return x_86;
}
}
}
else
{
uint8_t x_87; 
lean_dec(x_2);
x_87 = !lean_is_exclusive(x_8);
if (x_87 == 0)
{
return x_8;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_8, 0);
x_89 = lean_ctor_get(x_8, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_8);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
}
lean_object* l_Lean_Elab_Command_elabDeclaration___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Command_elabDeclaration(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabDeclaration___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabDeclaration");
return x_1;
}
}
lean_object* _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabDeclaration___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_declareBuiltinCommandElab___closed__3;
x_2 = l___regBuiltinCommandElab_Lean_Elab_Command_elabDeclaration___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabDeclaration___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabDeclaration___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabDeclaration(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Command_declaration___elambda__1___closed__2;
x_3 = l___regBuiltinCommandElab_Lean_Elab_Command_elabDeclaration___closed__2;
x_4 = l___regBuiltinCommandElab_Lean_Elab_Command_elabDeclaration___closed__3;
x_5 = l_Lean_Elab_Command_addBuiltinCommandElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* initialize_Init_Lean_Util_CollectLevelParams(lean_object*);
lean_object* initialize_Init_Lean_Elab_Definition(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Elab_Declaration(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Util_CollectLevelParams(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Elab_Definition(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Command_elabAbbrev___closed__1 = _init_l_Lean_Elab_Command_elabAbbrev___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabAbbrev___closed__1);
l_Lean_Elab_Command_elabAbbrev___closed__2 = _init_l_Lean_Elab_Command_elabAbbrev___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabAbbrev___closed__2);
l_Lean_Elab_Command_elabAbbrev___closed__3 = _init_l_Lean_Elab_Command_elabAbbrev___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabAbbrev___closed__3);
l_Lean_Elab_Command_elabAbbrev___closed__4 = _init_l_Lean_Elab_Command_elabAbbrev___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_elabAbbrev___closed__4);
l_Lean_Elab_Command_elabConstant___closed__1 = _init_l_Lean_Elab_Command_elabConstant___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabConstant___closed__1);
l_Lean_Elab_Command_elabConstant___closed__2 = _init_l_Lean_Elab_Command_elabConstant___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabConstant___closed__2);
l_Lean_Elab_Command_elabConstant___closed__3 = _init_l_Lean_Elab_Command_elabConstant___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabConstant___closed__3);
l_Lean_Elab_Command_elabConstant___closed__4 = _init_l_Lean_Elab_Command_elabConstant___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_elabConstant___closed__4);
l_Lean_Elab_Command_elabConstant___closed__5 = _init_l_Lean_Elab_Command_elabConstant___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_elabConstant___closed__5);
l_Lean_Elab_Command_elabConstant___closed__6 = _init_l_Lean_Elab_Command_elabConstant___closed__6();
lean_mark_persistent(l_Lean_Elab_Command_elabConstant___closed__6);
l_Lean_Elab_Command_elabConstant___closed__7 = _init_l_Lean_Elab_Command_elabConstant___closed__7();
lean_mark_persistent(l_Lean_Elab_Command_elabConstant___closed__7);
l_Lean_Elab_Command_elabConstant___closed__8 = _init_l_Lean_Elab_Command_elabConstant___closed__8();
lean_mark_persistent(l_Lean_Elab_Command_elabConstant___closed__8);
l_Lean_Elab_Command_elabConstant___closed__9 = _init_l_Lean_Elab_Command_elabConstant___closed__9();
lean_mark_persistent(l_Lean_Elab_Command_elabConstant___closed__9);
l_Lean_Elab_Command_elabInstance___closed__1 = _init_l_Lean_Elab_Command_elabInstance___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabInstance___closed__1);
l_Lean_Elab_Command_elabExample___closed__1 = _init_l_Lean_Elab_Command_elabExample___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabExample___closed__1);
l_Lean_Elab_Command_elabExample___closed__2 = _init_l_Lean_Elab_Command_elabExample___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabExample___closed__2);
l_Lean_Elab_Command_elabDeclaration___closed__1 = _init_l_Lean_Elab_Command_elabDeclaration___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabDeclaration___closed__1);
l_Lean_Elab_Command_elabDeclaration___closed__2 = _init_l_Lean_Elab_Command_elabDeclaration___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabDeclaration___closed__2);
l_Lean_Elab_Command_elabDeclaration___closed__3 = _init_l_Lean_Elab_Command_elabDeclaration___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabDeclaration___closed__3);
l_Lean_Elab_Command_elabDeclaration___closed__4 = _init_l_Lean_Elab_Command_elabDeclaration___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_elabDeclaration___closed__4);
l___regBuiltinCommandElab_Lean_Elab_Command_elabDeclaration___closed__1 = _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabDeclaration___closed__1();
lean_mark_persistent(l___regBuiltinCommandElab_Lean_Elab_Command_elabDeclaration___closed__1);
l___regBuiltinCommandElab_Lean_Elab_Command_elabDeclaration___closed__2 = _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabDeclaration___closed__2();
lean_mark_persistent(l___regBuiltinCommandElab_Lean_Elab_Command_elabDeclaration___closed__2);
l___regBuiltinCommandElab_Lean_Elab_Command_elabDeclaration___closed__3 = _init_l___regBuiltinCommandElab_Lean_Elab_Command_elabDeclaration___closed__3();
lean_mark_persistent(l___regBuiltinCommandElab_Lean_Elab_Command_elabDeclaration___closed__3);
res = l___regBuiltinCommandElab_Lean_Elab_Command_elabDeclaration(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
