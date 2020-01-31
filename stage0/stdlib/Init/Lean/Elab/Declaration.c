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
extern lean_object* l_Lean_mkHole___closed__3;
lean_object* l_Lean_Elab_Command_elabConstant___closed__9;
lean_object* l_Lean_Elab_Term_mkForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_extractMacroScopes(lean_object*);
extern lean_object* l_Lean_Parser_Command_abbrev___elambda__1___closed__2;
lean_object* l_Lean_Elab_Command_addDecl(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instantiateMVars(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabAxiom___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabConstant___closed__4;
lean_object* l_unreachable_x21___rarg(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_elabAxiom___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabDeclaration(lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabConstant___closed__2;
lean_object* l_Lean_Elab_Command_elabDeclaration___closed__4;
lean_object* l_Lean_Syntax_getIdAt(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabExample(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabAbbrev(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_runTermElabM___rarg___closed__1;
lean_object* l_Lean_Elab_Command_elabExample___closed__1;
lean_object* l_Lean_Elab_Command_elabConstant___closed__1;
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_elabAxiom___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_expandDeclSig(lean_object*);
lean_object* l_Lean_Elab_Command_elabExample___closed__2;
extern lean_object* l_Lean_Parser_Command_declaration___elambda__1___closed__2;
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Command_9__getVarDecls(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Elab_Term_mkForallUsedOnly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabDeclaration___closed__2;
lean_object* lean_string_utf8_byte_size(lean_object*);
extern lean_object* l_Lean_Parser_Command_example___elambda__1___closed__2;
lean_object* l_Lean_Elab_Command_elabAxiom___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_getNumParts___main(lean_object*);
lean_object* l_Lean_Elab_Command_elabInductive___rarg(lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__8;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_addBuiltinCommandElab(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_classInductive___elambda__1___closed__2;
extern lean_object* l_Lean_mkTermIdFromIdent___closed__2;
lean_object* l_Array_foldlStepMAux___main___at_Lean_Elab_Term_elabParen___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkDeclName(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabDeclaration___closed__1;
lean_object* l_Lean_Elab_Command_expandOptDeclSig___boxed(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_levelMVarToParam(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabStructure___rarg(lean_object*);
lean_object* l_Lean_Elab_Command_elabAxiom(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabInstance___closed__1;
lean_object* l_Lean_Elab_Command_elabConstant___closed__11;
extern lean_object* l_Lean_Parser_Command_def___elambda__1___closed__2;
extern lean_object* l_Lean_Parser_Command_declValSimple___elambda__1___closed__2;
extern lean_object* l_Lean_Meta_registerInstanceAttr___closed__1;
lean_object* l_Lean_Elab_Command_elabConstant(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabAxiom___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_expandOptDeclSig(lean_object*);
lean_object* l___regBuiltinCommandElab_Lean_Elab_Command_elabDeclaration___closed__3;
extern lean_object* l_Lean_Elab_Command_mkDef___lambda__1___closed__1;
extern lean_object* l_Lean_Meta_registerInstanceAttr___closed__2;
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_Elab_Command_elabClassInductive(lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabAxiom___spec__4(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_namespace___elambda__1___closed__1;
extern lean_object* l___regBuiltinParser_Lean_Parser_Command_antiquot___closed__2;
lean_object* l_Lean_Elab_Command_throwError___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_elem___main___at_Lean_Parser_addLeadingParser___spec__7(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Command_6__mkTermContext(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_11__synthesizeSyntheticMVarsAux___main(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabConstant___closed__7;
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabAxiom___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabTheorem(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabDef(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_withDeclId___closed__3;
lean_object* l_Lean_Elab_Command_elabAxiom___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_sortDeclLevelParams(lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabClassInductive___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_nullKind___closed__2;
extern lean_object* l_Lean_mkReducibilityAttrs___closed__4;
lean_object* l_Lean_Elab_Command_elabConstant___closed__10;
lean_object* l_Lean_mkAtomFrom(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Command_2__getState(lean_object*, lean_object*);
lean_object* l_List_drop___main___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabAbbrev___closed__3;
lean_object* l_Lean_Elab_Command_elabStructure___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabInstance(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_axiom___elambda__1___closed__2;
lean_object* l_Lean_Elab_Command_getCurrMacroScope(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getMainModule(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_elabLetDecl___closed__6;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_MacroScopesView_review(lean_object*);
lean_object* l_Lean_Elab_Command_elabInductive___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Command_12__addScopes___main(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabAbbrev___closed__2;
lean_object* l_Lean_Elab_Command_elabStructure(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_Modifiers_addAttribute(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabType(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_structure___elambda__1___closed__2;
extern lean_object* l_Lean_mkAppStx___closed__9;
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
lean_object* l_Lean_Elab_Command_expandDeclSig___boxed(lean_object*);
lean_object* l_Lean_Elab_Command_elabDeclaration___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkHole___closed__2;
lean_object* l_Lean_Elab_Term_elabBinders___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Init_Lean_Elab_TermBinders_4__expandBinderModifier___closed__3;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabDeclaration___closed__2;
lean_object* l_Lean_Elab_Command_elabAxiom___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
lean_object* l_Lean_Elab_Command_elabConstant___closed__5;
lean_object* l_Lean_Elab_Command_elabInductive(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabDeclaration___closed__1;
lean_object* l_Lean_Elab_Command_elabDeclaration___closed__3;
lean_object* l_Lean_Elab_Command_elabConstant___closed__3;
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabAxiom___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabAbbrev___closed__1;
lean_object* l___private_Init_Lean_Elab_Command_7__mkTermState(lean_object*);
lean_object* l_Lean_Elab_Command_elabAbbrev___closed__4;
lean_object* l_Lean_CollectLevelParams_main___main(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabAxiom___spec__1(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_constant___elambda__1___closed__2;
lean_object* l_Lean_Elab_Command_elabConstant___closed__8;
extern lean_object* l_Lean_Parser_Command_theorem___elambda__1___closed__2;
lean_object* l_Lean_Elab_Command_elabClassInductive___rarg(lean_object*);
lean_object* l___private_Init_Lean_Elab_Command_3__setState(lean_object*, lean_object*, lean_object*);
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
x_2 = l_Lean_mkHole___closed__3;
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
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_Elab_Command_elabConstant___closed__7;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_elabConstant___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkHole___closed__2;
x_2 = l_Lean_Elab_Command_elabConstant___closed__8;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_elabConstant___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_Elab_Command_elabConstant___closed__9;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_elabConstant___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_nullKind___closed__2;
x_2 = l_Lean_Elab_Command_elabConstant___closed__10;
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = l_Lean_Elab_Command_getCurrMacroScope(x_3, x_4);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_3);
x_16 = l_Lean_Elab_Command_getMainModule(x_3, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_box(0);
x_20 = l_Lean_Elab_Command_elabConstant___closed__4;
x_21 = l_Lean_addMacroScope(x_17, x_20, x_14);
x_22 = l_Lean_Elab_Command_elabConstant___closed__3;
x_23 = l_Lean_Elab_Command_elabConstant___closed__6;
x_24 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_24, 1, x_22);
lean_ctor_set(x_24, 2, x_21);
lean_ctor_set(x_24, 3, x_23);
x_25 = l_Array_empty___closed__1;
x_26 = lean_array_push(x_25, x_24);
x_27 = l___private_Init_Lean_Elab_Term_5__expandCDot___main___closed__4;
x_28 = lean_array_push(x_26, x_27);
x_29 = l_Lean_mkTermIdFromIdent___closed__2;
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = lean_array_push(x_25, x_30);
x_32 = l_Lean_Elab_Command_elabConstant___closed__11;
x_33 = lean_array_push(x_31, x_32);
x_34 = l_Lean_mkAppStx___closed__8;
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
x_36 = l_Lean_Elab_Term_elabLetDecl___closed__6;
x_37 = l_Lean_mkAtomFrom(x_2, x_36);
x_38 = l_Lean_mkAppStx___closed__9;
x_39 = lean_array_push(x_38, x_37);
x_40 = lean_array_push(x_39, x_35);
x_41 = l_Lean_Parser_Command_declValSimple___elambda__1___closed__2;
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
x_43 = lean_unsigned_to_nat(1u);
x_44 = l_Lean_Syntax_getArg(x_2, x_43);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_9);
x_46 = 3;
x_47 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_47, 0, x_2);
lean_ctor_set(x_47, 1, x_1);
lean_ctor_set(x_47, 2, x_44);
lean_ctor_set(x_47, 3, x_8);
lean_ctor_set(x_47, 4, x_45);
lean_ctor_set(x_47, 5, x_42);
lean_ctor_set_uint8(x_47, sizeof(void*)*6, x_46);
x_48 = l_Lean_Elab_Command_elabDefLike(x_47, x_3, x_18);
return x_48;
}
else
{
uint8_t x_49; 
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_16);
if (x_49 == 0)
{
return x_16;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_16, 0);
x_51 = lean_ctor_get(x_16, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_16);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_12);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; 
x_54 = lean_ctor_get(x_12, 0);
x_55 = lean_unsigned_to_nat(1u);
x_56 = l_Lean_Syntax_getArg(x_2, x_55);
lean_ctor_set(x_12, 0, x_9);
x_57 = 3;
x_58 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_58, 0, x_2);
lean_ctor_set(x_58, 1, x_1);
lean_ctor_set(x_58, 2, x_56);
lean_ctor_set(x_58, 3, x_8);
lean_ctor_set(x_58, 4, x_12);
lean_ctor_set(x_58, 5, x_54);
lean_ctor_set_uint8(x_58, sizeof(void*)*6, x_57);
x_59 = l_Lean_Elab_Command_elabDefLike(x_58, x_3, x_4);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; 
x_60 = lean_ctor_get(x_12, 0);
lean_inc(x_60);
lean_dec(x_12);
x_61 = lean_unsigned_to_nat(1u);
x_62 = l_Lean_Syntax_getArg(x_2, x_61);
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_9);
x_64 = 3;
x_65 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_65, 0, x_2);
lean_ctor_set(x_65, 1, x_1);
lean_ctor_set(x_65, 2, x_62);
lean_ctor_set(x_65, 3, x_8);
lean_ctor_set(x_65, 4, x_63);
lean_ctor_set(x_65, 5, x_60);
lean_ctor_set_uint8(x_65, sizeof(void*)*6, x_64);
x_66 = l_Lean_Elab_Command_elabDefLike(x_65, x_3, x_4);
return x_66;
}
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
x_15 = l___private_Init_Lean_Elab_TermBinders_4__expandBinderModifier___closed__3;
x_16 = l_Lean_Elab_Command_throwError___rarg(x_2, x_15, x_3, x_4);
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
x_12 = l_Lean_mkAppStx___closed__9;
x_13 = lean_array_push(x_12, x_11);
x_14 = l_Lean_mkOptionalNode___closed__1;
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
x_10 = lean_box(0);
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
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_5, 0);
x_24 = lean_ctor_get(x_5, 1);
x_25 = lean_ctor_get(x_5, 3);
x_26 = lean_ctor_get(x_5, 4);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_5);
x_27 = lean_box(0);
x_28 = l_unreachable_x21___rarg(x_27);
x_29 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_24);
lean_ctor_set(x_29, 2, x_28);
lean_ctor_set(x_29, 3, x_25);
lean_ctor_set(x_29, 4, x_26);
x_30 = l___private_Init_Lean_Elab_Command_3__setState(x_29, x_2, x_7);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_32 = x_30;
} else {
 lean_dec_ref(x_30);
 x_32 = lean_box(0);
}
x_33 = lean_box(0);
if (lean_is_scalar(x_32)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_32;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_30, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_30, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_37 = x_30;
} else {
 lean_dec_ref(x_30);
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
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_6, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_4, 1);
lean_inc(x_40);
lean_dec(x_4);
x_41 = !lean_is_exclusive(x_5);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_5, 2);
lean_dec(x_42);
x_43 = !lean_is_exclusive(x_6);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_6, 0);
lean_dec(x_44);
x_45 = !lean_is_exclusive(x_39);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_39, 5);
lean_dec(x_46);
lean_ctor_set(x_39, 5, x_1);
x_47 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_40);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_47, 0);
lean_dec(x_49);
x_50 = lean_box(0);
lean_ctor_set(x_47, 0, x_50);
return x_47;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_47, 1);
lean_inc(x_51);
lean_dec(x_47);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
else
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_47);
if (x_54 == 0)
{
return x_47;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_47, 0);
x_56 = lean_ctor_get(x_47, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_47);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_58 = lean_ctor_get(x_39, 0);
x_59 = lean_ctor_get(x_39, 1);
x_60 = lean_ctor_get(x_39, 2);
x_61 = lean_ctor_get(x_39, 3);
x_62 = lean_ctor_get(x_39, 4);
x_63 = lean_ctor_get(x_39, 6);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_39);
x_64 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_64, 0, x_58);
lean_ctor_set(x_64, 1, x_59);
lean_ctor_set(x_64, 2, x_60);
lean_ctor_set(x_64, 3, x_61);
lean_ctor_set(x_64, 4, x_62);
lean_ctor_set(x_64, 5, x_1);
lean_ctor_set(x_64, 6, x_63);
lean_ctor_set(x_6, 0, x_64);
x_65 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_40);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_67 = x_65;
} else {
 lean_dec_ref(x_65);
 x_67 = lean_box(0);
}
x_68 = lean_box(0);
if (lean_is_scalar(x_67)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_67;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_66);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_70 = lean_ctor_get(x_65, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_65, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_72 = x_65;
} else {
 lean_dec_ref(x_65);
 x_72 = lean_box(0);
}
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(1, 2, 0);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_71);
return x_73;
}
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_74 = lean_ctor_get(x_6, 1);
lean_inc(x_74);
lean_dec(x_6);
x_75 = lean_ctor_get(x_39, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_39, 1);
lean_inc(x_76);
x_77 = lean_ctor_get(x_39, 2);
lean_inc(x_77);
x_78 = lean_ctor_get(x_39, 3);
lean_inc(x_78);
x_79 = lean_ctor_get(x_39, 4);
lean_inc(x_79);
x_80 = lean_ctor_get(x_39, 6);
lean_inc(x_80);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 lean_ctor_release(x_39, 2);
 lean_ctor_release(x_39, 3);
 lean_ctor_release(x_39, 4);
 lean_ctor_release(x_39, 5);
 lean_ctor_release(x_39, 6);
 x_81 = x_39;
} else {
 lean_dec_ref(x_39);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(0, 7, 0);
} else {
 x_82 = x_81;
}
lean_ctor_set(x_82, 0, x_75);
lean_ctor_set(x_82, 1, x_76);
lean_ctor_set(x_82, 2, x_77);
lean_ctor_set(x_82, 3, x_78);
lean_ctor_set(x_82, 4, x_79);
lean_ctor_set(x_82, 5, x_1);
lean_ctor_set(x_82, 6, x_80);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_74);
lean_ctor_set(x_5, 2, x_83);
x_84 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_40);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
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
x_87 = lean_box(0);
if (lean_is_scalar(x_86)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_86;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_85);
return x_88;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_89 = lean_ctor_get(x_84, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_84, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_91 = x_84;
} else {
 lean_dec_ref(x_84);
 x_91 = lean_box(0);
}
if (lean_is_scalar(x_91)) {
 x_92 = lean_alloc_ctor(1, 2, 0);
} else {
 x_92 = x_91;
}
lean_ctor_set(x_92, 0, x_89);
lean_ctor_set(x_92, 1, x_90);
return x_92;
}
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_93 = lean_ctor_get(x_5, 0);
x_94 = lean_ctor_get(x_5, 1);
x_95 = lean_ctor_get(x_5, 3);
x_96 = lean_ctor_get(x_5, 4);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_5);
x_97 = lean_ctor_get(x_6, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_98 = x_6;
} else {
 lean_dec_ref(x_6);
 x_98 = lean_box(0);
}
x_99 = lean_ctor_get(x_39, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_39, 1);
lean_inc(x_100);
x_101 = lean_ctor_get(x_39, 2);
lean_inc(x_101);
x_102 = lean_ctor_get(x_39, 3);
lean_inc(x_102);
x_103 = lean_ctor_get(x_39, 4);
lean_inc(x_103);
x_104 = lean_ctor_get(x_39, 6);
lean_inc(x_104);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 lean_ctor_release(x_39, 2);
 lean_ctor_release(x_39, 3);
 lean_ctor_release(x_39, 4);
 lean_ctor_release(x_39, 5);
 lean_ctor_release(x_39, 6);
 x_105 = x_39;
} else {
 lean_dec_ref(x_39);
 x_105 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(0, 7, 0);
} else {
 x_106 = x_105;
}
lean_ctor_set(x_106, 0, x_99);
lean_ctor_set(x_106, 1, x_100);
lean_ctor_set(x_106, 2, x_101);
lean_ctor_set(x_106, 3, x_102);
lean_ctor_set(x_106, 4, x_103);
lean_ctor_set(x_106, 5, x_1);
lean_ctor_set(x_106, 6, x_104);
if (lean_is_scalar(x_98)) {
 x_107 = lean_alloc_ctor(1, 2, 0);
} else {
 x_107 = x_98;
}
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_97);
x_108 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_108, 0, x_93);
lean_ctor_set(x_108, 1, x_94);
lean_ctor_set(x_108, 2, x_107);
lean_ctor_set(x_108, 3, x_95);
lean_ctor_set(x_108, 4, x_96);
x_109 = l___private_Init_Lean_Elab_Command_3__setState(x_108, x_2, x_40);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_110 = lean_ctor_get(x_109, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_111 = x_109;
} else {
 lean_dec_ref(x_109);
 x_111 = lean_box(0);
}
x_112 = lean_box(0);
if (lean_is_scalar(x_111)) {
 x_113 = lean_alloc_ctor(0, 2, 0);
} else {
 x_113 = x_111;
}
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_110);
return x_113;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_114 = lean_ctor_get(x_109, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_109, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_116 = x_109;
} else {
 lean_dec_ref(x_109);
 x_116 = lean_box(0);
}
if (lean_is_scalar(x_116)) {
 x_117 = lean_alloc_ctor(1, 2, 0);
} else {
 x_117 = x_116;
}
lean_ctor_set(x_117, 0, x_114);
lean_ctor_set(x_117, 1, x_115);
return x_117;
}
}
}
}
else
{
uint8_t x_118; 
lean_dec(x_2);
lean_dec(x_1);
x_118 = !lean_is_exclusive(x_4);
if (x_118 == 0)
{
return x_4;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_4, 0);
x_120 = lean_ctor_get(x_4, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_4);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
return x_121;
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
x_10 = lean_box(0);
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
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_5, 0);
x_24 = lean_ctor_get(x_5, 1);
x_25 = lean_ctor_get(x_5, 3);
x_26 = lean_ctor_get(x_5, 4);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_5);
x_27 = lean_box(0);
x_28 = l_unreachable_x21___rarg(x_27);
x_29 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_24);
lean_ctor_set(x_29, 2, x_28);
lean_ctor_set(x_29, 3, x_25);
lean_ctor_set(x_29, 4, x_26);
x_30 = l___private_Init_Lean_Elab_Command_3__setState(x_29, x_2, x_7);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_32 = x_30;
} else {
 lean_dec_ref(x_30);
 x_32 = lean_box(0);
}
x_33 = lean_box(0);
if (lean_is_scalar(x_32)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_32;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_30, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_30, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_37 = x_30;
} else {
 lean_dec_ref(x_30);
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
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_6, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_4, 1);
lean_inc(x_40);
lean_dec(x_4);
x_41 = !lean_is_exclusive(x_5);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_5, 2);
lean_dec(x_42);
x_43 = !lean_is_exclusive(x_6);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_6, 0);
lean_dec(x_44);
x_45 = !lean_is_exclusive(x_39);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_39, 5);
lean_dec(x_46);
lean_ctor_set(x_39, 5, x_1);
x_47 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_40);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_47, 0);
lean_dec(x_49);
x_50 = lean_box(0);
lean_ctor_set(x_47, 0, x_50);
return x_47;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_47, 1);
lean_inc(x_51);
lean_dec(x_47);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
else
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_47);
if (x_54 == 0)
{
return x_47;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_47, 0);
x_56 = lean_ctor_get(x_47, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_47);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_58 = lean_ctor_get(x_39, 0);
x_59 = lean_ctor_get(x_39, 1);
x_60 = lean_ctor_get(x_39, 2);
x_61 = lean_ctor_get(x_39, 3);
x_62 = lean_ctor_get(x_39, 4);
x_63 = lean_ctor_get(x_39, 6);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_39);
x_64 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_64, 0, x_58);
lean_ctor_set(x_64, 1, x_59);
lean_ctor_set(x_64, 2, x_60);
lean_ctor_set(x_64, 3, x_61);
lean_ctor_set(x_64, 4, x_62);
lean_ctor_set(x_64, 5, x_1);
lean_ctor_set(x_64, 6, x_63);
lean_ctor_set(x_6, 0, x_64);
x_65 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_40);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_67 = x_65;
} else {
 lean_dec_ref(x_65);
 x_67 = lean_box(0);
}
x_68 = lean_box(0);
if (lean_is_scalar(x_67)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_67;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_66);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_70 = lean_ctor_get(x_65, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_65, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_72 = x_65;
} else {
 lean_dec_ref(x_65);
 x_72 = lean_box(0);
}
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(1, 2, 0);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_71);
return x_73;
}
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_74 = lean_ctor_get(x_6, 1);
lean_inc(x_74);
lean_dec(x_6);
x_75 = lean_ctor_get(x_39, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_39, 1);
lean_inc(x_76);
x_77 = lean_ctor_get(x_39, 2);
lean_inc(x_77);
x_78 = lean_ctor_get(x_39, 3);
lean_inc(x_78);
x_79 = lean_ctor_get(x_39, 4);
lean_inc(x_79);
x_80 = lean_ctor_get(x_39, 6);
lean_inc(x_80);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 lean_ctor_release(x_39, 2);
 lean_ctor_release(x_39, 3);
 lean_ctor_release(x_39, 4);
 lean_ctor_release(x_39, 5);
 lean_ctor_release(x_39, 6);
 x_81 = x_39;
} else {
 lean_dec_ref(x_39);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(0, 7, 0);
} else {
 x_82 = x_81;
}
lean_ctor_set(x_82, 0, x_75);
lean_ctor_set(x_82, 1, x_76);
lean_ctor_set(x_82, 2, x_77);
lean_ctor_set(x_82, 3, x_78);
lean_ctor_set(x_82, 4, x_79);
lean_ctor_set(x_82, 5, x_1);
lean_ctor_set(x_82, 6, x_80);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_74);
lean_ctor_set(x_5, 2, x_83);
x_84 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_40);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
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
x_87 = lean_box(0);
if (lean_is_scalar(x_86)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_86;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_85);
return x_88;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_89 = lean_ctor_get(x_84, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_84, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_91 = x_84;
} else {
 lean_dec_ref(x_84);
 x_91 = lean_box(0);
}
if (lean_is_scalar(x_91)) {
 x_92 = lean_alloc_ctor(1, 2, 0);
} else {
 x_92 = x_91;
}
lean_ctor_set(x_92, 0, x_89);
lean_ctor_set(x_92, 1, x_90);
return x_92;
}
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_93 = lean_ctor_get(x_5, 0);
x_94 = lean_ctor_get(x_5, 1);
x_95 = lean_ctor_get(x_5, 3);
x_96 = lean_ctor_get(x_5, 4);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_5);
x_97 = lean_ctor_get(x_6, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_98 = x_6;
} else {
 lean_dec_ref(x_6);
 x_98 = lean_box(0);
}
x_99 = lean_ctor_get(x_39, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_39, 1);
lean_inc(x_100);
x_101 = lean_ctor_get(x_39, 2);
lean_inc(x_101);
x_102 = lean_ctor_get(x_39, 3);
lean_inc(x_102);
x_103 = lean_ctor_get(x_39, 4);
lean_inc(x_103);
x_104 = lean_ctor_get(x_39, 6);
lean_inc(x_104);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 lean_ctor_release(x_39, 2);
 lean_ctor_release(x_39, 3);
 lean_ctor_release(x_39, 4);
 lean_ctor_release(x_39, 5);
 lean_ctor_release(x_39, 6);
 x_105 = x_39;
} else {
 lean_dec_ref(x_39);
 x_105 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(0, 7, 0);
} else {
 x_106 = x_105;
}
lean_ctor_set(x_106, 0, x_99);
lean_ctor_set(x_106, 1, x_100);
lean_ctor_set(x_106, 2, x_101);
lean_ctor_set(x_106, 3, x_102);
lean_ctor_set(x_106, 4, x_103);
lean_ctor_set(x_106, 5, x_1);
lean_ctor_set(x_106, 6, x_104);
if (lean_is_scalar(x_98)) {
 x_107 = lean_alloc_ctor(1, 2, 0);
} else {
 x_107 = x_98;
}
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_97);
x_108 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_108, 0, x_93);
lean_ctor_set(x_108, 1, x_94);
lean_ctor_set(x_108, 2, x_107);
lean_ctor_set(x_108, 3, x_95);
lean_ctor_set(x_108, 4, x_96);
x_109 = l___private_Init_Lean_Elab_Command_3__setState(x_108, x_2, x_40);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_110 = lean_ctor_get(x_109, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_111 = x_109;
} else {
 lean_dec_ref(x_109);
 x_111 = lean_box(0);
}
x_112 = lean_box(0);
if (lean_is_scalar(x_111)) {
 x_113 = lean_alloc_ctor(0, 2, 0);
} else {
 x_113 = x_111;
}
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_110);
return x_113;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_114 = lean_ctor_get(x_109, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_109, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_116 = x_109;
} else {
 lean_dec_ref(x_109);
 x_116 = lean_box(0);
}
if (lean_is_scalar(x_116)) {
 x_117 = lean_alloc_ctor(1, 2, 0);
} else {
 x_117 = x_116;
}
lean_ctor_set(x_117, 0, x_114);
lean_ctor_set(x_117, 1, x_115);
return x_117;
}
}
}
}
else
{
uint8_t x_118; 
lean_dec(x_2);
lean_dec(x_1);
x_118 = !lean_is_exclusive(x_4);
if (x_118 == 0)
{
return x_4;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_4, 0);
x_120 = lean_ctor_get(x_4, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_4);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
return x_121;
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
x_10 = lean_box(0);
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
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_5, 0);
x_24 = lean_ctor_get(x_5, 1);
x_25 = lean_ctor_get(x_5, 3);
x_26 = lean_ctor_get(x_5, 4);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_5);
x_27 = lean_box(0);
x_28 = l_unreachable_x21___rarg(x_27);
x_29 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_24);
lean_ctor_set(x_29, 2, x_28);
lean_ctor_set(x_29, 3, x_25);
lean_ctor_set(x_29, 4, x_26);
x_30 = l___private_Init_Lean_Elab_Command_3__setState(x_29, x_2, x_7);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_32 = x_30;
} else {
 lean_dec_ref(x_30);
 x_32 = lean_box(0);
}
x_33 = lean_box(0);
if (lean_is_scalar(x_32)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_32;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_30, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_30, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_37 = x_30;
} else {
 lean_dec_ref(x_30);
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
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_6, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_4, 1);
lean_inc(x_40);
lean_dec(x_4);
x_41 = !lean_is_exclusive(x_5);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_5, 2);
lean_dec(x_42);
x_43 = !lean_is_exclusive(x_6);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_6, 0);
lean_dec(x_44);
x_45 = !lean_is_exclusive(x_39);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_39, 5);
lean_dec(x_46);
lean_ctor_set(x_39, 5, x_1);
x_47 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_40);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_47, 0);
lean_dec(x_49);
x_50 = lean_box(0);
lean_ctor_set(x_47, 0, x_50);
return x_47;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_47, 1);
lean_inc(x_51);
lean_dec(x_47);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
else
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_47);
if (x_54 == 0)
{
return x_47;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_47, 0);
x_56 = lean_ctor_get(x_47, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_47);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_58 = lean_ctor_get(x_39, 0);
x_59 = lean_ctor_get(x_39, 1);
x_60 = lean_ctor_get(x_39, 2);
x_61 = lean_ctor_get(x_39, 3);
x_62 = lean_ctor_get(x_39, 4);
x_63 = lean_ctor_get(x_39, 6);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_39);
x_64 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_64, 0, x_58);
lean_ctor_set(x_64, 1, x_59);
lean_ctor_set(x_64, 2, x_60);
lean_ctor_set(x_64, 3, x_61);
lean_ctor_set(x_64, 4, x_62);
lean_ctor_set(x_64, 5, x_1);
lean_ctor_set(x_64, 6, x_63);
lean_ctor_set(x_6, 0, x_64);
x_65 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_40);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_67 = x_65;
} else {
 lean_dec_ref(x_65);
 x_67 = lean_box(0);
}
x_68 = lean_box(0);
if (lean_is_scalar(x_67)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_67;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_66);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_70 = lean_ctor_get(x_65, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_65, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_72 = x_65;
} else {
 lean_dec_ref(x_65);
 x_72 = lean_box(0);
}
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(1, 2, 0);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_71);
return x_73;
}
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_74 = lean_ctor_get(x_6, 1);
lean_inc(x_74);
lean_dec(x_6);
x_75 = lean_ctor_get(x_39, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_39, 1);
lean_inc(x_76);
x_77 = lean_ctor_get(x_39, 2);
lean_inc(x_77);
x_78 = lean_ctor_get(x_39, 3);
lean_inc(x_78);
x_79 = lean_ctor_get(x_39, 4);
lean_inc(x_79);
x_80 = lean_ctor_get(x_39, 6);
lean_inc(x_80);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 lean_ctor_release(x_39, 2);
 lean_ctor_release(x_39, 3);
 lean_ctor_release(x_39, 4);
 lean_ctor_release(x_39, 5);
 lean_ctor_release(x_39, 6);
 x_81 = x_39;
} else {
 lean_dec_ref(x_39);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(0, 7, 0);
} else {
 x_82 = x_81;
}
lean_ctor_set(x_82, 0, x_75);
lean_ctor_set(x_82, 1, x_76);
lean_ctor_set(x_82, 2, x_77);
lean_ctor_set(x_82, 3, x_78);
lean_ctor_set(x_82, 4, x_79);
lean_ctor_set(x_82, 5, x_1);
lean_ctor_set(x_82, 6, x_80);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_74);
lean_ctor_set(x_5, 2, x_83);
x_84 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_40);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
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
x_87 = lean_box(0);
if (lean_is_scalar(x_86)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_86;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_85);
return x_88;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_89 = lean_ctor_get(x_84, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_84, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_91 = x_84;
} else {
 lean_dec_ref(x_84);
 x_91 = lean_box(0);
}
if (lean_is_scalar(x_91)) {
 x_92 = lean_alloc_ctor(1, 2, 0);
} else {
 x_92 = x_91;
}
lean_ctor_set(x_92, 0, x_89);
lean_ctor_set(x_92, 1, x_90);
return x_92;
}
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_93 = lean_ctor_get(x_5, 0);
x_94 = lean_ctor_get(x_5, 1);
x_95 = lean_ctor_get(x_5, 3);
x_96 = lean_ctor_get(x_5, 4);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_5);
x_97 = lean_ctor_get(x_6, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_98 = x_6;
} else {
 lean_dec_ref(x_6);
 x_98 = lean_box(0);
}
x_99 = lean_ctor_get(x_39, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_39, 1);
lean_inc(x_100);
x_101 = lean_ctor_get(x_39, 2);
lean_inc(x_101);
x_102 = lean_ctor_get(x_39, 3);
lean_inc(x_102);
x_103 = lean_ctor_get(x_39, 4);
lean_inc(x_103);
x_104 = lean_ctor_get(x_39, 6);
lean_inc(x_104);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 lean_ctor_release(x_39, 2);
 lean_ctor_release(x_39, 3);
 lean_ctor_release(x_39, 4);
 lean_ctor_release(x_39, 5);
 lean_ctor_release(x_39, 6);
 x_105 = x_39;
} else {
 lean_dec_ref(x_39);
 x_105 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(0, 7, 0);
} else {
 x_106 = x_105;
}
lean_ctor_set(x_106, 0, x_99);
lean_ctor_set(x_106, 1, x_100);
lean_ctor_set(x_106, 2, x_101);
lean_ctor_set(x_106, 3, x_102);
lean_ctor_set(x_106, 4, x_103);
lean_ctor_set(x_106, 5, x_1);
lean_ctor_set(x_106, 6, x_104);
if (lean_is_scalar(x_98)) {
 x_107 = lean_alloc_ctor(1, 2, 0);
} else {
 x_107 = x_98;
}
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_97);
x_108 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_108, 0, x_93);
lean_ctor_set(x_108, 1, x_94);
lean_ctor_set(x_108, 2, x_107);
lean_ctor_set(x_108, 3, x_95);
lean_ctor_set(x_108, 4, x_96);
x_109 = l___private_Init_Lean_Elab_Command_3__setState(x_108, x_2, x_40);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_110 = lean_ctor_get(x_109, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_111 = x_109;
} else {
 lean_dec_ref(x_109);
 x_111 = lean_box(0);
}
x_112 = lean_box(0);
if (lean_is_scalar(x_111)) {
 x_113 = lean_alloc_ctor(0, 2, 0);
} else {
 x_113 = x_111;
}
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_110);
return x_113;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_114 = lean_ctor_get(x_109, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_109, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_116 = x_109;
} else {
 lean_dec_ref(x_109);
 x_116 = lean_box(0);
}
if (lean_is_scalar(x_116)) {
 x_117 = lean_alloc_ctor(1, 2, 0);
} else {
 x_117 = x_116;
}
lean_ctor_set(x_117, 0, x_114);
lean_ctor_set(x_117, 1, x_115);
return x_117;
}
}
}
}
else
{
uint8_t x_118; 
lean_dec(x_2);
lean_dec(x_1);
x_118 = !lean_is_exclusive(x_4);
if (x_118 == 0)
{
return x_4;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_4, 0);
x_120 = lean_ctor_get(x_4, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_4);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
return x_121;
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
x_10 = lean_box(0);
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
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_5, 0);
x_24 = lean_ctor_get(x_5, 1);
x_25 = lean_ctor_get(x_5, 3);
x_26 = lean_ctor_get(x_5, 4);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_5);
x_27 = lean_box(0);
x_28 = l_unreachable_x21___rarg(x_27);
x_29 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_24);
lean_ctor_set(x_29, 2, x_28);
lean_ctor_set(x_29, 3, x_25);
lean_ctor_set(x_29, 4, x_26);
x_30 = l___private_Init_Lean_Elab_Command_3__setState(x_29, x_2, x_7);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_32 = x_30;
} else {
 lean_dec_ref(x_30);
 x_32 = lean_box(0);
}
x_33 = lean_box(0);
if (lean_is_scalar(x_32)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_32;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_30, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_30, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_37 = x_30;
} else {
 lean_dec_ref(x_30);
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
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_6, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_4, 1);
lean_inc(x_40);
lean_dec(x_4);
x_41 = !lean_is_exclusive(x_5);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_5, 2);
lean_dec(x_42);
x_43 = !lean_is_exclusive(x_6);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_6, 0);
lean_dec(x_44);
x_45 = !lean_is_exclusive(x_39);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_39, 5);
lean_dec(x_46);
lean_ctor_set(x_39, 5, x_1);
x_47 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_40);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_47, 0);
lean_dec(x_49);
x_50 = lean_box(0);
lean_ctor_set(x_47, 0, x_50);
return x_47;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_47, 1);
lean_inc(x_51);
lean_dec(x_47);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
else
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_47);
if (x_54 == 0)
{
return x_47;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_47, 0);
x_56 = lean_ctor_get(x_47, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_47);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_58 = lean_ctor_get(x_39, 0);
x_59 = lean_ctor_get(x_39, 1);
x_60 = lean_ctor_get(x_39, 2);
x_61 = lean_ctor_get(x_39, 3);
x_62 = lean_ctor_get(x_39, 4);
x_63 = lean_ctor_get(x_39, 6);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_39);
x_64 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_64, 0, x_58);
lean_ctor_set(x_64, 1, x_59);
lean_ctor_set(x_64, 2, x_60);
lean_ctor_set(x_64, 3, x_61);
lean_ctor_set(x_64, 4, x_62);
lean_ctor_set(x_64, 5, x_1);
lean_ctor_set(x_64, 6, x_63);
lean_ctor_set(x_6, 0, x_64);
x_65 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_40);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_67 = x_65;
} else {
 lean_dec_ref(x_65);
 x_67 = lean_box(0);
}
x_68 = lean_box(0);
if (lean_is_scalar(x_67)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_67;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_66);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_70 = lean_ctor_get(x_65, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_65, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_72 = x_65;
} else {
 lean_dec_ref(x_65);
 x_72 = lean_box(0);
}
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(1, 2, 0);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_71);
return x_73;
}
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_74 = lean_ctor_get(x_6, 1);
lean_inc(x_74);
lean_dec(x_6);
x_75 = lean_ctor_get(x_39, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_39, 1);
lean_inc(x_76);
x_77 = lean_ctor_get(x_39, 2);
lean_inc(x_77);
x_78 = lean_ctor_get(x_39, 3);
lean_inc(x_78);
x_79 = lean_ctor_get(x_39, 4);
lean_inc(x_79);
x_80 = lean_ctor_get(x_39, 6);
lean_inc(x_80);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 lean_ctor_release(x_39, 2);
 lean_ctor_release(x_39, 3);
 lean_ctor_release(x_39, 4);
 lean_ctor_release(x_39, 5);
 lean_ctor_release(x_39, 6);
 x_81 = x_39;
} else {
 lean_dec_ref(x_39);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(0, 7, 0);
} else {
 x_82 = x_81;
}
lean_ctor_set(x_82, 0, x_75);
lean_ctor_set(x_82, 1, x_76);
lean_ctor_set(x_82, 2, x_77);
lean_ctor_set(x_82, 3, x_78);
lean_ctor_set(x_82, 4, x_79);
lean_ctor_set(x_82, 5, x_1);
lean_ctor_set(x_82, 6, x_80);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_74);
lean_ctor_set(x_5, 2, x_83);
x_84 = l___private_Init_Lean_Elab_Command_3__setState(x_5, x_2, x_40);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
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
x_87 = lean_box(0);
if (lean_is_scalar(x_86)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_86;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_85);
return x_88;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_89 = lean_ctor_get(x_84, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_84, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_91 = x_84;
} else {
 lean_dec_ref(x_84);
 x_91 = lean_box(0);
}
if (lean_is_scalar(x_91)) {
 x_92 = lean_alloc_ctor(1, 2, 0);
} else {
 x_92 = x_91;
}
lean_ctor_set(x_92, 0, x_89);
lean_ctor_set(x_92, 1, x_90);
return x_92;
}
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_93 = lean_ctor_get(x_5, 0);
x_94 = lean_ctor_get(x_5, 1);
x_95 = lean_ctor_get(x_5, 3);
x_96 = lean_ctor_get(x_5, 4);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_5);
x_97 = lean_ctor_get(x_6, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_98 = x_6;
} else {
 lean_dec_ref(x_6);
 x_98 = lean_box(0);
}
x_99 = lean_ctor_get(x_39, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_39, 1);
lean_inc(x_100);
x_101 = lean_ctor_get(x_39, 2);
lean_inc(x_101);
x_102 = lean_ctor_get(x_39, 3);
lean_inc(x_102);
x_103 = lean_ctor_get(x_39, 4);
lean_inc(x_103);
x_104 = lean_ctor_get(x_39, 6);
lean_inc(x_104);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 lean_ctor_release(x_39, 2);
 lean_ctor_release(x_39, 3);
 lean_ctor_release(x_39, 4);
 lean_ctor_release(x_39, 5);
 lean_ctor_release(x_39, 6);
 x_105 = x_39;
} else {
 lean_dec_ref(x_39);
 x_105 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(0, 7, 0);
} else {
 x_106 = x_105;
}
lean_ctor_set(x_106, 0, x_99);
lean_ctor_set(x_106, 1, x_100);
lean_ctor_set(x_106, 2, x_101);
lean_ctor_set(x_106, 3, x_102);
lean_ctor_set(x_106, 4, x_103);
lean_ctor_set(x_106, 5, x_1);
lean_ctor_set(x_106, 6, x_104);
if (lean_is_scalar(x_98)) {
 x_107 = lean_alloc_ctor(1, 2, 0);
} else {
 x_107 = x_98;
}
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_97);
x_108 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_108, 0, x_93);
lean_ctor_set(x_108, 1, x_94);
lean_ctor_set(x_108, 2, x_107);
lean_ctor_set(x_108, 3, x_95);
lean_ctor_set(x_108, 4, x_96);
x_109 = l___private_Init_Lean_Elab_Command_3__setState(x_108, x_2, x_40);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_110 = lean_ctor_get(x_109, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_111 = x_109;
} else {
 lean_dec_ref(x_109);
 x_111 = lean_box(0);
}
x_112 = lean_box(0);
if (lean_is_scalar(x_111)) {
 x_113 = lean_alloc_ctor(0, 2, 0);
} else {
 x_113 = x_111;
}
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_110);
return x_113;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_114 = lean_ctor_get(x_109, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_109, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_116 = x_109;
} else {
 lean_dec_ref(x_109);
 x_116 = lean_box(0);
}
if (lean_is_scalar(x_116)) {
 x_117 = lean_alloc_ctor(1, 2, 0);
} else {
 x_117 = x_116;
}
lean_ctor_set(x_117, 0, x_114);
lean_ctor_set(x_117, 1, x_115);
return x_117;
}
}
}
}
else
{
uint8_t x_118; 
lean_dec(x_2);
lean_dec(x_1);
x_118 = !lean_is_exclusive(x_4);
if (x_118 == 0)
{
return x_4;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_4, 0);
x_120 = lean_ctor_get(x_4, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_4);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
return x_121;
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
lean_dec(x_5);
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
x_14 = l_List_elem___main___at_Lean_Parser_addLeadingParser___spec__7(x_13, x_4);
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
x_14 = l___private_Init_Lean_Elab_SynthesizeSyntheticMVars_11__synthesizeSyntheticMVarsAux___main(x_12, x_13, x_7, x_11);
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
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = l_Lean_Elab_Command_mkDef___lambda__1___closed__1;
lean_inc(x_28);
x_30 = l_Lean_CollectLevelParams_main___main(x_28, x_29);
x_31 = lean_ctor_get(x_30, 2);
lean_inc(x_31);
lean_dec(x_30);
x_32 = l_Lean_Elab_Command_sortDeclLevelParams(x_3, x_31);
x_33 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_33, 0, x_4);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_33, 2, x_28);
x_34 = lean_ctor_get_uint8(x_5, sizeof(void*)*2 + 3);
x_35 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_34);
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_26, 0, x_36);
return x_26;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_37 = lean_ctor_get(x_26, 0);
x_38 = lean_ctor_get(x_26, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_26);
x_39 = l_Lean_Elab_Command_mkDef___lambda__1___closed__1;
lean_inc(x_37);
x_40 = l_Lean_CollectLevelParams_main___main(x_37, x_39);
x_41 = lean_ctor_get(x_40, 2);
lean_inc(x_41);
lean_dec(x_40);
x_42 = l_Lean_Elab_Command_sortDeclLevelParams(x_3, x_41);
x_43 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_43, 0, x_4);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_43, 2, x_37);
x_44 = lean_ctor_get_uint8(x_5, sizeof(void*)*2 + 3);
x_45 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set_uint8(x_45, sizeof(void*)*1, x_44);
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_38);
return x_47;
}
}
else
{
uint8_t x_48; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_48 = !lean_is_exclusive(x_22);
if (x_48 == 0)
{
return x_22;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_22, 0);
x_50 = lean_ctor_get(x_22, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_22);
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
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_52 = !lean_is_exclusive(x_19);
if (x_52 == 0)
{
return x_19;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_19, 0);
x_54 = lean_ctor_get(x_19, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_19);
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
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_14);
if (x_56 == 0)
{
return x_14;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_14, 0);
x_58 = lean_ctor_get(x_14, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_14);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_60 = !lean_is_exclusive(x_9);
if (x_60 == 0)
{
return x_9;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_9, 0);
x_62 = lean_ctor_get(x_9, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_9);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
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
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_371; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_371 = l_Lean_Syntax_isNone(x_14);
if (x_371 == 0)
{
lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; 
x_372 = l_Lean_Syntax_getArg(x_14, x_5);
lean_dec(x_14);
x_373 = l_Lean_Syntax_getArgs(x_372);
lean_dec(x_372);
x_374 = l_Array_empty___closed__1;
x_375 = l_Array_foldlStepMAux___main___at_Lean_Elab_Term_elabParen___spec__1(x_7, x_373, x_12, x_374);
lean_dec(x_373);
lean_inc(x_3);
lean_inc(x_16);
x_376 = l_Array_iterateMAux___main___at_Lean_Elab_Command_elabAxiom___spec__5(x_2, x_375, x_12, x_16, x_3, x_17);
lean_dec(x_375);
if (lean_obj_tag(x_376) == 0)
{
lean_object* x_377; lean_object* x_378; 
x_377 = lean_ctor_get(x_376, 0);
lean_inc(x_377);
x_378 = lean_ctor_get(x_376, 1);
lean_inc(x_378);
lean_dec(x_376);
x_18 = x_377;
x_19 = x_378;
goto block_370;
}
else
{
uint8_t x_379; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_379 = !lean_is_exclusive(x_376);
if (x_379 == 0)
{
return x_376;
}
else
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; 
x_380 = lean_ctor_get(x_376, 0);
x_381 = lean_ctor_get(x_376, 1);
lean_inc(x_381);
lean_inc(x_380);
lean_dec(x_376);
x_382 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_382, 0, x_380);
lean_ctor_set(x_382, 1, x_381);
return x_382;
}
}
}
else
{
lean_dec(x_14);
lean_inc(x_16);
x_18 = x_16;
x_19 = x_17;
goto block_370;
}
block_370:
{
lean_object* x_20; lean_object* x_21; 
x_20 = l_Lean_extractMacroScopes(x_13);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 1)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_23 = lean_ctor_get(x_20, 0);
lean_dec(x_23);
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_dec(x_21);
x_26 = lean_box(0);
x_27 = lean_name_mk_string(x_26, x_25);
lean_ctor_set(x_20, 0, x_27);
x_28 = l_Lean_MacroScopesView_review(x_20);
x_29 = l_Lean_Parser_Command_namespace___elambda__1___closed__1;
x_30 = 1;
lean_inc(x_3);
lean_inc(x_24);
x_31 = l___private_Init_Lean_Elab_Command_12__addScopes___main(x_6, x_29, x_30, x_24, x_3, x_19);
lean_dec(x_6);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
lean_inc(x_3);
x_33 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabAxiom___spec__1(x_18, x_3, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_47; 
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
lean_inc(x_3);
x_47 = l_Lean_Elab_Command_mkDeclName(x_1, x_28, x_3, x_34);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_118; lean_object* x_119; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_ctor_get(x_1, 1);
lean_inc(x_50);
x_118 = 2;
lean_inc(x_3);
lean_inc(x_48);
x_119 = l_Array_forMAux___main___at_Lean_Elab_Command_applyAttributes___spec__1(x_2, x_48, x_118, x_50, x_12, x_3, x_49);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; 
x_120 = lean_ctor_get(x_119, 1);
lean_inc(x_120);
lean_dec(x_119);
lean_inc(x_3);
x_121 = l_Lean_Elab_Command_getLevelNames(x_3, x_120);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
lean_dec(x_121);
lean_inc(x_48);
x_124 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_124, 0, x_48);
lean_inc(x_48);
x_125 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabAxiom___lambda__2___boxed), 8, 5);
lean_closure_set(x_125, 0, x_10);
lean_closure_set(x_125, 1, x_11);
lean_closure_set(x_125, 2, x_122);
lean_closure_set(x_125, 3, x_48);
lean_closure_set(x_125, 4, x_1);
lean_inc(x_3);
x_126 = l___private_Init_Lean_Elab_Command_2__getState(x_3, x_123);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec(x_126);
x_129 = l___private_Init_Lean_Elab_Command_9__getVarDecls(x_127);
x_130 = l___private_Init_Lean_Elab_Command_6__mkTermContext(x_3, x_127, x_124);
x_131 = l___private_Init_Lean_Elab_Command_7__mkTermState(x_127);
lean_dec(x_127);
x_132 = l_Lean_Elab_Term_elabBinders___rarg(x_129, x_125, x_130, x_131);
lean_dec(x_129);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec(x_132);
lean_inc(x_3);
x_135 = l___private_Init_Lean_Elab_Command_2__getState(x_3, x_128);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; 
x_136 = lean_ctor_get(x_134, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_135, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_135, 1);
lean_inc(x_138);
lean_dec(x_135);
x_139 = lean_ctor_get(x_136, 0);
lean_inc(x_139);
lean_dec(x_136);
x_140 = lean_ctor_get(x_134, 2);
lean_inc(x_140);
lean_dec(x_134);
x_141 = !lean_is_exclusive(x_137);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_142 = lean_ctor_get(x_137, 1);
lean_dec(x_142);
x_143 = lean_ctor_get(x_137, 0);
lean_dec(x_143);
lean_ctor_set(x_137, 1, x_140);
lean_ctor_set(x_137, 0, x_139);
lean_inc(x_3);
x_144 = l___private_Init_Lean_Elab_Command_3__setState(x_137, x_3, x_138);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; 
x_145 = lean_ctor_get(x_144, 1);
lean_inc(x_145);
lean_dec(x_144);
x_51 = x_133;
x_52 = x_145;
goto block_117;
}
else
{
lean_object* x_146; lean_object* x_147; 
lean_dec(x_133);
lean_dec(x_50);
lean_dec(x_48);
lean_dec(x_24);
x_146 = lean_ctor_get(x_144, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_144, 1);
lean_inc(x_147);
lean_dec(x_144);
x_35 = x_146;
x_36 = x_147;
goto block_46;
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_148 = lean_ctor_get(x_137, 2);
x_149 = lean_ctor_get(x_137, 3);
x_150 = lean_ctor_get(x_137, 4);
lean_inc(x_150);
lean_inc(x_149);
lean_inc(x_148);
lean_dec(x_137);
x_151 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_151, 0, x_139);
lean_ctor_set(x_151, 1, x_140);
lean_ctor_set(x_151, 2, x_148);
lean_ctor_set(x_151, 3, x_149);
lean_ctor_set(x_151, 4, x_150);
lean_inc(x_3);
x_152 = l___private_Init_Lean_Elab_Command_3__setState(x_151, x_3, x_138);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; 
x_153 = lean_ctor_get(x_152, 1);
lean_inc(x_153);
lean_dec(x_152);
x_51 = x_133;
x_52 = x_153;
goto block_117;
}
else
{
lean_object* x_154; lean_object* x_155; 
lean_dec(x_133);
lean_dec(x_50);
lean_dec(x_48);
lean_dec(x_24);
x_154 = lean_ctor_get(x_152, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_152, 1);
lean_inc(x_155);
lean_dec(x_152);
x_35 = x_154;
x_36 = x_155;
goto block_46;
}
}
}
else
{
lean_object* x_156; lean_object* x_157; 
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_50);
lean_dec(x_48);
lean_dec(x_24);
x_156 = lean_ctor_get(x_135, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_135, 1);
lean_inc(x_157);
lean_dec(x_135);
x_35 = x_156;
x_36 = x_157;
goto block_46;
}
}
else
{
lean_object* x_158; 
x_158 = lean_ctor_get(x_132, 0);
lean_inc(x_158);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_dec(x_50);
lean_dec(x_48);
lean_dec(x_24);
x_159 = lean_ctor_get(x_132, 1);
lean_inc(x_159);
lean_dec(x_132);
x_160 = lean_ctor_get(x_158, 0);
lean_inc(x_160);
lean_dec(x_158);
lean_inc(x_3);
x_161 = l___private_Init_Lean_Elab_Command_2__getState(x_3, x_128);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; uint8_t x_167; 
x_162 = lean_ctor_get(x_159, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_161, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_161, 1);
lean_inc(x_164);
lean_dec(x_161);
x_165 = lean_ctor_get(x_162, 0);
lean_inc(x_165);
lean_dec(x_162);
x_166 = lean_ctor_get(x_159, 2);
lean_inc(x_166);
lean_dec(x_159);
x_167 = !lean_is_exclusive(x_163);
if (x_167 == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_168 = lean_ctor_get(x_163, 1);
lean_dec(x_168);
x_169 = lean_ctor_get(x_163, 0);
lean_dec(x_169);
lean_ctor_set(x_163, 1, x_166);
lean_ctor_set(x_163, 0, x_165);
lean_inc(x_3);
x_170 = l___private_Init_Lean_Elab_Command_3__setState(x_163, x_3, x_164);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; 
x_171 = lean_ctor_get(x_170, 1);
lean_inc(x_171);
lean_dec(x_170);
x_35 = x_160;
x_36 = x_171;
goto block_46;
}
else
{
lean_object* x_172; lean_object* x_173; 
lean_dec(x_160);
x_172 = lean_ctor_get(x_170, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_170, 1);
lean_inc(x_173);
lean_dec(x_170);
x_35 = x_172;
x_36 = x_173;
goto block_46;
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_174 = lean_ctor_get(x_163, 2);
x_175 = lean_ctor_get(x_163, 3);
x_176 = lean_ctor_get(x_163, 4);
lean_inc(x_176);
lean_inc(x_175);
lean_inc(x_174);
lean_dec(x_163);
x_177 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_177, 0, x_165);
lean_ctor_set(x_177, 1, x_166);
lean_ctor_set(x_177, 2, x_174);
lean_ctor_set(x_177, 3, x_175);
lean_ctor_set(x_177, 4, x_176);
lean_inc(x_3);
x_178 = l___private_Init_Lean_Elab_Command_3__setState(x_177, x_3, x_164);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; 
x_179 = lean_ctor_get(x_178, 1);
lean_inc(x_179);
lean_dec(x_178);
x_35 = x_160;
x_36 = x_179;
goto block_46;
}
else
{
lean_object* x_180; lean_object* x_181; 
lean_dec(x_160);
x_180 = lean_ctor_get(x_178, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_178, 1);
lean_inc(x_181);
lean_dec(x_178);
x_35 = x_180;
x_36 = x_181;
goto block_46;
}
}
}
else
{
lean_object* x_182; lean_object* x_183; 
lean_dec(x_160);
lean_dec(x_159);
x_182 = lean_ctor_get(x_161, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_161, 1);
lean_inc(x_183);
lean_dec(x_161);
x_35 = x_182;
x_36 = x_183;
goto block_46;
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
lean_dec(x_132);
x_184 = l_Lean_Elab_Command_runTermElabM___rarg___closed__1;
x_185 = l_unreachable_x21___rarg(x_184);
lean_inc(x_3);
x_186 = lean_apply_2(x_185, x_3, x_128);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_187; lean_object* x_188; 
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_186, 1);
lean_inc(x_188);
lean_dec(x_186);
x_51 = x_187;
x_52 = x_188;
goto block_117;
}
else
{
lean_object* x_189; lean_object* x_190; 
lean_dec(x_50);
lean_dec(x_48);
lean_dec(x_24);
x_189 = lean_ctor_get(x_186, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_186, 1);
lean_inc(x_190);
lean_dec(x_186);
x_35 = x_189;
x_36 = x_190;
goto block_46;
}
}
}
}
else
{
lean_object* x_191; lean_object* x_192; 
lean_dec(x_125);
lean_dec(x_124);
lean_dec(x_50);
lean_dec(x_48);
lean_dec(x_24);
x_191 = lean_ctor_get(x_126, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_126, 1);
lean_inc(x_192);
lean_dec(x_126);
x_35 = x_191;
x_36 = x_192;
goto block_46;
}
}
else
{
lean_object* x_193; lean_object* x_194; 
lean_dec(x_50);
lean_dec(x_48);
lean_dec(x_24);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_1);
x_193 = lean_ctor_get(x_121, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_121, 1);
lean_inc(x_194);
lean_dec(x_121);
x_35 = x_193;
x_36 = x_194;
goto block_46;
}
}
else
{
lean_object* x_195; lean_object* x_196; 
lean_dec(x_50);
lean_dec(x_48);
lean_dec(x_24);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_1);
x_195 = lean_ctor_get(x_119, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_119, 1);
lean_inc(x_196);
lean_dec(x_119);
x_35 = x_195;
x_36 = x_196;
goto block_46;
}
block_117:
{
lean_object* x_53; 
lean_inc(x_3);
x_53 = l_Lean_Elab_Command_addDecl(x_2, x_51, x_3, x_52);
lean_dec(x_51);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; uint8_t x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
x_55 = 0;
lean_inc(x_3);
lean_inc(x_48);
x_56 = l_Array_forMAux___main___at_Lean_Elab_Command_applyAttributes___spec__1(x_2, x_48, x_55, x_50, x_12, x_3, x_54);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; uint8_t x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
lean_dec(x_56);
x_58 = 1;
lean_inc(x_3);
x_59 = l_Array_forMAux___main___at_Lean_Elab_Command_applyAttributes___spec__1(x_2, x_48, x_58, x_50, x_12, x_3, x_57);
lean_dec(x_50);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
lean_inc(x_3);
lean_inc(x_16);
x_62 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabAxiom___spec__3(x_16, x_3, x_61);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_16);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec(x_62);
lean_inc(x_3);
x_64 = l___private_Init_Lean_Elab_Command_2__getState(x_3, x_63);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = !lean_is_exclusive(x_65);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_68 = lean_ctor_get(x_65, 2);
x_69 = l_Lean_Name_getNumParts___main(x_24);
lean_dec(x_24);
x_70 = l_List_drop___main___rarg(x_69, x_68);
lean_dec(x_68);
lean_ctor_set(x_65, 2, x_70);
x_71 = l___private_Init_Lean_Elab_Command_3__setState(x_65, x_3, x_66);
if (lean_obj_tag(x_71) == 0)
{
uint8_t x_72; 
x_72 = !lean_is_exclusive(x_71);
if (x_72 == 0)
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_71, 0);
lean_dec(x_73);
lean_ctor_set(x_71, 0, x_60);
return x_71;
}
else
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_71, 1);
lean_inc(x_74);
lean_dec(x_71);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_60);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
else
{
uint8_t x_76; 
lean_dec(x_60);
x_76 = !lean_is_exclusive(x_71);
if (x_76 == 0)
{
return x_71;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_71, 0);
x_78 = lean_ctor_get(x_71, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_71);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_80 = lean_ctor_get(x_65, 0);
x_81 = lean_ctor_get(x_65, 1);
x_82 = lean_ctor_get(x_65, 2);
x_83 = lean_ctor_get(x_65, 3);
x_84 = lean_ctor_get(x_65, 4);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_65);
x_85 = l_Lean_Name_getNumParts___main(x_24);
lean_dec(x_24);
x_86 = l_List_drop___main___rarg(x_85, x_82);
lean_dec(x_82);
x_87 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_87, 0, x_80);
lean_ctor_set(x_87, 1, x_81);
lean_ctor_set(x_87, 2, x_86);
lean_ctor_set(x_87, 3, x_83);
lean_ctor_set(x_87, 4, x_84);
x_88 = l___private_Init_Lean_Elab_Command_3__setState(x_87, x_3, x_66);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_90 = x_88;
} else {
 lean_dec_ref(x_88);
 x_90 = lean_box(0);
}
if (lean_is_scalar(x_90)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_90;
}
lean_ctor_set(x_91, 0, x_60);
lean_ctor_set(x_91, 1, x_89);
return x_91;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_60);
x_92 = lean_ctor_get(x_88, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_88, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_94 = x_88;
} else {
 lean_dec_ref(x_88);
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
}
else
{
uint8_t x_96; 
lean_dec(x_60);
lean_dec(x_24);
lean_dec(x_3);
x_96 = !lean_is_exclusive(x_64);
if (x_96 == 0)
{
return x_64;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_64, 0);
x_98 = lean_ctor_get(x_64, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_64);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_60);
lean_dec(x_24);
x_100 = lean_ctor_get(x_62, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_62, 1);
lean_inc(x_101);
lean_dec(x_62);
x_102 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabAxiom___spec__4(x_16, x_3, x_101);
if (lean_obj_tag(x_102) == 0)
{
uint8_t x_103; 
x_103 = !lean_is_exclusive(x_102);
if (x_103 == 0)
{
lean_object* x_104; 
x_104 = lean_ctor_get(x_102, 0);
lean_dec(x_104);
lean_ctor_set_tag(x_102, 1);
lean_ctor_set(x_102, 0, x_100);
return x_102;
}
else
{
lean_object* x_105; lean_object* x_106; 
x_105 = lean_ctor_get(x_102, 1);
lean_inc(x_105);
lean_dec(x_102);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_100);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
}
else
{
uint8_t x_107; 
lean_dec(x_100);
x_107 = !lean_is_exclusive(x_102);
if (x_107 == 0)
{
return x_102;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_102, 0);
x_109 = lean_ctor_get(x_102, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_102);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
}
}
}
else
{
lean_object* x_111; lean_object* x_112; 
lean_dec(x_24);
x_111 = lean_ctor_get(x_59, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_59, 1);
lean_inc(x_112);
lean_dec(x_59);
x_35 = x_111;
x_36 = x_112;
goto block_46;
}
}
else
{
lean_object* x_113; lean_object* x_114; 
lean_dec(x_50);
lean_dec(x_48);
lean_dec(x_24);
x_113 = lean_ctor_get(x_56, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_56, 1);
lean_inc(x_114);
lean_dec(x_56);
x_35 = x_113;
x_36 = x_114;
goto block_46;
}
}
else
{
lean_object* x_115; lean_object* x_116; 
lean_dec(x_50);
lean_dec(x_48);
lean_dec(x_24);
x_115 = lean_ctor_get(x_53, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_53, 1);
lean_inc(x_116);
lean_dec(x_53);
x_35 = x_115;
x_36 = x_116;
goto block_46;
}
}
}
else
{
lean_object* x_197; lean_object* x_198; 
lean_dec(x_24);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_1);
x_197 = lean_ctor_get(x_47, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_47, 1);
lean_inc(x_198);
lean_dec(x_47);
x_35 = x_197;
x_36 = x_198;
goto block_46;
}
block_46:
{
lean_object* x_37; 
x_37 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabAxiom___spec__2(x_16, x_3, x_36);
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_37, 0);
lean_dec(x_39);
lean_ctor_set_tag(x_37, 1);
lean_ctor_set(x_37, 0, x_35);
return x_37;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_35);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
else
{
uint8_t x_42; 
lean_dec(x_35);
x_42 = !lean_is_exclusive(x_37);
if (x_42 == 0)
{
return x_37;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_37, 0);
x_44 = lean_ctor_get(x_37, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_37);
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
uint8_t x_199; 
lean_dec(x_28);
lean_dec(x_24);
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_1);
x_199 = !lean_is_exclusive(x_33);
if (x_199 == 0)
{
return x_33;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_200 = lean_ctor_get(x_33, 0);
x_201 = lean_ctor_get(x_33, 1);
lean_inc(x_201);
lean_inc(x_200);
lean_dec(x_33);
x_202 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_202, 0, x_200);
lean_ctor_set(x_202, 1, x_201);
return x_202;
}
}
}
else
{
uint8_t x_203; 
lean_dec(x_28);
lean_dec(x_24);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_1);
x_203 = !lean_is_exclusive(x_31);
if (x_203 == 0)
{
return x_31;
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_204 = lean_ctor_get(x_31, 0);
x_205 = lean_ctor_get(x_31, 1);
lean_inc(x_205);
lean_inc(x_204);
lean_dec(x_31);
x_206 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_206, 0, x_204);
lean_ctor_set(x_206, 1, x_205);
return x_206;
}
}
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; uint8_t x_217; lean_object* x_218; 
x_207 = lean_ctor_get(x_20, 1);
x_208 = lean_ctor_get(x_20, 2);
x_209 = lean_ctor_get(x_20, 3);
lean_inc(x_209);
lean_inc(x_208);
lean_inc(x_207);
lean_dec(x_20);
x_210 = lean_ctor_get(x_21, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_21, 1);
lean_inc(x_211);
lean_dec(x_21);
x_212 = lean_box(0);
x_213 = lean_name_mk_string(x_212, x_211);
x_214 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set(x_214, 1, x_207);
lean_ctor_set(x_214, 2, x_208);
lean_ctor_set(x_214, 3, x_209);
x_215 = l_Lean_MacroScopesView_review(x_214);
x_216 = l_Lean_Parser_Command_namespace___elambda__1___closed__1;
x_217 = 1;
lean_inc(x_3);
lean_inc(x_210);
x_218 = l___private_Init_Lean_Elab_Command_12__addScopes___main(x_6, x_216, x_217, x_210, x_3, x_19);
lean_dec(x_6);
if (lean_obj_tag(x_218) == 0)
{
lean_object* x_219; lean_object* x_220; 
x_219 = lean_ctor_get(x_218, 1);
lean_inc(x_219);
lean_dec(x_218);
lean_inc(x_3);
x_220 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabAxiom___spec__1(x_18, x_3, x_219);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_233; 
x_221 = lean_ctor_get(x_220, 1);
lean_inc(x_221);
lean_dec(x_220);
lean_inc(x_3);
x_233 = l_Lean_Elab_Command_mkDeclName(x_1, x_215, x_3, x_221);
if (lean_obj_tag(x_233) == 0)
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; uint8_t x_291; lean_object* x_292; 
x_234 = lean_ctor_get(x_233, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_233, 1);
lean_inc(x_235);
lean_dec(x_233);
x_236 = lean_ctor_get(x_1, 1);
lean_inc(x_236);
x_291 = 2;
lean_inc(x_3);
lean_inc(x_234);
x_292 = l_Array_forMAux___main___at_Lean_Elab_Command_applyAttributes___spec__1(x_2, x_234, x_291, x_236, x_12, x_3, x_235);
if (lean_obj_tag(x_292) == 0)
{
lean_object* x_293; lean_object* x_294; 
x_293 = lean_ctor_get(x_292, 1);
lean_inc(x_293);
lean_dec(x_292);
lean_inc(x_3);
x_294 = l_Lean_Elab_Command_getLevelNames(x_3, x_293);
if (lean_obj_tag(x_294) == 0)
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; 
x_295 = lean_ctor_get(x_294, 0);
lean_inc(x_295);
x_296 = lean_ctor_get(x_294, 1);
lean_inc(x_296);
lean_dec(x_294);
lean_inc(x_234);
x_297 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_297, 0, x_234);
lean_inc(x_234);
x_298 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabAxiom___lambda__2___boxed), 8, 5);
lean_closure_set(x_298, 0, x_10);
lean_closure_set(x_298, 1, x_11);
lean_closure_set(x_298, 2, x_295);
lean_closure_set(x_298, 3, x_234);
lean_closure_set(x_298, 4, x_1);
lean_inc(x_3);
x_299 = l___private_Init_Lean_Elab_Command_2__getState(x_3, x_296);
if (lean_obj_tag(x_299) == 0)
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; 
x_300 = lean_ctor_get(x_299, 0);
lean_inc(x_300);
x_301 = lean_ctor_get(x_299, 1);
lean_inc(x_301);
lean_dec(x_299);
x_302 = l___private_Init_Lean_Elab_Command_9__getVarDecls(x_300);
x_303 = l___private_Init_Lean_Elab_Command_6__mkTermContext(x_3, x_300, x_297);
x_304 = l___private_Init_Lean_Elab_Command_7__mkTermState(x_300);
lean_dec(x_300);
x_305 = l_Lean_Elab_Term_elabBinders___rarg(x_302, x_298, x_303, x_304);
lean_dec(x_302);
if (lean_obj_tag(x_305) == 0)
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; 
x_306 = lean_ctor_get(x_305, 0);
lean_inc(x_306);
x_307 = lean_ctor_get(x_305, 1);
lean_inc(x_307);
lean_dec(x_305);
lean_inc(x_3);
x_308 = l___private_Init_Lean_Elab_Command_2__getState(x_3, x_301);
if (lean_obj_tag(x_308) == 0)
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; 
x_309 = lean_ctor_get(x_307, 0);
lean_inc(x_309);
x_310 = lean_ctor_get(x_308, 0);
lean_inc(x_310);
x_311 = lean_ctor_get(x_308, 1);
lean_inc(x_311);
lean_dec(x_308);
x_312 = lean_ctor_get(x_309, 0);
lean_inc(x_312);
lean_dec(x_309);
x_313 = lean_ctor_get(x_307, 2);
lean_inc(x_313);
lean_dec(x_307);
x_314 = lean_ctor_get(x_310, 2);
lean_inc(x_314);
x_315 = lean_ctor_get(x_310, 3);
lean_inc(x_315);
x_316 = lean_ctor_get(x_310, 4);
lean_inc(x_316);
if (lean_is_exclusive(x_310)) {
 lean_ctor_release(x_310, 0);
 lean_ctor_release(x_310, 1);
 lean_ctor_release(x_310, 2);
 lean_ctor_release(x_310, 3);
 lean_ctor_release(x_310, 4);
 x_317 = x_310;
} else {
 lean_dec_ref(x_310);
 x_317 = lean_box(0);
}
if (lean_is_scalar(x_317)) {
 x_318 = lean_alloc_ctor(0, 5, 0);
} else {
 x_318 = x_317;
}
lean_ctor_set(x_318, 0, x_312);
lean_ctor_set(x_318, 1, x_313);
lean_ctor_set(x_318, 2, x_314);
lean_ctor_set(x_318, 3, x_315);
lean_ctor_set(x_318, 4, x_316);
lean_inc(x_3);
x_319 = l___private_Init_Lean_Elab_Command_3__setState(x_318, x_3, x_311);
if (lean_obj_tag(x_319) == 0)
{
lean_object* x_320; 
x_320 = lean_ctor_get(x_319, 1);
lean_inc(x_320);
lean_dec(x_319);
x_237 = x_306;
x_238 = x_320;
goto block_290;
}
else
{
lean_object* x_321; lean_object* x_322; 
lean_dec(x_306);
lean_dec(x_236);
lean_dec(x_234);
lean_dec(x_210);
x_321 = lean_ctor_get(x_319, 0);
lean_inc(x_321);
x_322 = lean_ctor_get(x_319, 1);
lean_inc(x_322);
lean_dec(x_319);
x_222 = x_321;
x_223 = x_322;
goto block_232;
}
}
else
{
lean_object* x_323; lean_object* x_324; 
lean_dec(x_307);
lean_dec(x_306);
lean_dec(x_236);
lean_dec(x_234);
lean_dec(x_210);
x_323 = lean_ctor_get(x_308, 0);
lean_inc(x_323);
x_324 = lean_ctor_get(x_308, 1);
lean_inc(x_324);
lean_dec(x_308);
x_222 = x_323;
x_223 = x_324;
goto block_232;
}
}
else
{
lean_object* x_325; 
x_325 = lean_ctor_get(x_305, 0);
lean_inc(x_325);
if (lean_obj_tag(x_325) == 0)
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; 
lean_dec(x_236);
lean_dec(x_234);
lean_dec(x_210);
x_326 = lean_ctor_get(x_305, 1);
lean_inc(x_326);
lean_dec(x_305);
x_327 = lean_ctor_get(x_325, 0);
lean_inc(x_327);
lean_dec(x_325);
lean_inc(x_3);
x_328 = l___private_Init_Lean_Elab_Command_2__getState(x_3, x_301);
if (lean_obj_tag(x_328) == 0)
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; 
x_329 = lean_ctor_get(x_326, 0);
lean_inc(x_329);
x_330 = lean_ctor_get(x_328, 0);
lean_inc(x_330);
x_331 = lean_ctor_get(x_328, 1);
lean_inc(x_331);
lean_dec(x_328);
x_332 = lean_ctor_get(x_329, 0);
lean_inc(x_332);
lean_dec(x_329);
x_333 = lean_ctor_get(x_326, 2);
lean_inc(x_333);
lean_dec(x_326);
x_334 = lean_ctor_get(x_330, 2);
lean_inc(x_334);
x_335 = lean_ctor_get(x_330, 3);
lean_inc(x_335);
x_336 = lean_ctor_get(x_330, 4);
lean_inc(x_336);
if (lean_is_exclusive(x_330)) {
 lean_ctor_release(x_330, 0);
 lean_ctor_release(x_330, 1);
 lean_ctor_release(x_330, 2);
 lean_ctor_release(x_330, 3);
 lean_ctor_release(x_330, 4);
 x_337 = x_330;
} else {
 lean_dec_ref(x_330);
 x_337 = lean_box(0);
}
if (lean_is_scalar(x_337)) {
 x_338 = lean_alloc_ctor(0, 5, 0);
} else {
 x_338 = x_337;
}
lean_ctor_set(x_338, 0, x_332);
lean_ctor_set(x_338, 1, x_333);
lean_ctor_set(x_338, 2, x_334);
lean_ctor_set(x_338, 3, x_335);
lean_ctor_set(x_338, 4, x_336);
lean_inc(x_3);
x_339 = l___private_Init_Lean_Elab_Command_3__setState(x_338, x_3, x_331);
if (lean_obj_tag(x_339) == 0)
{
lean_object* x_340; 
x_340 = lean_ctor_get(x_339, 1);
lean_inc(x_340);
lean_dec(x_339);
x_222 = x_327;
x_223 = x_340;
goto block_232;
}
else
{
lean_object* x_341; lean_object* x_342; 
lean_dec(x_327);
x_341 = lean_ctor_get(x_339, 0);
lean_inc(x_341);
x_342 = lean_ctor_get(x_339, 1);
lean_inc(x_342);
lean_dec(x_339);
x_222 = x_341;
x_223 = x_342;
goto block_232;
}
}
else
{
lean_object* x_343; lean_object* x_344; 
lean_dec(x_327);
lean_dec(x_326);
x_343 = lean_ctor_get(x_328, 0);
lean_inc(x_343);
x_344 = lean_ctor_get(x_328, 1);
lean_inc(x_344);
lean_dec(x_328);
x_222 = x_343;
x_223 = x_344;
goto block_232;
}
}
else
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; 
lean_dec(x_305);
x_345 = l_Lean_Elab_Command_runTermElabM___rarg___closed__1;
x_346 = l_unreachable_x21___rarg(x_345);
lean_inc(x_3);
x_347 = lean_apply_2(x_346, x_3, x_301);
if (lean_obj_tag(x_347) == 0)
{
lean_object* x_348; lean_object* x_349; 
x_348 = lean_ctor_get(x_347, 0);
lean_inc(x_348);
x_349 = lean_ctor_get(x_347, 1);
lean_inc(x_349);
lean_dec(x_347);
x_237 = x_348;
x_238 = x_349;
goto block_290;
}
else
{
lean_object* x_350; lean_object* x_351; 
lean_dec(x_236);
lean_dec(x_234);
lean_dec(x_210);
x_350 = lean_ctor_get(x_347, 0);
lean_inc(x_350);
x_351 = lean_ctor_get(x_347, 1);
lean_inc(x_351);
lean_dec(x_347);
x_222 = x_350;
x_223 = x_351;
goto block_232;
}
}
}
}
else
{
lean_object* x_352; lean_object* x_353; 
lean_dec(x_298);
lean_dec(x_297);
lean_dec(x_236);
lean_dec(x_234);
lean_dec(x_210);
x_352 = lean_ctor_get(x_299, 0);
lean_inc(x_352);
x_353 = lean_ctor_get(x_299, 1);
lean_inc(x_353);
lean_dec(x_299);
x_222 = x_352;
x_223 = x_353;
goto block_232;
}
}
else
{
lean_object* x_354; lean_object* x_355; 
lean_dec(x_236);
lean_dec(x_234);
lean_dec(x_210);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_1);
x_354 = lean_ctor_get(x_294, 0);
lean_inc(x_354);
x_355 = lean_ctor_get(x_294, 1);
lean_inc(x_355);
lean_dec(x_294);
x_222 = x_354;
x_223 = x_355;
goto block_232;
}
}
else
{
lean_object* x_356; lean_object* x_357; 
lean_dec(x_236);
lean_dec(x_234);
lean_dec(x_210);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_1);
x_356 = lean_ctor_get(x_292, 0);
lean_inc(x_356);
x_357 = lean_ctor_get(x_292, 1);
lean_inc(x_357);
lean_dec(x_292);
x_222 = x_356;
x_223 = x_357;
goto block_232;
}
block_290:
{
lean_object* x_239; 
lean_inc(x_3);
x_239 = l_Lean_Elab_Command_addDecl(x_2, x_237, x_3, x_238);
lean_dec(x_237);
if (lean_obj_tag(x_239) == 0)
{
lean_object* x_240; uint8_t x_241; lean_object* x_242; 
x_240 = lean_ctor_get(x_239, 1);
lean_inc(x_240);
lean_dec(x_239);
x_241 = 0;
lean_inc(x_3);
lean_inc(x_234);
x_242 = l_Array_forMAux___main___at_Lean_Elab_Command_applyAttributes___spec__1(x_2, x_234, x_241, x_236, x_12, x_3, x_240);
if (lean_obj_tag(x_242) == 0)
{
lean_object* x_243; uint8_t x_244; lean_object* x_245; 
x_243 = lean_ctor_get(x_242, 1);
lean_inc(x_243);
lean_dec(x_242);
x_244 = 1;
lean_inc(x_3);
x_245 = l_Array_forMAux___main___at_Lean_Elab_Command_applyAttributes___spec__1(x_2, x_234, x_244, x_236, x_12, x_3, x_243);
lean_dec(x_236);
if (lean_obj_tag(x_245) == 0)
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_246 = lean_ctor_get(x_245, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_245, 1);
lean_inc(x_247);
lean_dec(x_245);
lean_inc(x_3);
lean_inc(x_16);
x_248 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabAxiom___spec__3(x_16, x_3, x_247);
if (lean_obj_tag(x_248) == 0)
{
lean_object* x_249; lean_object* x_250; 
lean_dec(x_16);
x_249 = lean_ctor_get(x_248, 1);
lean_inc(x_249);
lean_dec(x_248);
lean_inc(x_3);
x_250 = l___private_Init_Lean_Elab_Command_2__getState(x_3, x_249);
if (lean_obj_tag(x_250) == 0)
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
x_251 = lean_ctor_get(x_250, 0);
lean_inc(x_251);
x_252 = lean_ctor_get(x_250, 1);
lean_inc(x_252);
lean_dec(x_250);
x_253 = lean_ctor_get(x_251, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_251, 1);
lean_inc(x_254);
x_255 = lean_ctor_get(x_251, 2);
lean_inc(x_255);
x_256 = lean_ctor_get(x_251, 3);
lean_inc(x_256);
x_257 = lean_ctor_get(x_251, 4);
lean_inc(x_257);
if (lean_is_exclusive(x_251)) {
 lean_ctor_release(x_251, 0);
 lean_ctor_release(x_251, 1);
 lean_ctor_release(x_251, 2);
 lean_ctor_release(x_251, 3);
 lean_ctor_release(x_251, 4);
 x_258 = x_251;
} else {
 lean_dec_ref(x_251);
 x_258 = lean_box(0);
}
x_259 = l_Lean_Name_getNumParts___main(x_210);
lean_dec(x_210);
x_260 = l_List_drop___main___rarg(x_259, x_255);
lean_dec(x_255);
if (lean_is_scalar(x_258)) {
 x_261 = lean_alloc_ctor(0, 5, 0);
} else {
 x_261 = x_258;
}
lean_ctor_set(x_261, 0, x_253);
lean_ctor_set(x_261, 1, x_254);
lean_ctor_set(x_261, 2, x_260);
lean_ctor_set(x_261, 3, x_256);
lean_ctor_set(x_261, 4, x_257);
x_262 = l___private_Init_Lean_Elab_Command_3__setState(x_261, x_3, x_252);
if (lean_obj_tag(x_262) == 0)
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_263 = lean_ctor_get(x_262, 1);
lean_inc(x_263);
if (lean_is_exclusive(x_262)) {
 lean_ctor_release(x_262, 0);
 lean_ctor_release(x_262, 1);
 x_264 = x_262;
} else {
 lean_dec_ref(x_262);
 x_264 = lean_box(0);
}
if (lean_is_scalar(x_264)) {
 x_265 = lean_alloc_ctor(0, 2, 0);
} else {
 x_265 = x_264;
}
lean_ctor_set(x_265, 0, x_246);
lean_ctor_set(x_265, 1, x_263);
return x_265;
}
else
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
lean_dec(x_246);
x_266 = lean_ctor_get(x_262, 0);
lean_inc(x_266);
x_267 = lean_ctor_get(x_262, 1);
lean_inc(x_267);
if (lean_is_exclusive(x_262)) {
 lean_ctor_release(x_262, 0);
 lean_ctor_release(x_262, 1);
 x_268 = x_262;
} else {
 lean_dec_ref(x_262);
 x_268 = lean_box(0);
}
if (lean_is_scalar(x_268)) {
 x_269 = lean_alloc_ctor(1, 2, 0);
} else {
 x_269 = x_268;
}
lean_ctor_set(x_269, 0, x_266);
lean_ctor_set(x_269, 1, x_267);
return x_269;
}
}
else
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; 
lean_dec(x_246);
lean_dec(x_210);
lean_dec(x_3);
x_270 = lean_ctor_get(x_250, 0);
lean_inc(x_270);
x_271 = lean_ctor_get(x_250, 1);
lean_inc(x_271);
if (lean_is_exclusive(x_250)) {
 lean_ctor_release(x_250, 0);
 lean_ctor_release(x_250, 1);
 x_272 = x_250;
} else {
 lean_dec_ref(x_250);
 x_272 = lean_box(0);
}
if (lean_is_scalar(x_272)) {
 x_273 = lean_alloc_ctor(1, 2, 0);
} else {
 x_273 = x_272;
}
lean_ctor_set(x_273, 0, x_270);
lean_ctor_set(x_273, 1, x_271);
return x_273;
}
}
else
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; 
lean_dec(x_246);
lean_dec(x_210);
x_274 = lean_ctor_get(x_248, 0);
lean_inc(x_274);
x_275 = lean_ctor_get(x_248, 1);
lean_inc(x_275);
lean_dec(x_248);
x_276 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabAxiom___spec__4(x_16, x_3, x_275);
if (lean_obj_tag(x_276) == 0)
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_277 = lean_ctor_get(x_276, 1);
lean_inc(x_277);
if (lean_is_exclusive(x_276)) {
 lean_ctor_release(x_276, 0);
 lean_ctor_release(x_276, 1);
 x_278 = x_276;
} else {
 lean_dec_ref(x_276);
 x_278 = lean_box(0);
}
if (lean_is_scalar(x_278)) {
 x_279 = lean_alloc_ctor(1, 2, 0);
} else {
 x_279 = x_278;
 lean_ctor_set_tag(x_279, 1);
}
lean_ctor_set(x_279, 0, x_274);
lean_ctor_set(x_279, 1, x_277);
return x_279;
}
else
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; 
lean_dec(x_274);
x_280 = lean_ctor_get(x_276, 0);
lean_inc(x_280);
x_281 = lean_ctor_get(x_276, 1);
lean_inc(x_281);
if (lean_is_exclusive(x_276)) {
 lean_ctor_release(x_276, 0);
 lean_ctor_release(x_276, 1);
 x_282 = x_276;
} else {
 lean_dec_ref(x_276);
 x_282 = lean_box(0);
}
if (lean_is_scalar(x_282)) {
 x_283 = lean_alloc_ctor(1, 2, 0);
} else {
 x_283 = x_282;
}
lean_ctor_set(x_283, 0, x_280);
lean_ctor_set(x_283, 1, x_281);
return x_283;
}
}
}
else
{
lean_object* x_284; lean_object* x_285; 
lean_dec(x_210);
x_284 = lean_ctor_get(x_245, 0);
lean_inc(x_284);
x_285 = lean_ctor_get(x_245, 1);
lean_inc(x_285);
lean_dec(x_245);
x_222 = x_284;
x_223 = x_285;
goto block_232;
}
}
else
{
lean_object* x_286; lean_object* x_287; 
lean_dec(x_236);
lean_dec(x_234);
lean_dec(x_210);
x_286 = lean_ctor_get(x_242, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_242, 1);
lean_inc(x_287);
lean_dec(x_242);
x_222 = x_286;
x_223 = x_287;
goto block_232;
}
}
else
{
lean_object* x_288; lean_object* x_289; 
lean_dec(x_236);
lean_dec(x_234);
lean_dec(x_210);
x_288 = lean_ctor_get(x_239, 0);
lean_inc(x_288);
x_289 = lean_ctor_get(x_239, 1);
lean_inc(x_289);
lean_dec(x_239);
x_222 = x_288;
x_223 = x_289;
goto block_232;
}
}
}
else
{
lean_object* x_358; lean_object* x_359; 
lean_dec(x_210);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_1);
x_358 = lean_ctor_get(x_233, 0);
lean_inc(x_358);
x_359 = lean_ctor_get(x_233, 1);
lean_inc(x_359);
lean_dec(x_233);
x_222 = x_358;
x_223 = x_359;
goto block_232;
}
block_232:
{
lean_object* x_224; 
x_224 = l_Lean_Elab_Command_modifyScope___at_Lean_Elab_Command_elabAxiom___spec__2(x_16, x_3, x_223);
if (lean_obj_tag(x_224) == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_225 = lean_ctor_get(x_224, 1);
lean_inc(x_225);
if (lean_is_exclusive(x_224)) {
 lean_ctor_release(x_224, 0);
 lean_ctor_release(x_224, 1);
 x_226 = x_224;
} else {
 lean_dec_ref(x_224);
 x_226 = lean_box(0);
}
if (lean_is_scalar(x_226)) {
 x_227 = lean_alloc_ctor(1, 2, 0);
} else {
 x_227 = x_226;
 lean_ctor_set_tag(x_227, 1);
}
lean_ctor_set(x_227, 0, x_222);
lean_ctor_set(x_227, 1, x_225);
return x_227;
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
lean_dec(x_222);
x_228 = lean_ctor_get(x_224, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_224, 1);
lean_inc(x_229);
if (lean_is_exclusive(x_224)) {
 lean_ctor_release(x_224, 0);
 lean_ctor_release(x_224, 1);
 x_230 = x_224;
} else {
 lean_dec_ref(x_224);
 x_230 = lean_box(0);
}
if (lean_is_scalar(x_230)) {
 x_231 = lean_alloc_ctor(1, 2, 0);
} else {
 x_231 = x_230;
}
lean_ctor_set(x_231, 0, x_228);
lean_ctor_set(x_231, 1, x_229);
return x_231;
}
}
}
else
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; 
lean_dec(x_215);
lean_dec(x_210);
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_1);
x_360 = lean_ctor_get(x_220, 0);
lean_inc(x_360);
x_361 = lean_ctor_get(x_220, 1);
lean_inc(x_361);
if (lean_is_exclusive(x_220)) {
 lean_ctor_release(x_220, 0);
 lean_ctor_release(x_220, 1);
 x_362 = x_220;
} else {
 lean_dec_ref(x_220);
 x_362 = lean_box(0);
}
if (lean_is_scalar(x_362)) {
 x_363 = lean_alloc_ctor(1, 2, 0);
} else {
 x_363 = x_362;
}
lean_ctor_set(x_363, 0, x_360);
lean_ctor_set(x_363, 1, x_361);
return x_363;
}
}
else
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; 
lean_dec(x_215);
lean_dec(x_210);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_1);
x_364 = lean_ctor_get(x_218, 0);
lean_inc(x_364);
x_365 = lean_ctor_get(x_218, 1);
lean_inc(x_365);
if (lean_is_exclusive(x_218)) {
 lean_ctor_release(x_218, 0);
 lean_ctor_release(x_218, 1);
 x_366 = x_218;
} else {
 lean_dec_ref(x_218);
 x_366 = lean_box(0);
}
if (lean_is_scalar(x_366)) {
 x_367 = lean_alloc_ctor(1, 2, 0);
} else {
 x_367 = x_366;
}
lean_ctor_set(x_367, 0, x_364);
lean_ctor_set(x_367, 1, x_365);
return x_367;
}
}
}
else
{
lean_object* x_368; lean_object* x_369; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_1);
x_368 = l_Lean_Elab_Command_withDeclId___closed__3;
x_369 = l_Lean_Elab_Command_throwError___rarg(x_6, x_368, x_3, x_19);
lean_dec(x_6);
return x_369;
}
}
}
else
{
uint8_t x_383; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_383 = !lean_is_exclusive(x_15);
if (x_383 == 0)
{
return x_15;
}
else
{
lean_object* x_384; lean_object* x_385; lean_object* x_386; 
x_384 = lean_ctor_get(x_15, 0);
x_385 = lean_ctor_get(x_15, 1);
lean_inc(x_385);
lean_inc(x_384);
lean_dec(x_15);
x_386 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_386, 0, x_384);
lean_ctor_set(x_386, 1, x_385);
return x_386;
}
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Command_elabAxiom___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_iterateMAux___main___at_Lean_Elab_Command_elabAxiom___spec__5(x_1, x_2, x_3, x_4, x_5, x_6);
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_Syntax_getArg(x_1, x_4);
lean_inc(x_2);
x_6 = l_Lean_Elab_Command_elabModifiers(x_5, x_2, x_3);
lean_dec(x_5);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = lean_unsigned_to_nat(1u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
lean_inc(x_11);
x_12 = l_Lean_Syntax_getKind(x_11);
x_13 = l_Lean_Parser_Command_abbrev___elambda__1___closed__2;
x_14 = lean_name_eq(x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = l_Lean_Parser_Command_def___elambda__1___closed__2;
x_16 = lean_name_eq(x_12, x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Lean_Parser_Command_theorem___elambda__1___closed__2;
x_18 = lean_name_eq(x_12, x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = l_Lean_Parser_Command_constant___elambda__1___closed__2;
x_20 = lean_name_eq(x_12, x_19);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = l_Lean_Elab_Command_elabDeclaration___closed__1;
x_22 = lean_name_eq(x_12, x_21);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = l_Lean_Parser_Command_axiom___elambda__1___closed__2;
x_24 = lean_name_eq(x_12, x_23);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = l_Lean_Parser_Command_example___elambda__1___closed__2;
x_26 = lean_name_eq(x_12, x_25);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
lean_dec(x_11);
lean_dec(x_8);
x_27 = l_Lean_Parser_Command_inductive___elambda__1___closed__2;
x_28 = lean_name_eq(x_12, x_27);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = l_Lean_Parser_Command_classInductive___elambda__1___closed__2;
x_30 = lean_name_eq(x_12, x_29);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = l_Lean_Parser_Command_structure___elambda__1___closed__2;
x_32 = lean_name_eq(x_12, x_31);
lean_dec(x_12);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_free_object(x_6);
x_33 = l_Lean_Elab_Command_elabDeclaration___closed__4;
x_34 = l_Lean_Elab_Command_throwError___rarg(x_1, x_33, x_2, x_9);
return x_34;
}
else
{
lean_object* x_35; 
lean_dec(x_2);
x_35 = lean_box(0);
lean_ctor_set(x_6, 0, x_35);
return x_6;
}
}
else
{
lean_object* x_36; 
lean_dec(x_12);
lean_dec(x_2);
x_36 = lean_box(0);
lean_ctor_set(x_6, 0, x_36);
return x_6;
}
}
else
{
lean_object* x_37; 
lean_dec(x_12);
lean_dec(x_2);
x_37 = lean_box(0);
lean_ctor_set(x_6, 0, x_37);
return x_6;
}
}
else
{
lean_object* x_38; 
lean_dec(x_12);
lean_free_object(x_6);
x_38 = l_Lean_Elab_Command_elabExample(x_8, x_11, x_2, x_9);
return x_38;
}
}
else
{
lean_object* x_39; 
lean_dec(x_12);
lean_free_object(x_6);
x_39 = l_Lean_Elab_Command_elabAxiom(x_8, x_11, x_2, x_9);
lean_dec(x_11);
return x_39;
}
}
else
{
lean_object* x_40; 
lean_dec(x_12);
lean_free_object(x_6);
x_40 = l_Lean_Elab_Command_elabInstance(x_8, x_11, x_2, x_9);
return x_40;
}
}
else
{
lean_object* x_41; 
lean_dec(x_12);
lean_free_object(x_6);
x_41 = l_Lean_Elab_Command_elabConstant(x_8, x_11, x_2, x_9);
return x_41;
}
}
else
{
lean_object* x_42; 
lean_dec(x_12);
lean_free_object(x_6);
x_42 = l_Lean_Elab_Command_elabTheorem(x_8, x_11, x_2, x_9);
return x_42;
}
}
else
{
lean_object* x_43; 
lean_dec(x_12);
lean_free_object(x_6);
x_43 = l_Lean_Elab_Command_elabDef(x_8, x_11, x_2, x_9);
return x_43;
}
}
else
{
lean_object* x_44; 
lean_dec(x_12);
lean_free_object(x_6);
x_44 = l_Lean_Elab_Command_elabAbbrev(x_8, x_11, x_2, x_9);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_45 = lean_ctor_get(x_6, 0);
x_46 = lean_ctor_get(x_6, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_6);
x_47 = lean_unsigned_to_nat(1u);
x_48 = l_Lean_Syntax_getArg(x_1, x_47);
lean_inc(x_48);
x_49 = l_Lean_Syntax_getKind(x_48);
x_50 = l_Lean_Parser_Command_abbrev___elambda__1___closed__2;
x_51 = lean_name_eq(x_49, x_50);
if (x_51 == 0)
{
lean_object* x_52; uint8_t x_53; 
x_52 = l_Lean_Parser_Command_def___elambda__1___closed__2;
x_53 = lean_name_eq(x_49, x_52);
if (x_53 == 0)
{
lean_object* x_54; uint8_t x_55; 
x_54 = l_Lean_Parser_Command_theorem___elambda__1___closed__2;
x_55 = lean_name_eq(x_49, x_54);
if (x_55 == 0)
{
lean_object* x_56; uint8_t x_57; 
x_56 = l_Lean_Parser_Command_constant___elambda__1___closed__2;
x_57 = lean_name_eq(x_49, x_56);
if (x_57 == 0)
{
lean_object* x_58; uint8_t x_59; 
x_58 = l_Lean_Elab_Command_elabDeclaration___closed__1;
x_59 = lean_name_eq(x_49, x_58);
if (x_59 == 0)
{
lean_object* x_60; uint8_t x_61; 
x_60 = l_Lean_Parser_Command_axiom___elambda__1___closed__2;
x_61 = lean_name_eq(x_49, x_60);
if (x_61 == 0)
{
lean_object* x_62; uint8_t x_63; 
x_62 = l_Lean_Parser_Command_example___elambda__1___closed__2;
x_63 = lean_name_eq(x_49, x_62);
if (x_63 == 0)
{
lean_object* x_64; uint8_t x_65; 
lean_dec(x_48);
lean_dec(x_45);
x_64 = l_Lean_Parser_Command_inductive___elambda__1___closed__2;
x_65 = lean_name_eq(x_49, x_64);
if (x_65 == 0)
{
lean_object* x_66; uint8_t x_67; 
x_66 = l_Lean_Parser_Command_classInductive___elambda__1___closed__2;
x_67 = lean_name_eq(x_49, x_66);
if (x_67 == 0)
{
lean_object* x_68; uint8_t x_69; 
x_68 = l_Lean_Parser_Command_structure___elambda__1___closed__2;
x_69 = lean_name_eq(x_49, x_68);
lean_dec(x_49);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; 
x_70 = l_Lean_Elab_Command_elabDeclaration___closed__4;
x_71 = l_Lean_Elab_Command_throwError___rarg(x_1, x_70, x_2, x_46);
return x_71;
}
else
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_2);
x_72 = lean_box(0);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_46);
return x_73;
}
}
else
{
lean_object* x_74; lean_object* x_75; 
lean_dec(x_49);
lean_dec(x_2);
x_74 = lean_box(0);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_46);
return x_75;
}
}
else
{
lean_object* x_76; lean_object* x_77; 
lean_dec(x_49);
lean_dec(x_2);
x_76 = lean_box(0);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_46);
return x_77;
}
}
else
{
lean_object* x_78; 
lean_dec(x_49);
x_78 = l_Lean_Elab_Command_elabExample(x_45, x_48, x_2, x_46);
return x_78;
}
}
else
{
lean_object* x_79; 
lean_dec(x_49);
x_79 = l_Lean_Elab_Command_elabAxiom(x_45, x_48, x_2, x_46);
lean_dec(x_48);
return x_79;
}
}
else
{
lean_object* x_80; 
lean_dec(x_49);
x_80 = l_Lean_Elab_Command_elabInstance(x_45, x_48, x_2, x_46);
return x_80;
}
}
else
{
lean_object* x_81; 
lean_dec(x_49);
x_81 = l_Lean_Elab_Command_elabConstant(x_45, x_48, x_2, x_46);
return x_81;
}
}
else
{
lean_object* x_82; 
lean_dec(x_49);
x_82 = l_Lean_Elab_Command_elabTheorem(x_45, x_48, x_2, x_46);
return x_82;
}
}
else
{
lean_object* x_83; 
lean_dec(x_49);
x_83 = l_Lean_Elab_Command_elabDef(x_45, x_48, x_2, x_46);
return x_83;
}
}
else
{
lean_object* x_84; 
lean_dec(x_49);
x_84 = l_Lean_Elab_Command_elabAbbrev(x_45, x_48, x_2, x_46);
return x_84;
}
}
}
else
{
uint8_t x_85; 
lean_dec(x_2);
x_85 = !lean_is_exclusive(x_6);
if (x_85 == 0)
{
return x_6;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_6, 0);
x_87 = lean_ctor_get(x_6, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_6);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
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
l_Lean_Elab_Command_elabConstant___closed__10 = _init_l_Lean_Elab_Command_elabConstant___closed__10();
lean_mark_persistent(l_Lean_Elab_Command_elabConstant___closed__10);
l_Lean_Elab_Command_elabConstant___closed__11 = _init_l_Lean_Elab_Command_elabConstant___closed__11();
lean_mark_persistent(l_Lean_Elab_Command_elabConstant___closed__11);
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
