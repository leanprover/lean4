// Lean compiler output
// Module: Lean.Elab.Declaration
// Imports: Init Lean.Util.CollectLevelParams Lean.Elab.DeclUtil Lean.Elab.Definition Lean.Elab.Inductive Lean.Elab.Structure
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
lean_object* l_Lean_Elab_Command_elabDeclaration(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkForall(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Declaration_7__expandMutualPreamble_x3f___closed__2;
lean_object* l_Lean_Elab_Term_throwErrorAt___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_expandOptDeclSig(lean_object*);
extern lean_object* l_Lean_Parser_Command_abbrev___elambda__1___closed__2;
lean_object* l___private_Lean_Elab_Declaration_7__expandMutualPreamble_x3f___closed__7;
lean_object* l_Lean_Elab_Command_addDecl(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instantiateMVars(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabAxiom___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabConstant___closed__4;
lean_object* l_unreachable_x21___rarg(lean_object*);
extern lean_object* l_Lean_nullKind;
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabConstant___closed__2;
lean_object* l_Lean_Syntax_getIdAt(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
lean_object* l_Lean_Elab_Command_elabExample(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabAbbrev(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_withDeclId___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabExample___closed__1;
lean_object* l_Lean_Elab_Command_elabConstant___closed__1;
extern lean_object* l_Array_empty___closed__1;
extern lean_object* l_Lean_Parser_Command_section___elambda__1___closed__2;
extern lean_object* l_Lean_Elab_Command_monadIOAux___rarg___closed__1;
lean_object* l_Lean_Elab_Command_elabExample___closed__2;
lean_object* lean_io_ref_get(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_declaration___elambda__1___closed__2;
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elabDeclaration(lean_object*);
extern lean_object* l_Lean_Parser_Command_mutual___elambda__1___closed__2;
lean_object* l___private_Lean_Elab_Declaration_2__classInductiveSyntaxToView(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l___private_Lean_Elab_Command_3__mkTermContext(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkForallUsedOnly(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* l_Lean_Elab_Command_getLevelNames___rarg(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Command_elabMutual(lean_object*);
extern lean_object* l_Lean_Parser_Command_mutual___elambda__1___closed__1;
lean_object* lean_string_utf8_byte_size(lean_object*);
extern lean_object* l_Lean_Parser_Command_example___elambda__1___closed__2;
lean_object* l___private_Lean_Elab_SyntheticMVars_11__synthesizeSyntheticMVarsAux___main(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_section___elambda__1___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Command_elabDeclaration___closed__1;
lean_object* l_Lean_Elab_Command_applyVisibility(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__8;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_1__inductiveSyntaxToView___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_1__inductiveSyntaxToView___spec__1___closed__1;
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Elab_Declaration_3__isMutualInductive___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_check___elambda__1___closed__2;
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_1__inductiveSyntaxToView___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__3;
extern lean_object* l_Lean_Parser_Command_classInductive___elambda__1___closed__2;
lean_object* l_Lean_Elab_Command_elabInstance___closed__4;
lean_object* l_Lean_Elab_Command_mkDeclName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Declaration_1__inductiveSyntaxToView___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_levelMVarToParam(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Declaration_7__expandMutualPreamble_x3f___closed__12;
lean_object* l___private_Lean_Elab_Declaration_6__splitMutualPreamble(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabAxiom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_tacticBlock___elambda__1___closed__7;
lean_object* l_Lean_Elab_Command_elabInstance___closed__1;
extern lean_object* l_Lean_Parser_Command_set__option___elambda__1___closed__2;
lean_object* l_Lean_Elab_Command_elabInstance___closed__2;
lean_object* l_Lean_Name_append___main(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_elabStructure___closed__8;
extern lean_object* l_Lean_Parser_Command_def___elambda__1___closed__2;
extern lean_object* l_Lean_Parser_Command_declValSimple___elambda__1___closed__2;
lean_object* l_Lean_Elab_Command_elabInductiveViews(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabConstant(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabAxiom___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Declaration_7__expandMutualPreamble_x3f___closed__5;
extern lean_object* l_Lean_Elab_Command_mkDef___lambda__1___closed__1;
lean_object* l___private_Lean_Elab_Declaration_7__expandMutualPreamble_x3f___closed__3;
lean_object* l_Lean_Elab_Command_elabClassInductive(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_throwError___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_instance___elambda__1___closed__1;
extern lean_object* l_Lean_Parser_Command_variable___elambda__1___closed__2;
lean_object* l_Lean_Elab_Command_elabCommand___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_4__elabMutualInductive___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Declaration_6__splitMutualPreamble___main(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_open___elambda__1___closed__2;
lean_object* l___private_Lean_Elab_Declaration_3__isMutualInductive___boxed(lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_1__inductiveSyntaxToView___spec__1___closed__2;
lean_object* l_Lean_Elab_Command_elabMutual___closed__2;
lean_object* l___private_Lean_Elab_Declaration_7__expandMutualPreamble_x3f___closed__9;
lean_object* l_Lean_Elab_Command_elabTheorem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabDef(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Declaration_7__expandMutualPreamble_x3f___closed__4;
lean_object* l_Lean_Elab_Command_elabAxiom___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_sortDeclLevelParams(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabInstance___closed__5;
extern lean_object* l_Lean_nullKind___closed__2;
uint8_t l___private_Lean_Elab_Declaration_3__isMutualInductive(lean_object*);
extern lean_object* l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
extern lean_object* l_Lean_Parser_Command_instance___elambda__1___closed__2;
extern lean_object* l_Lean_mkReducibilityAttrs___closed__4;
lean_object* l_Lean_mkAtomFrom(lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_mkInlineAttrs___closed__4;
extern lean_object* l_Lean_PrettyPrinter_Formatter_withPosition_formatter___closed__1;
extern lean_object* l_Lean_Parser_Command_universe___elambda__1___closed__2;
extern lean_object* l___private_Lean_Elab_Quotation_8__letBindRhss___main___closed__11;
uint8_t l___private_Lean_Elab_Declaration_5__isMutualPreambleCommand(lean_object*);
lean_object* l___private_Lean_Elab_Declaration_1__inductiveSyntaxToView(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Command_4__mkTermState(lean_object*);
lean_object* lean_environment_main_module(lean_object*);
extern lean_object* l_Lean_Parser_Command_end___elambda__1___closed__1;
lean_object* l_Lean_Elab_Command_elabMutual(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_axiom___elambda__1___closed__2;
lean_object* l_Lean_Elab_Command_getCurrMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_1__inductiveSyntaxToView___spec__1___closed__4;
extern lean_object* l_Lean_SourceInfo_inhabited___closed__1;
lean_object* l___private_Lean_Elab_Declaration_7__expandMutualPreamble_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabInstance___closed__3;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Elab_Declaration_3__isMutualInductive___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabAbbrev___closed__2;
lean_object* l___private_Lean_Elab_Declaration_7__expandMutualPreamble_x3f___closed__10;
lean_object* l_Lean_Elab_Command_getMainModule___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabStructure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_Modifiers_addAttribute(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getEnv___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabMutual___closed__3;
lean_object* l_Lean_Elab_expandDeclSig(lean_object*);
lean_object* l_Lean_Elab_Term_elabType(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_structure___elambda__1___closed__2;
extern lean_object* l_Lean_mkAppStx___closed__9;
lean_object* l_Lean_Elab_Command_elabConstant___closed__6;
lean_object* l___private_Lean_Elab_Declaration_6__splitMutualPreamble___main___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_inductive___elambda__1___closed__2;
lean_object* l___private_Lean_Elab_Declaration_7__expandMutualPreamble_x3f___closed__1;
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l___private_Lean_Elab_Declaration_7__expandMutualPreamble_x3f___closed__6;
extern lean_object* l_Lean_Parser_Command_universes___elambda__1___closed__2;
lean_object* lean_io_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_Elab_Command_applyAttributes___spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__1;
lean_object* l___private_Lean_Elab_Command_5__getVarDecls(lean_object*);
lean_object* l_Lean_Elab_Command_elabModifiers(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabDefLike(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Declaration_6__splitMutualPreamble___boxed(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_1__inductiveSyntaxToView___spec__1___closed__5;
lean_object* l_Lean_Elab_Command_elabDeclaration___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabBinders___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_Command_Modifiers_isProtected(lean_object*);
extern lean_object* l_Lean_Parser_Command_variables___elambda__1___closed__2;
lean_object* l___private_Lean_Elab_Declaration_4__elabMutualInductive(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Declaration_1__inductiveSyntaxToView___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_Command_Modifiers_isPrivate(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabDeclaration___closed__2;
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_1__inductiveSyntaxToView___spec__1___closed__3;
lean_object* l_Lean_Elab_Command_elabAxiom___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabConstant___closed__5;
lean_object* l_Lean_Elab_Command_checkValidCtorModifier(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabInductive(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_1__inductiveSyntaxToView___spec__1___closed__6;
lean_object* l_Lean_Elab_Command_elabDeclaration___closed__1;
lean_object* l_Lean_Elab_Command_elabDeclaration___closed__3;
lean_object* l_Lean_Elab_Command_elabConstant___closed__3;
lean_object* l___private_Lean_Elab_Declaration_7__expandMutualPreamble_x3f___closed__11;
lean_object* l_Lean_Elab_Command_elabAbbrev___closed__1;
lean_object* l_Lean_Elab_Command_checkValidInductiveModifier(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_CollectLevelParams_main___main(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_liftTermElabM___rarg___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Command_elabMutual___closed__1;
extern lean_object* l_Lean_Parser_Command_constant___elambda__1___closed__2;
extern lean_object* l_Lean_Parser_Command_theorem___elambda__1___closed__2;
lean_object* l___private_Lean_Elab_Declaration_5__isMutualPreambleCommand___boxed(lean_object*);
lean_object* l___private_Lean_Elab_Declaration_7__expandMutualPreamble_x3f___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabAxiom___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Declaration_7__expandMutualPreamble_x3f___closed__8;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Elab_replaceRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_declId___elambda__1___closed__2;
lean_object* l_Lean_Elab_Command_elabMutual___closed__1;
lean_object* _init_l_Lean_Elab_Command_elabAbbrev___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_mkInlineAttrs___closed__4;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_elabAbbrev___closed__2() {
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
lean_object* l_Lean_Elab_Command_elabAbbrev(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_6 = lean_unsigned_to_nat(2u);
x_7 = l_Lean_Syntax_getArg(x_2, x_6);
x_8 = l_Lean_Elab_expandOptDeclSig(x_7);
lean_dec(x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Elab_Command_elabAbbrev___closed__1;
x_12 = l_Lean_Elab_Command_Modifiers_addAttribute(x_1, x_11);
x_13 = l_Lean_Elab_Command_elabAbbrev___closed__2;
x_14 = l_Lean_Elab_Command_Modifiers_addAttribute(x_12, x_13);
x_15 = lean_unsigned_to_nat(1u);
x_16 = l_Lean_Syntax_getArg(x_2, x_15);
x_17 = lean_unsigned_to_nat(3u);
x_18 = l_Lean_Syntax_getArg(x_2, x_17);
x_19 = 4;
x_20 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_20, 0, x_2);
lean_ctor_set(x_20, 1, x_14);
lean_ctor_set(x_20, 2, x_16);
lean_ctor_set(x_20, 3, x_9);
lean_ctor_set(x_20, 4, x_10);
lean_ctor_set(x_20, 5, x_18);
lean_ctor_set_uint8(x_20, sizeof(void*)*6, x_19);
x_21 = l_Lean_Elab_Command_elabDefLike(x_20, x_3, x_4, x_5);
return x_21;
}
}
lean_object* l_Lean_Elab_Command_elabDef(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_6 = lean_unsigned_to_nat(2u);
x_7 = l_Lean_Syntax_getArg(x_2, x_6);
x_8 = l_Lean_Elab_expandOptDeclSig(x_7);
lean_dec(x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_unsigned_to_nat(1u);
x_12 = l_Lean_Syntax_getArg(x_2, x_11);
x_13 = lean_unsigned_to_nat(3u);
x_14 = l_Lean_Syntax_getArg(x_2, x_13);
x_15 = 0;
x_16 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_1);
lean_ctor_set(x_16, 2, x_12);
lean_ctor_set(x_16, 3, x_9);
lean_ctor_set(x_16, 4, x_10);
lean_ctor_set(x_16, 5, x_14);
lean_ctor_set_uint8(x_16, sizeof(void*)*6, x_15);
x_17 = l_Lean_Elab_Command_elabDefLike(x_16, x_3, x_4, x_5);
return x_17;
}
}
lean_object* l_Lean_Elab_Command_elabTheorem(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_6 = lean_unsigned_to_nat(2u);
x_7 = l_Lean_Syntax_getArg(x_2, x_6);
x_8 = l_Lean_Elab_expandDeclSig(x_7);
lean_dec(x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_unsigned_to_nat(1u);
x_12 = l_Lean_Syntax_getArg(x_2, x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_10);
x_14 = lean_unsigned_to_nat(3u);
x_15 = l_Lean_Syntax_getArg(x_2, x_14);
x_16 = 1;
x_17 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_1);
lean_ctor_set(x_17, 2, x_12);
lean_ctor_set(x_17, 3, x_9);
lean_ctor_set(x_17, 4, x_13);
lean_ctor_set(x_17, 5, x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*6, x_16);
x_18 = l_Lean_Elab_Command_elabDefLike(x_17, x_3, x_4, x_5);
return x_18;
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
lean_object* l_Lean_Elab_Command_elabConstant(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_unsigned_to_nat(2u);
x_7 = l_Lean_Syntax_getArg(x_2, x_6);
x_8 = l_Lean_Elab_expandDeclSig(x_7);
lean_dec(x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_unsigned_to_nat(3u);
x_12 = l_Lean_Syntax_getArg(x_2, x_11);
x_13 = l_Lean_Syntax_getOptional_x3f(x_12);
lean_dec(x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = l_Lean_Elab_Command_getCurrMacroScope(x_3, x_4, x_5);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Elab_Command_getMainModule___rarg(x_4, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Elab_Command_elabConstant___closed__4;
x_21 = l_Lean_addMacroScope(x_18, x_20, x_15);
x_22 = l_Lean_SourceInfo_inhabited___closed__1;
x_23 = l_Lean_Elab_Command_elabConstant___closed__3;
x_24 = l_Lean_Elab_Command_elabConstant___closed__6;
x_25 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set(x_25, 2, x_21);
lean_ctor_set(x_25, 3, x_24);
x_26 = l_Array_empty___closed__1;
x_27 = lean_array_push(x_26, x_25);
x_28 = l___private_Lean_Elab_Quotation_8__letBindRhss___main___closed__11;
x_29 = lean_array_push(x_27, x_28);
x_30 = l_Lean_mkAppStx___closed__8;
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
x_32 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__3;
x_33 = l_Lean_mkAtomFrom(x_2, x_32);
x_34 = l_Lean_mkAppStx___closed__9;
x_35 = lean_array_push(x_34, x_33);
x_36 = lean_array_push(x_35, x_31);
x_37 = l_Lean_Parser_Command_declValSimple___elambda__1___closed__2;
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
x_39 = lean_unsigned_to_nat(1u);
x_40 = l_Lean_Syntax_getArg(x_2, x_39);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_10);
x_42 = 3;
x_43 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_43, 0, x_2);
lean_ctor_set(x_43, 1, x_1);
lean_ctor_set(x_43, 2, x_40);
lean_ctor_set(x_43, 3, x_9);
lean_ctor_set(x_43, 4, x_41);
lean_ctor_set(x_43, 5, x_38);
lean_ctor_set_uint8(x_43, sizeof(void*)*6, x_42);
x_44 = l_Lean_Elab_Command_elabDefLike(x_43, x_3, x_4, x_19);
return x_44;
}
else
{
uint8_t x_45; 
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_17);
if (x_45 == 0)
{
return x_17;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_17, 0);
x_47 = lean_ctor_get(x_17, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_17);
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
x_49 = !lean_is_exclusive(x_13);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; 
x_50 = lean_ctor_get(x_13, 0);
x_51 = lean_unsigned_to_nat(1u);
x_52 = l_Lean_Syntax_getArg(x_2, x_51);
lean_ctor_set(x_13, 0, x_10);
x_53 = 3;
x_54 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_54, 0, x_2);
lean_ctor_set(x_54, 1, x_1);
lean_ctor_set(x_54, 2, x_52);
lean_ctor_set(x_54, 3, x_9);
lean_ctor_set(x_54, 4, x_13);
lean_ctor_set(x_54, 5, x_50);
lean_ctor_set_uint8(x_54, sizeof(void*)*6, x_53);
x_55 = l_Lean_Elab_Command_elabDefLike(x_54, x_3, x_4, x_5);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; 
x_56 = lean_ctor_get(x_13, 0);
lean_inc(x_56);
lean_dec(x_13);
x_57 = lean_unsigned_to_nat(1u);
x_58 = l_Lean_Syntax_getArg(x_2, x_57);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_10);
x_60 = 3;
x_61 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_61, 0, x_2);
lean_ctor_set(x_61, 1, x_1);
lean_ctor_set(x_61, 2, x_58);
lean_ctor_set(x_61, 3, x_9);
lean_ctor_set(x_61, 4, x_59);
lean_ctor_set(x_61, 5, x_56);
lean_ctor_set_uint8(x_61, sizeof(void*)*6, x_60);
x_62 = l_Lean_Elab_Command_elabDefLike(x_61, x_3, x_4, x_5);
return x_62;
}
}
}
}
lean_object* _init_l_Lean_Elab_Command_elabInstance___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Command_instance___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_elabInstance___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabInstance___closed__1;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_elabInstance___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("not implemented yet");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_elabInstance___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabInstance___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_elabInstance___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabInstance___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_elabInstance(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_6 = lean_unsigned_to_nat(2u);
x_7 = l_Lean_Syntax_getArg(x_2, x_6);
x_8 = l_Lean_Elab_expandDeclSig(x_7);
lean_dec(x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Elab_Command_elabInstance___closed__2;
x_12 = l_Lean_Elab_Command_Modifiers_addAttribute(x_1, x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = l_Lean_Syntax_getArg(x_2, x_13);
x_15 = l_Lean_Syntax_getOptional_x3f(x_14);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_2);
x_16 = l_Lean_Elab_Command_elabInstance___closed__5;
x_17 = l_Lean_Elab_Command_throwError___rarg(x_16, x_3, x_4, x_5);
lean_dec(x_4);
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
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_15);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_15, 0);
lean_ctor_set(x_15, 0, x_10);
x_24 = lean_unsigned_to_nat(3u);
x_25 = l_Lean_Syntax_getArg(x_2, x_24);
x_26 = 0;
x_27 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_27, 0, x_2);
lean_ctor_set(x_27, 1, x_12);
lean_ctor_set(x_27, 2, x_23);
lean_ctor_set(x_27, 3, x_9);
lean_ctor_set(x_27, 4, x_15);
lean_ctor_set(x_27, 5, x_25);
lean_ctor_set_uint8(x_27, sizeof(void*)*6, x_26);
x_28 = l_Lean_Elab_Command_elabDefLike(x_27, x_3, x_4, x_5);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; 
x_29 = lean_ctor_get(x_15, 0);
lean_inc(x_29);
lean_dec(x_15);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_10);
x_31 = lean_unsigned_to_nat(3u);
x_32 = l_Lean_Syntax_getArg(x_2, x_31);
x_33 = 0;
x_34 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_34, 0, x_2);
lean_ctor_set(x_34, 1, x_12);
lean_ctor_set(x_34, 2, x_29);
lean_ctor_set(x_34, 3, x_9);
lean_ctor_set(x_34, 4, x_30);
lean_ctor_set(x_34, 5, x_32);
lean_ctor_set_uint8(x_34, sizeof(void*)*6, x_33);
x_35 = l_Lean_Elab_Command_elabDefLike(x_34, x_3, x_4, x_5);
return x_35;
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
lean_object* l_Lean_Elab_Command_elabExample(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = l_Lean_Syntax_getArg(x_2, x_6);
x_8 = l_Lean_Elab_expandDeclSig(x_7);
lean_dec(x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Elab_Command_elabExample___closed__2;
x_12 = l_Lean_mkIdentFrom(x_2, x_11);
x_13 = l_Lean_mkAppStx___closed__9;
x_14 = lean_array_push(x_13, x_12);
x_15 = l_Lean_mkOptionalNode___closed__1;
x_16 = lean_array_push(x_14, x_15);
x_17 = l_Lean_Parser_Command_declId___elambda__1___closed__2;
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_10);
x_20 = lean_unsigned_to_nat(2u);
x_21 = l_Lean_Syntax_getArg(x_2, x_20);
x_22 = 2;
x_23 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_23, 0, x_2);
lean_ctor_set(x_23, 1, x_1);
lean_ctor_set(x_23, 2, x_18);
lean_ctor_set(x_23, 3, x_9);
lean_ctor_set(x_23, 4, x_19);
lean_ctor_set(x_23, 5, x_21);
lean_ctor_set_uint8(x_23, sizeof(void*)*6, x_22);
x_24 = l_Lean_Elab_Command_elabDefLike(x_23, x_3, x_4, x_5);
return x_24;
}
}
lean_object* l_Lean_Elab_Command_elabAxiom___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
x_11 = l_Lean_Elab_Term_elabType(x_1, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = 0;
x_15 = lean_box(0);
lean_inc(x_9);
x_16 = l___private_Lean_Elab_SyntheticMVars_11__synthesizeSyntheticMVarsAux___main(x_14, x_15, x_9, x_13);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
lean_inc(x_9);
x_18 = l_Lean_Elab_Term_instantiateMVars(x_12, x_9, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_9);
x_21 = l_Lean_Elab_Term_mkForall(x_8, x_19, x_9, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_9);
x_24 = l_Lean_Elab_Term_mkForallUsedOnly(x_2, x_22, x_9, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_unsigned_to_nat(1u);
lean_inc(x_9);
x_29 = l_Lean_Elab_Term_levelMVarToParam(x_27, x_28, x_9, x_26);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_ctor_get(x_29, 1);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_Elab_Command_mkDef___lambda__1___closed__1;
lean_inc(x_33);
x_35 = l_Lean_CollectLevelParams_main___main(x_33, x_34);
x_36 = lean_ctor_get(x_35, 2);
lean_inc(x_36);
lean_dec(x_35);
x_37 = l_Lean_Elab_Command_sortDeclLevelParams(x_3, x_4, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_33);
lean_free_object(x_29);
lean_dec(x_6);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec(x_37);
x_39 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = l_Lean_Elab_Term_throwErrorAt___rarg(x_5, x_40, x_9, x_32);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_9);
x_42 = lean_ctor_get(x_37, 0);
lean_inc(x_42);
lean_dec(x_37);
x_43 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_43, 0, x_6);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_43, 2, x_33);
x_44 = lean_ctor_get_uint8(x_7, sizeof(void*)*2 + 3);
x_45 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set_uint8(x_45, sizeof(void*)*1, x_44);
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_29, 0, x_46);
return x_29;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_47 = lean_ctor_get(x_29, 0);
x_48 = lean_ctor_get(x_29, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_29);
x_49 = lean_ctor_get(x_47, 0);
lean_inc(x_49);
lean_dec(x_47);
x_50 = l_Lean_Elab_Command_mkDef___lambda__1___closed__1;
lean_inc(x_49);
x_51 = l_Lean_CollectLevelParams_main___main(x_49, x_50);
x_52 = lean_ctor_get(x_51, 2);
lean_inc(x_52);
lean_dec(x_51);
x_53 = l_Lean_Elab_Command_sortDeclLevelParams(x_3, x_4, x_52);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_49);
lean_dec(x_6);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
lean_dec(x_53);
x_55 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_55, 0, x_54);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_55);
x_57 = l_Lean_Elab_Term_throwErrorAt___rarg(x_5, x_56, x_9, x_48);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_9);
x_58 = lean_ctor_get(x_53, 0);
lean_inc(x_58);
lean_dec(x_53);
x_59 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_59, 0, x_6);
lean_ctor_set(x_59, 1, x_58);
lean_ctor_set(x_59, 2, x_49);
x_60 = lean_ctor_get_uint8(x_7, sizeof(void*)*2 + 3);
x_61 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set_uint8(x_61, sizeof(void*)*1, x_60);
x_62 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_62, 0, x_61);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_48);
return x_63;
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_64 = !lean_is_exclusive(x_24);
if (x_64 == 0)
{
return x_24;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_24, 0);
x_66 = lean_ctor_get(x_24, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_24);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
else
{
uint8_t x_68; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_68 = !lean_is_exclusive(x_21);
if (x_68 == 0)
{
return x_21;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_21, 0);
x_70 = lean_ctor_get(x_21, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_21);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_72 = !lean_is_exclusive(x_16);
if (x_72 == 0)
{
return x_16;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_16, 0);
x_74 = lean_ctor_get(x_16, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_16);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
else
{
uint8_t x_76; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_76 = !lean_is_exclusive(x_11);
if (x_76 == 0)
{
return x_11;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_11, 0);
x_78 = lean_ctor_get(x_11, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_11);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
}
lean_object* l_Lean_Elab_Command_elabAxiom___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_Lean_Syntax_getArgs(x_1);
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabAxiom___lambda__1___boxed), 10, 7);
lean_closure_set(x_12, 0, x_2);
lean_closure_set(x_12, 1, x_8);
lean_closure_set(x_12, 2, x_3);
lean_closure_set(x_12, 3, x_4);
lean_closure_set(x_12, 4, x_5);
lean_closure_set(x_12, 5, x_6);
lean_closure_set(x_12, 6, x_7);
x_13 = l_Lean_Elab_Term_elabBinders___rarg(x_11, x_12, x_9, x_10);
lean_dec(x_11);
return x_13;
}
}
lean_object* l_Lean_Elab_Command_elabAxiom___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_7);
x_10 = l_Lean_Elab_Command_mkDeclName(x_1, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_33; lean_object* x_34; lean_object* x_35; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_33 = 2;
x_34 = lean_unsigned_to_nat(0u);
lean_inc(x_7);
lean_inc(x_11);
x_35 = l_Array_forMAux___main___at_Lean_Elab_Command_applyAttributes___spec__1(x_11, x_33, x_13, x_34, x_7, x_8, x_12);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = l_Lean_Elab_Command_getLevelNames___rarg(x_8, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
lean_inc(x_11);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_11);
lean_inc(x_11);
x_41 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabAxiom___lambda__2___boxed), 10, 7);
lean_closure_set(x_41, 0, x_2);
lean_closure_set(x_41, 1, x_3);
lean_closure_set(x_41, 2, x_4);
lean_closure_set(x_41, 3, x_38);
lean_closure_set(x_41, 4, x_5);
lean_closure_set(x_41, 5, x_11);
lean_closure_set(x_41, 6, x_1);
x_42 = lean_io_ref_get(x_8, x_39);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = l___private_Lean_Elab_Command_5__getVarDecls(x_43);
lean_dec(x_43);
x_46 = lean_io_ref_get(x_8, x_44);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = l___private_Lean_Elab_Command_3__mkTermContext(x_7, x_47, x_40);
x_50 = l___private_Lean_Elab_Command_4__mkTermState(x_47);
lean_dec(x_47);
x_51 = l_Lean_Elab_Term_elabBinders___rarg(x_45, x_41, x_49, x_50);
lean_dec(x_45);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_io_ref_take(x_8, x_48);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_55 = lean_ctor_get(x_53, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
lean_dec(x_54);
x_58 = lean_ctor_get(x_55, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_55, 3);
lean_inc(x_59);
lean_dec(x_55);
x_60 = lean_ctor_get(x_53, 2);
lean_inc(x_60);
lean_dec(x_53);
x_61 = !lean_is_exclusive(x_56);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = lean_ctor_get(x_56, 5);
lean_dec(x_62);
x_63 = lean_ctor_get(x_56, 1);
lean_dec(x_63);
x_64 = lean_ctor_get(x_56, 0);
lean_dec(x_64);
lean_ctor_set(x_56, 5, x_59);
lean_ctor_set(x_56, 1, x_60);
lean_ctor_set(x_56, 0, x_58);
x_65 = lean_io_ref_set(x_8, x_56, x_57);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
x_14 = x_52;
x_15 = x_66;
goto block_32;
}
else
{
uint8_t x_67; 
lean_dec(x_52);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
x_67 = !lean_is_exclusive(x_65);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_68 = lean_ctor_get(x_65, 0);
x_69 = lean_box(0);
x_70 = lean_io_error_to_string(x_68);
x_71 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_71, 0, x_70);
x_72 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_72, 0, x_71);
x_73 = l_Lean_Elab_Command_monadIOAux___rarg___closed__1;
x_74 = l_Lean_PrettyPrinter_Formatter_withPosition_formatter___closed__1;
x_75 = 2;
x_76 = l_String_splitAux___main___closed__1;
x_77 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_77, 0, x_73);
lean_ctor_set(x_77, 1, x_74);
lean_ctor_set(x_77, 2, x_69);
lean_ctor_set(x_77, 3, x_76);
lean_ctor_set(x_77, 4, x_72);
lean_ctor_set_uint8(x_77, sizeof(void*)*5, x_75);
x_78 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_65, 0, x_78);
return x_65;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_79 = lean_ctor_get(x_65, 0);
x_80 = lean_ctor_get(x_65, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_65);
x_81 = lean_box(0);
x_82 = lean_io_error_to_string(x_79);
x_83 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_83, 0, x_82);
x_84 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_84, 0, x_83);
x_85 = l_Lean_Elab_Command_monadIOAux___rarg___closed__1;
x_86 = l_Lean_PrettyPrinter_Formatter_withPosition_formatter___closed__1;
x_87 = 2;
x_88 = l_String_splitAux___main___closed__1;
x_89 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_89, 0, x_85);
lean_ctor_set(x_89, 1, x_86);
lean_ctor_set(x_89, 2, x_81);
lean_ctor_set(x_89, 3, x_88);
lean_ctor_set(x_89, 4, x_84);
lean_ctor_set_uint8(x_89, sizeof(void*)*5, x_87);
x_90 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_90, 0, x_89);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_80);
return x_91;
}
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_92 = lean_ctor_get(x_56, 2);
x_93 = lean_ctor_get(x_56, 3);
x_94 = lean_ctor_get(x_56, 4);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_56);
x_95 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_95, 0, x_58);
lean_ctor_set(x_95, 1, x_60);
lean_ctor_set(x_95, 2, x_92);
lean_ctor_set(x_95, 3, x_93);
lean_ctor_set(x_95, 4, x_94);
lean_ctor_set(x_95, 5, x_59);
x_96 = lean_io_ref_set(x_8, x_95, x_57);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; 
x_97 = lean_ctor_get(x_96, 1);
lean_inc(x_97);
lean_dec(x_96);
x_14 = x_52;
x_15 = x_97;
goto block_32;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_52);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
x_98 = lean_ctor_get(x_96, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_96, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_100 = x_96;
} else {
 lean_dec_ref(x_96);
 x_100 = lean_box(0);
}
x_101 = lean_box(0);
x_102 = lean_io_error_to_string(x_98);
x_103 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_103, 0, x_102);
x_104 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_104, 0, x_103);
x_105 = l_Lean_Elab_Command_monadIOAux___rarg___closed__1;
x_106 = l_Lean_PrettyPrinter_Formatter_withPosition_formatter___closed__1;
x_107 = 2;
x_108 = l_String_splitAux___main___closed__1;
x_109 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_109, 0, x_105);
lean_ctor_set(x_109, 1, x_106);
lean_ctor_set(x_109, 2, x_101);
lean_ctor_set(x_109, 3, x_108);
lean_ctor_set(x_109, 4, x_104);
lean_ctor_set_uint8(x_109, sizeof(void*)*5, x_107);
x_110 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_110, 0, x_109);
if (lean_is_scalar(x_100)) {
 x_111 = lean_alloc_ctor(1, 2, 0);
} else {
 x_111 = x_100;
}
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_99);
return x_111;
}
}
}
else
{
uint8_t x_112; 
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
x_112 = !lean_is_exclusive(x_54);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_113 = lean_ctor_get(x_54, 0);
x_114 = lean_box(0);
x_115 = lean_io_error_to_string(x_113);
x_116 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_116, 0, x_115);
x_117 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_117, 0, x_116);
x_118 = l_Lean_Elab_Command_monadIOAux___rarg___closed__1;
x_119 = l_Lean_PrettyPrinter_Formatter_withPosition_formatter___closed__1;
x_120 = 2;
x_121 = l_String_splitAux___main___closed__1;
x_122 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_122, 0, x_118);
lean_ctor_set(x_122, 1, x_119);
lean_ctor_set(x_122, 2, x_114);
lean_ctor_set(x_122, 3, x_121);
lean_ctor_set(x_122, 4, x_117);
lean_ctor_set_uint8(x_122, sizeof(void*)*5, x_120);
x_123 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_54, 0, x_123);
return x_54;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_124 = lean_ctor_get(x_54, 0);
x_125 = lean_ctor_get(x_54, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_54);
x_126 = lean_box(0);
x_127 = lean_io_error_to_string(x_124);
x_128 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_128, 0, x_127);
x_129 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_129, 0, x_128);
x_130 = l_Lean_Elab_Command_monadIOAux___rarg___closed__1;
x_131 = l_Lean_PrettyPrinter_Formatter_withPosition_formatter___closed__1;
x_132 = 2;
x_133 = l_String_splitAux___main___closed__1;
x_134 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_134, 0, x_130);
lean_ctor_set(x_134, 1, x_131);
lean_ctor_set(x_134, 2, x_126);
lean_ctor_set(x_134, 3, x_133);
lean_ctor_set(x_134, 4, x_129);
lean_ctor_set_uint8(x_134, sizeof(void*)*5, x_132);
x_135 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_135, 0, x_134);
x_136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_125);
return x_136;
}
}
}
else
{
lean_object* x_137; 
x_137 = lean_ctor_get(x_51, 0);
lean_inc(x_137);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_7);
x_138 = lean_ctor_get(x_51, 1);
lean_inc(x_138);
lean_dec(x_51);
x_139 = lean_ctor_get(x_137, 0);
lean_inc(x_139);
lean_dec(x_137);
x_140 = lean_io_ref_take(x_8, x_48);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; 
x_141 = lean_ctor_get(x_138, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_140, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_140, 1);
lean_inc(x_143);
lean_dec(x_140);
x_144 = lean_ctor_get(x_141, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_141, 3);
lean_inc(x_145);
lean_dec(x_141);
x_146 = lean_ctor_get(x_138, 2);
lean_inc(x_146);
lean_dec(x_138);
x_147 = !lean_is_exclusive(x_142);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_148 = lean_ctor_get(x_142, 5);
lean_dec(x_148);
x_149 = lean_ctor_get(x_142, 1);
lean_dec(x_149);
x_150 = lean_ctor_get(x_142, 0);
lean_dec(x_150);
lean_ctor_set(x_142, 5, x_145);
lean_ctor_set(x_142, 1, x_146);
lean_ctor_set(x_142, 0, x_144);
x_151 = lean_io_ref_set(x_8, x_142, x_143);
lean_dec(x_8);
if (lean_obj_tag(x_151) == 0)
{
uint8_t x_152; 
x_152 = !lean_is_exclusive(x_151);
if (x_152 == 0)
{
lean_object* x_153; 
x_153 = lean_ctor_get(x_151, 0);
lean_dec(x_153);
lean_ctor_set_tag(x_151, 1);
lean_ctor_set(x_151, 0, x_139);
return x_151;
}
else
{
lean_object* x_154; lean_object* x_155; 
x_154 = lean_ctor_get(x_151, 1);
lean_inc(x_154);
lean_dec(x_151);
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_139);
lean_ctor_set(x_155, 1, x_154);
return x_155;
}
}
else
{
uint8_t x_156; 
lean_dec(x_139);
x_156 = !lean_is_exclusive(x_151);
if (x_156 == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; uint8_t x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_157 = lean_ctor_get(x_151, 0);
x_158 = lean_box(0);
x_159 = lean_io_error_to_string(x_157);
x_160 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_160, 0, x_159);
x_161 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_161, 0, x_160);
x_162 = l_Lean_Elab_Command_monadIOAux___rarg___closed__1;
x_163 = l_Lean_PrettyPrinter_Formatter_withPosition_formatter___closed__1;
x_164 = 2;
x_165 = l_String_splitAux___main___closed__1;
x_166 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_166, 0, x_162);
lean_ctor_set(x_166, 1, x_163);
lean_ctor_set(x_166, 2, x_158);
lean_ctor_set(x_166, 3, x_165);
lean_ctor_set(x_166, 4, x_161);
lean_ctor_set_uint8(x_166, sizeof(void*)*5, x_164);
x_167 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_151, 0, x_167);
return x_151;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_168 = lean_ctor_get(x_151, 0);
x_169 = lean_ctor_get(x_151, 1);
lean_inc(x_169);
lean_inc(x_168);
lean_dec(x_151);
x_170 = lean_box(0);
x_171 = lean_io_error_to_string(x_168);
x_172 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_172, 0, x_171);
x_173 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_173, 0, x_172);
x_174 = l_Lean_Elab_Command_monadIOAux___rarg___closed__1;
x_175 = l_Lean_PrettyPrinter_Formatter_withPosition_formatter___closed__1;
x_176 = 2;
x_177 = l_String_splitAux___main___closed__1;
x_178 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_178, 0, x_174);
lean_ctor_set(x_178, 1, x_175);
lean_ctor_set(x_178, 2, x_170);
lean_ctor_set(x_178, 3, x_177);
lean_ctor_set(x_178, 4, x_173);
lean_ctor_set_uint8(x_178, sizeof(void*)*5, x_176);
x_179 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_179, 0, x_178);
x_180 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_169);
return x_180;
}
}
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_181 = lean_ctor_get(x_142, 2);
x_182 = lean_ctor_get(x_142, 3);
x_183 = lean_ctor_get(x_142, 4);
lean_inc(x_183);
lean_inc(x_182);
lean_inc(x_181);
lean_dec(x_142);
x_184 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_184, 0, x_144);
lean_ctor_set(x_184, 1, x_146);
lean_ctor_set(x_184, 2, x_181);
lean_ctor_set(x_184, 3, x_182);
lean_ctor_set(x_184, 4, x_183);
lean_ctor_set(x_184, 5, x_145);
x_185 = lean_io_ref_set(x_8, x_184, x_143);
lean_dec(x_8);
if (lean_obj_tag(x_185) == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_186 = lean_ctor_get(x_185, 1);
lean_inc(x_186);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 x_187 = x_185;
} else {
 lean_dec_ref(x_185);
 x_187 = lean_box(0);
}
if (lean_is_scalar(x_187)) {
 x_188 = lean_alloc_ctor(1, 2, 0);
} else {
 x_188 = x_187;
 lean_ctor_set_tag(x_188, 1);
}
lean_ctor_set(x_188, 0, x_139);
lean_ctor_set(x_188, 1, x_186);
return x_188;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; uint8_t x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
lean_dec(x_139);
x_189 = lean_ctor_get(x_185, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_185, 1);
lean_inc(x_190);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 x_191 = x_185;
} else {
 lean_dec_ref(x_185);
 x_191 = lean_box(0);
}
x_192 = lean_box(0);
x_193 = lean_io_error_to_string(x_189);
x_194 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_194, 0, x_193);
x_195 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_195, 0, x_194);
x_196 = l_Lean_Elab_Command_monadIOAux___rarg___closed__1;
x_197 = l_Lean_PrettyPrinter_Formatter_withPosition_formatter___closed__1;
x_198 = 2;
x_199 = l_String_splitAux___main___closed__1;
x_200 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_200, 0, x_196);
lean_ctor_set(x_200, 1, x_197);
lean_ctor_set(x_200, 2, x_192);
lean_ctor_set(x_200, 3, x_199);
lean_ctor_set(x_200, 4, x_195);
lean_ctor_set_uint8(x_200, sizeof(void*)*5, x_198);
x_201 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_201, 0, x_200);
if (lean_is_scalar(x_191)) {
 x_202 = lean_alloc_ctor(1, 2, 0);
} else {
 x_202 = x_191;
}
lean_ctor_set(x_202, 0, x_201);
lean_ctor_set(x_202, 1, x_190);
return x_202;
}
}
}
else
{
uint8_t x_203; 
lean_dec(x_139);
lean_dec(x_138);
lean_dec(x_8);
x_203 = !lean_is_exclusive(x_140);
if (x_203 == 0)
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; uint8_t x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_204 = lean_ctor_get(x_140, 0);
x_205 = lean_box(0);
x_206 = lean_io_error_to_string(x_204);
x_207 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_207, 0, x_206);
x_208 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_208, 0, x_207);
x_209 = l_Lean_Elab_Command_monadIOAux___rarg___closed__1;
x_210 = l_Lean_PrettyPrinter_Formatter_withPosition_formatter___closed__1;
x_211 = 2;
x_212 = l_String_splitAux___main___closed__1;
x_213 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_213, 0, x_209);
lean_ctor_set(x_213, 1, x_210);
lean_ctor_set(x_213, 2, x_205);
lean_ctor_set(x_213, 3, x_212);
lean_ctor_set(x_213, 4, x_208);
lean_ctor_set_uint8(x_213, sizeof(void*)*5, x_211);
x_214 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set(x_140, 0, x_214);
return x_140;
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; uint8_t x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_215 = lean_ctor_get(x_140, 0);
x_216 = lean_ctor_get(x_140, 1);
lean_inc(x_216);
lean_inc(x_215);
lean_dec(x_140);
x_217 = lean_box(0);
x_218 = lean_io_error_to_string(x_215);
x_219 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_219, 0, x_218);
x_220 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_220, 0, x_219);
x_221 = l_Lean_Elab_Command_monadIOAux___rarg___closed__1;
x_222 = l_Lean_PrettyPrinter_Formatter_withPosition_formatter___closed__1;
x_223 = 2;
x_224 = l_String_splitAux___main___closed__1;
x_225 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_225, 0, x_221);
lean_ctor_set(x_225, 1, x_222);
lean_ctor_set(x_225, 2, x_217);
lean_ctor_set(x_225, 3, x_224);
lean_ctor_set(x_225, 4, x_220);
lean_ctor_set_uint8(x_225, sizeof(void*)*5, x_223);
x_226 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_226, 0, x_225);
x_227 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_227, 0, x_226);
lean_ctor_set(x_227, 1, x_216);
return x_227;
}
}
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; 
lean_dec(x_51);
x_228 = l_Lean_Elab_Command_liftTermElabM___rarg___closed__1;
x_229 = l_unreachable_x21___rarg(x_228);
lean_inc(x_8);
lean_inc(x_7);
x_230 = lean_apply_3(x_229, x_7, x_8, x_48);
if (lean_obj_tag(x_230) == 0)
{
lean_object* x_231; lean_object* x_232; 
x_231 = lean_ctor_get(x_230, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_230, 1);
lean_inc(x_232);
lean_dec(x_230);
x_14 = x_231;
x_15 = x_232;
goto block_32;
}
else
{
uint8_t x_233; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
x_233 = !lean_is_exclusive(x_230);
if (x_233 == 0)
{
return x_230;
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_234 = lean_ctor_get(x_230, 0);
x_235 = lean_ctor_get(x_230, 1);
lean_inc(x_235);
lean_inc(x_234);
lean_dec(x_230);
x_236 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_236, 0, x_234);
lean_ctor_set(x_236, 1, x_235);
return x_236;
}
}
}
}
}
else
{
uint8_t x_237; 
lean_dec(x_45);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
x_237 = !lean_is_exclusive(x_46);
if (x_237 == 0)
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; uint8_t x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_238 = lean_ctor_get(x_46, 0);
x_239 = lean_box(0);
x_240 = lean_io_error_to_string(x_238);
x_241 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_241, 0, x_240);
x_242 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_242, 0, x_241);
x_243 = l_Lean_Elab_Command_monadIOAux___rarg___closed__1;
x_244 = l_Lean_PrettyPrinter_Formatter_withPosition_formatter___closed__1;
x_245 = 2;
x_246 = l_String_splitAux___main___closed__1;
x_247 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_247, 0, x_243);
lean_ctor_set(x_247, 1, x_244);
lean_ctor_set(x_247, 2, x_239);
lean_ctor_set(x_247, 3, x_246);
lean_ctor_set(x_247, 4, x_242);
lean_ctor_set_uint8(x_247, sizeof(void*)*5, x_245);
x_248 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_248, 0, x_247);
lean_ctor_set(x_46, 0, x_248);
return x_46;
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; uint8_t x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_249 = lean_ctor_get(x_46, 0);
x_250 = lean_ctor_get(x_46, 1);
lean_inc(x_250);
lean_inc(x_249);
lean_dec(x_46);
x_251 = lean_box(0);
x_252 = lean_io_error_to_string(x_249);
x_253 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_253, 0, x_252);
x_254 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_254, 0, x_253);
x_255 = l_Lean_Elab_Command_monadIOAux___rarg___closed__1;
x_256 = l_Lean_PrettyPrinter_Formatter_withPosition_formatter___closed__1;
x_257 = 2;
x_258 = l_String_splitAux___main___closed__1;
x_259 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_259, 0, x_255);
lean_ctor_set(x_259, 1, x_256);
lean_ctor_set(x_259, 2, x_251);
lean_ctor_set(x_259, 3, x_258);
lean_ctor_set(x_259, 4, x_254);
lean_ctor_set_uint8(x_259, sizeof(void*)*5, x_257);
x_260 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_260, 0, x_259);
x_261 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_261, 0, x_260);
lean_ctor_set(x_261, 1, x_250);
return x_261;
}
}
}
else
{
uint8_t x_262; 
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
x_262 = !lean_is_exclusive(x_42);
if (x_262 == 0)
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; uint8_t x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; 
x_263 = lean_ctor_get(x_42, 0);
x_264 = lean_box(0);
x_265 = lean_io_error_to_string(x_263);
x_266 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_266, 0, x_265);
x_267 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_267, 0, x_266);
x_268 = l_Lean_Elab_Command_monadIOAux___rarg___closed__1;
x_269 = l_Lean_PrettyPrinter_Formatter_withPosition_formatter___closed__1;
x_270 = 2;
x_271 = l_String_splitAux___main___closed__1;
x_272 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_272, 0, x_268);
lean_ctor_set(x_272, 1, x_269);
lean_ctor_set(x_272, 2, x_264);
lean_ctor_set(x_272, 3, x_271);
lean_ctor_set(x_272, 4, x_267);
lean_ctor_set_uint8(x_272, sizeof(void*)*5, x_270);
x_273 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_273, 0, x_272);
lean_ctor_set(x_42, 0, x_273);
return x_42;
}
else
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; uint8_t x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; 
x_274 = lean_ctor_get(x_42, 0);
x_275 = lean_ctor_get(x_42, 1);
lean_inc(x_275);
lean_inc(x_274);
lean_dec(x_42);
x_276 = lean_box(0);
x_277 = lean_io_error_to_string(x_274);
x_278 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_278, 0, x_277);
x_279 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_279, 0, x_278);
x_280 = l_Lean_Elab_Command_monadIOAux___rarg___closed__1;
x_281 = l_Lean_PrettyPrinter_Formatter_withPosition_formatter___closed__1;
x_282 = 2;
x_283 = l_String_splitAux___main___closed__1;
x_284 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_284, 0, x_280);
lean_ctor_set(x_284, 1, x_281);
lean_ctor_set(x_284, 2, x_276);
lean_ctor_set(x_284, 3, x_283);
lean_ctor_set(x_284, 4, x_279);
lean_ctor_set_uint8(x_284, sizeof(void*)*5, x_282);
x_285 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_285, 0, x_284);
x_286 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_286, 0, x_285);
lean_ctor_set(x_286, 1, x_275);
return x_286;
}
}
}
else
{
uint8_t x_287; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_287 = !lean_is_exclusive(x_37);
if (x_287 == 0)
{
return x_37;
}
else
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; 
x_288 = lean_ctor_get(x_37, 0);
x_289 = lean_ctor_get(x_37, 1);
lean_inc(x_289);
lean_inc(x_288);
lean_dec(x_37);
x_290 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_290, 0, x_288);
lean_ctor_set(x_290, 1, x_289);
return x_290;
}
}
}
else
{
uint8_t x_291; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_291 = !lean_is_exclusive(x_35);
if (x_291 == 0)
{
return x_35;
}
else
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; 
x_292 = lean_ctor_get(x_35, 0);
x_293 = lean_ctor_get(x_35, 1);
lean_inc(x_293);
lean_inc(x_292);
lean_dec(x_35);
x_294 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_294, 0, x_292);
lean_ctor_set(x_294, 1, x_293);
return x_294;
}
}
block_32:
{
lean_object* x_16; 
x_16 = l_Lean_Elab_Command_addDecl(x_14, x_7, x_8, x_15);
lean_dec(x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = 0;
x_19 = lean_unsigned_to_nat(0u);
lean_inc(x_7);
lean_inc(x_11);
x_20 = l_Array_forMAux___main___at_Lean_Elab_Command_applyAttributes___spec__1(x_11, x_18, x_13, x_19, x_7, x_8, x_17);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = 1;
x_23 = l_Array_forMAux___main___at_Lean_Elab_Command_applyAttributes___spec__1(x_11, x_22, x_13, x_19, x_7, x_8, x_21);
lean_dec(x_8);
lean_dec(x_13);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
x_24 = !lean_is_exclusive(x_20);
if (x_24 == 0)
{
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_20, 0);
x_26 = lean_ctor_get(x_20, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_20);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
uint8_t x_28; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
x_28 = !lean_is_exclusive(x_16);
if (x_28 == 0)
{
return x_16;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_16, 0);
x_30 = lean_ctor_get(x_16, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_16);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
else
{
uint8_t x_295; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_295 = !lean_is_exclusive(x_10);
if (x_295 == 0)
{
return x_10;
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; 
x_296 = lean_ctor_get(x_10, 0);
x_297 = lean_ctor_get(x_10, 1);
lean_inc(x_297);
lean_inc(x_296);
lean_dec(x_10);
x_298 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_298, 0, x_296);
lean_ctor_set(x_298, 1, x_297);
return x_298;
}
}
}
}
lean_object* l_Lean_Elab_Command_elabAxiom(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = l_Lean_Syntax_getArg(x_2, x_6);
x_8 = lean_unsigned_to_nat(2u);
x_9 = l_Lean_Syntax_getArg(x_2, x_8);
x_10 = l_Lean_Elab_expandDeclSig(x_9);
lean_dec(x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Elab_Command_getLevelNames___rarg(x_4, x_5);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabAxiom___lambda__3), 9, 5);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_11);
lean_closure_set(x_16, 2, x_12);
lean_closure_set(x_16, 3, x_14);
lean_closure_set(x_16, 4, x_2);
x_17 = l_Lean_Elab_Command_withDeclId___rarg(x_7, x_16, x_3, x_4, x_15);
lean_dec(x_7);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_13);
if (x_18 == 0)
{
return x_13;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_13, 0);
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_13);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
lean_object* l_Lean_Elab_Command_elabAxiom___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Command_elabAxiom___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_7);
lean_dec(x_5);
return x_11;
}
}
lean_object* l_Lean_Elab_Command_elabAxiom___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Command_elabAxiom___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
lean_object* _init_l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_1__inductiveSyntaxToView___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid 'protected' constructor in a 'private' inductive datatype");
return x_1;
}
}
lean_object* _init_l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_1__inductiveSyntaxToView___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_1__inductiveSyntaxToView___spec__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_1__inductiveSyntaxToView___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_1__inductiveSyntaxToView___spec__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_1__inductiveSyntaxToView___spec__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid 'private' constructor in a 'private' inductive datatype");
return x_1;
}
}
lean_object* _init_l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_1__inductiveSyntaxToView___spec__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_1__inductiveSyntaxToView___spec__1___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_1__inductiveSyntaxToView___spec__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_1__inductiveSyntaxToView___spec__1___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_1__inductiveSyntaxToView___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_4);
x_9 = lean_nat_dec_lt(x_3, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_3);
x_10 = x_4;
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_12 = lean_array_fget(x_4, x_3);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_fset(x_4, x_3, x_13);
x_28 = x_12;
x_29 = lean_unsigned_to_nat(1u);
x_30 = l_Lean_Syntax_getArg(x_28, x_29);
x_31 = lean_ctor_get(x_5, 0);
x_32 = lean_ctor_get(x_5, 1);
x_33 = lean_ctor_get(x_5, 2);
x_34 = lean_ctor_get(x_5, 3);
x_35 = lean_ctor_get(x_5, 4);
x_36 = lean_ctor_get(x_5, 5);
x_37 = lean_ctor_get(x_5, 6);
x_38 = l_Lean_Elab_replaceRef(x_28, x_37);
lean_inc(x_38);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
x_39 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_39, 0, x_31);
lean_ctor_set(x_39, 1, x_32);
lean_ctor_set(x_39, 2, x_33);
lean_ctor_set(x_39, 3, x_34);
lean_ctor_set(x_39, 4, x_35);
lean_ctor_set(x_39, 5, x_36);
lean_ctor_set(x_39, 6, x_38);
lean_inc(x_39);
x_40 = l_Lean_Elab_Command_elabModifiers(x_30, x_39, x_6, x_7);
lean_dec(x_30);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_97; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_97 = l_Lean_Elab_Command_Modifiers_isPrivate(x_41);
if (x_97 == 0)
{
uint8_t x_98; 
x_98 = l_Lean_Elab_Command_Modifiers_isProtected(x_41);
if (x_98 == 0)
{
x_43 = x_42;
goto block_96;
}
else
{
uint8_t x_99; 
x_99 = l_Lean_Elab_Command_Modifiers_isPrivate(x_1);
if (x_99 == 0)
{
x_43 = x_42;
goto block_96;
}
else
{
lean_object* x_100; lean_object* x_101; uint8_t x_102; 
lean_dec(x_41);
lean_dec(x_38);
lean_dec(x_28);
x_100 = l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_1__inductiveSyntaxToView___spec__1___closed__3;
x_101 = l_Lean_Elab_Command_throwError___rarg(x_100, x_39, x_6, x_42);
x_102 = !lean_is_exclusive(x_101);
if (x_102 == 0)
{
x_15 = x_101;
goto block_27;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_101, 0);
x_104 = lean_ctor_get(x_101, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_101);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
x_15 = x_105;
goto block_27;
}
}
}
}
else
{
uint8_t x_106; 
x_106 = l_Lean_Elab_Command_Modifiers_isPrivate(x_1);
if (x_106 == 0)
{
x_43 = x_42;
goto block_96;
}
else
{
lean_object* x_107; lean_object* x_108; uint8_t x_109; 
lean_dec(x_41);
lean_dec(x_38);
lean_dec(x_28);
x_107 = l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_1__inductiveSyntaxToView___spec__1___closed__6;
x_108 = l_Lean_Elab_Command_throwError___rarg(x_107, x_39, x_6, x_42);
x_109 = !lean_is_exclusive(x_108);
if (x_109 == 0)
{
x_15 = x_108;
goto block_27;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_108, 0);
x_111 = lean_ctor_get(x_108, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_108);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
x_15 = x_112;
goto block_27;
}
}
}
block_96:
{
lean_object* x_44; 
x_44 = l_Lean_Elab_Command_checkValidCtorModifier(x_41, x_39, x_6, x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_unsigned_to_nat(2u);
x_47 = l_Lean_Syntax_getIdAt(x_28, x_46);
x_48 = l_Lean_Name_append___main(x_2, x_47);
x_49 = l_Lean_Syntax_getArg(x_28, x_46);
x_50 = lean_ctor_get_uint8(x_41, sizeof(void*)*2);
x_51 = l_Lean_Elab_replaceRef(x_49, x_38);
lean_dec(x_38);
lean_dec(x_49);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
x_52 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_52, 0, x_31);
lean_ctor_set(x_52, 1, x_32);
lean_ctor_set(x_52, 2, x_33);
lean_ctor_set(x_52, 3, x_34);
lean_ctor_set(x_52, 4, x_35);
lean_ctor_set(x_52, 5, x_36);
lean_ctor_set(x_52, 6, x_51);
x_53 = l_Lean_Elab_Command_applyVisibility(x_50, x_48, x_52, x_6, x_45);
if (lean_obj_tag(x_53) == 0)
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_55 = lean_ctor_get(x_53, 0);
x_56 = lean_unsigned_to_nat(3u);
x_57 = l_Lean_Syntax_getArg(x_28, x_56);
x_58 = l_Lean_Syntax_isNone(x_57);
lean_dec(x_57);
x_59 = lean_unsigned_to_nat(4u);
x_60 = l_Lean_Syntax_getArg(x_28, x_59);
x_61 = l_Lean_Elab_expandOptDeclSig(x_60);
lean_dec(x_60);
if (x_58 == 0)
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = 1;
x_65 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_65, 0, x_28);
lean_ctor_set(x_65, 1, x_41);
lean_ctor_set(x_65, 2, x_55);
lean_ctor_set(x_65, 3, x_62);
lean_ctor_set(x_65, 4, x_63);
lean_ctor_set_uint8(x_65, sizeof(void*)*5, x_64);
lean_ctor_set(x_53, 0, x_65);
x_15 = x_53;
goto block_27;
}
else
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_61, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_61, 1);
lean_inc(x_67);
lean_dec(x_61);
x_68 = 0;
x_69 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_69, 0, x_28);
lean_ctor_set(x_69, 1, x_41);
lean_ctor_set(x_69, 2, x_55);
lean_ctor_set(x_69, 3, x_66);
lean_ctor_set(x_69, 4, x_67);
lean_ctor_set_uint8(x_69, sizeof(void*)*5, x_68);
lean_ctor_set(x_53, 0, x_69);
x_15 = x_53;
goto block_27;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_70 = lean_ctor_get(x_53, 0);
x_71 = lean_ctor_get(x_53, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_53);
x_72 = lean_unsigned_to_nat(3u);
x_73 = l_Lean_Syntax_getArg(x_28, x_72);
x_74 = l_Lean_Syntax_isNone(x_73);
lean_dec(x_73);
x_75 = lean_unsigned_to_nat(4u);
x_76 = l_Lean_Syntax_getArg(x_28, x_75);
x_77 = l_Lean_Elab_expandOptDeclSig(x_76);
lean_dec(x_76);
if (x_74 == 0)
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = 1;
x_81 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_81, 0, x_28);
lean_ctor_set(x_81, 1, x_41);
lean_ctor_set(x_81, 2, x_70);
lean_ctor_set(x_81, 3, x_78);
lean_ctor_set(x_81, 4, x_79);
lean_ctor_set_uint8(x_81, sizeof(void*)*5, x_80);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_71);
x_15 = x_82;
goto block_27;
}
else
{
lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; lean_object* x_87; 
x_83 = lean_ctor_get(x_77, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_77, 1);
lean_inc(x_84);
lean_dec(x_77);
x_85 = 0;
x_86 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_86, 0, x_28);
lean_ctor_set(x_86, 1, x_41);
lean_ctor_set(x_86, 2, x_70);
lean_ctor_set(x_86, 3, x_83);
lean_ctor_set(x_86, 4, x_84);
lean_ctor_set_uint8(x_86, sizeof(void*)*5, x_85);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_71);
x_15 = x_87;
goto block_27;
}
}
}
else
{
uint8_t x_88; 
lean_dec(x_41);
lean_dec(x_28);
x_88 = !lean_is_exclusive(x_53);
if (x_88 == 0)
{
x_15 = x_53;
goto block_27;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_53, 0);
x_90 = lean_ctor_get(x_53, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_53);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
x_15 = x_91;
goto block_27;
}
}
}
else
{
uint8_t x_92; 
lean_dec(x_41);
lean_dec(x_38);
lean_dec(x_28);
x_92 = !lean_is_exclusive(x_44);
if (x_92 == 0)
{
x_15 = x_44;
goto block_27;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_44, 0);
x_94 = lean_ctor_get(x_44, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_44);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
x_15 = x_95;
goto block_27;
}
}
}
}
else
{
uint8_t x_113; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_28);
x_113 = !lean_is_exclusive(x_40);
if (x_113 == 0)
{
x_15 = x_40;
goto block_27;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_40, 0);
x_115 = lean_ctor_get(x_40, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_40);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
x_15 = x_116;
goto block_27;
}
}
block_27:
{
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_3, x_18);
x_20 = x_16;
x_21 = lean_array_fset(x_14, x_3, x_20);
lean_dec(x_3);
x_3 = x_19;
x_4 = x_21;
x_7 = x_17;
goto _start;
}
else
{
uint8_t x_23; 
lean_dec(x_14);
lean_dec(x_3);
x_23 = !lean_is_exclusive(x_15);
if (x_23 == 0)
{
return x_15;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_15, 0);
x_25 = lean_ctor_get(x_15, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_15);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
}
}
lean_object* l___private_Lean_Elab_Declaration_1__inductiveSyntaxToView___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Command_getLevelNames___rarg(x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_7);
lean_inc(x_6);
x_13 = l_Lean_Elab_Command_mkDeclName(x_1, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_unsigned_to_nat(2u);
x_17 = lean_nat_add(x_2, x_16);
x_18 = l_Lean_Syntax_getArg(x_3, x_17);
lean_dec(x_17);
x_19 = l_Lean_Syntax_getArgs(x_18);
lean_dec(x_18);
x_20 = x_19;
x_21 = lean_unsigned_to_nat(0u);
lean_inc(x_14);
lean_inc(x_1);
x_22 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_1__inductiveSyntaxToView___spec__1___boxed), 7, 4);
lean_closure_set(x_22, 0, x_1);
lean_closure_set(x_22, 1, x_14);
lean_closure_set(x_22, 2, x_21);
lean_closure_set(x_22, 3, x_20);
x_23 = x_22;
x_24 = lean_apply_3(x_23, x_7, x_8, x_15);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_27, 0, x_3);
lean_ctor_set(x_27, 1, x_1);
lean_ctor_set(x_27, 2, x_6);
lean_ctor_set(x_27, 3, x_14);
lean_ctor_set(x_27, 4, x_11);
lean_ctor_set(x_27, 5, x_4);
lean_ctor_set(x_27, 6, x_5);
lean_ctor_set(x_27, 7, x_26);
lean_ctor_set(x_24, 0, x_27);
return x_24;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_24, 0);
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_24);
x_30 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_30, 0, x_3);
lean_ctor_set(x_30, 1, x_1);
lean_ctor_set(x_30, 2, x_6);
lean_ctor_set(x_30, 3, x_14);
lean_ctor_set(x_30, 4, x_11);
lean_ctor_set(x_30, 5, x_4);
lean_ctor_set(x_30, 6, x_5);
lean_ctor_set(x_30, 7, x_28);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_24);
if (x_32 == 0)
{
return x_24;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_24, 0);
x_34 = lean_ctor_get(x_24, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_24);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_13);
if (x_36 == 0)
{
return x_13;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_13, 0);
x_38 = lean_ctor_get(x_13, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_13);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_10);
if (x_40 == 0)
{
return x_10;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_10, 0);
x_42 = lean_ctor_get(x_10, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_10);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
lean_object* l___private_Lean_Elab_Declaration_1__inductiveSyntaxToView(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_4);
x_7 = l_Lean_Elab_Command_checkValidInductiveModifier(x_1, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_3, x_9);
x_11 = l_Lean_Syntax_getArg(x_2, x_10);
lean_dec(x_10);
x_12 = l_Lean_Elab_expandOptDeclSig(x_11);
lean_dec(x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Syntax_getArg(x_2, x_3);
x_16 = lean_alloc_closure((void*)(l___private_Lean_Elab_Declaration_1__inductiveSyntaxToView___lambda__1___boxed), 9, 5);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_3);
lean_closure_set(x_16, 2, x_2);
lean_closure_set(x_16, 3, x_13);
lean_closure_set(x_16, 4, x_14);
x_17 = l_Lean_Elab_Command_withDeclId___rarg(x_15, x_16, x_4, x_5, x_8);
lean_dec(x_15);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_7);
if (x_18 == 0)
{
return x_7;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_7, 0);
x_20 = lean_ctor_get(x_7, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_7);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_1__inductiveSyntaxToView___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_1__inductiveSyntaxToView___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Lean_Elab_Declaration_1__inductiveSyntaxToView___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Declaration_1__inductiveSyntaxToView___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_10;
}
}
lean_object* l___private_Lean_Elab_Declaration_2__classInductiveSyntaxToView(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_unsigned_to_nat(2u);
x_7 = l___private_Lean_Elab_Declaration_1__inductiveSyntaxToView(x_1, x_2, x_6, x_3, x_4, x_5);
return x_7;
}
}
lean_object* l_Lean_Elab_Command_elabInductive(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_unsigned_to_nat(1u);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l___private_Lean_Elab_Declaration_1__inductiveSyntaxToView(x_1, x_2, x_6, x_3, x_4, x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_mkOptionalNode___closed__2;
x_11 = lean_array_push(x_10, x_8);
x_12 = l_Lean_Elab_Command_elabInductiveViews(x_11, x_3, x_4, x_9);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_4);
lean_dec(x_3);
x_13 = !lean_is_exclusive(x_7);
if (x_13 == 0)
{
return x_7;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_7, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_7);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
lean_object* l_Lean_Elab_Command_elabClassInductive(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = l_Lean_Elab_Command_elabStructure___closed__8;
x_7 = l_Lean_Elab_Command_Modifiers_addAttribute(x_1, x_6);
x_8 = lean_unsigned_to_nat(2u);
lean_inc(x_4);
lean_inc(x_3);
x_9 = l___private_Lean_Elab_Declaration_1__inductiveSyntaxToView(x_7, x_2, x_8, x_3, x_4, x_5);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_mkOptionalNode___closed__2;
x_13 = lean_array_push(x_12, x_10);
x_14 = l_Lean_Elab_Command_elabInductiveViews(x_13, x_3, x_4, x_11);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_4);
lean_dec(x_3);
x_15 = !lean_is_exclusive(x_9);
if (x_15 == 0)
{
return x_9;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_9, 0);
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_9);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
lean_object* _init_l_Lean_Elab_Command_elabDeclaration___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected declaration");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_elabDeclaration___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabDeclaration___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_elabDeclaration___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabDeclaration___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_elabDeclaration(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
lean_inc(x_2);
x_7 = l_Lean_Elab_Command_elabModifiers(x_6, x_2, x_3, x_4);
lean_dec(x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
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
x_21 = l_Lean_Parser_Command_instance___elambda__1___closed__2;
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
lean_dec(x_11);
lean_dec(x_8);
x_33 = l_Lean_Elab_Command_elabDeclaration___closed__3;
x_34 = l_Lean_Elab_Command_throwError___rarg(x_33, x_2, x_3, x_9);
lean_dec(x_3);
return x_34;
}
else
{
lean_object* x_35; 
x_35 = l_Lean_Elab_Command_elabStructure(x_8, x_11, x_2, x_3, x_9);
return x_35;
}
}
else
{
lean_object* x_36; 
lean_dec(x_12);
x_36 = l_Lean_Elab_Command_elabClassInductive(x_8, x_11, x_2, x_3, x_9);
return x_36;
}
}
else
{
lean_object* x_37; 
lean_dec(x_12);
x_37 = l_Lean_Elab_Command_elabInductive(x_8, x_11, x_2, x_3, x_9);
return x_37;
}
}
else
{
lean_object* x_38; 
lean_dec(x_12);
x_38 = l_Lean_Elab_Command_elabExample(x_8, x_11, x_2, x_3, x_9);
return x_38;
}
}
else
{
lean_object* x_39; 
lean_dec(x_12);
x_39 = l_Lean_Elab_Command_elabAxiom(x_8, x_11, x_2, x_3, x_9);
return x_39;
}
}
else
{
lean_object* x_40; 
lean_dec(x_12);
x_40 = l_Lean_Elab_Command_elabInstance(x_8, x_11, x_2, x_3, x_9);
return x_40;
}
}
else
{
lean_object* x_41; 
lean_dec(x_12);
x_41 = l_Lean_Elab_Command_elabConstant(x_8, x_11, x_2, x_3, x_9);
return x_41;
}
}
else
{
lean_object* x_42; 
lean_dec(x_12);
x_42 = l_Lean_Elab_Command_elabTheorem(x_8, x_11, x_2, x_3, x_9);
return x_42;
}
}
else
{
lean_object* x_43; 
lean_dec(x_12);
x_43 = l_Lean_Elab_Command_elabDef(x_8, x_11, x_2, x_3, x_9);
return x_43;
}
}
else
{
lean_object* x_44; 
lean_dec(x_12);
x_44 = l_Lean_Elab_Command_elabAbbrev(x_8, x_11, x_2, x_3, x_9);
return x_44;
}
}
else
{
uint8_t x_45; 
lean_dec(x_3);
lean_dec(x_2);
x_45 = !lean_is_exclusive(x_7);
if (x_45 == 0)
{
return x_7;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_7, 0);
x_47 = lean_ctor_get(x_7, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_7);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
lean_object* l_Lean_Elab_Command_elabDeclaration___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabDeclaration(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabDeclaration___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabDeclaration___boxed), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Command_elabDeclaration(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = l_Lean_Parser_Command_declaration___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_elabDeclaration___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Elab_Declaration_3__isMutualInductive___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_4);
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_array_fget(x_2, x_4);
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Syntax_getArg(x_7, x_8);
lean_dec(x_7);
x_10 = l_Lean_Syntax_getKind(x_9);
x_11 = l_Lean_Parser_Command_inductive___elambda__1___closed__2;
x_12 = lean_name_eq(x_10, x_11);
lean_dec(x_10);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_4);
x_13 = 1;
return x_13;
}
else
{
lean_object* x_14; 
x_14 = lean_nat_add(x_4, x_8);
lean_dec(x_4);
x_4 = x_14;
goto _start;
}
}
}
}
uint8_t l___private_Lean_Elab_Declaration_3__isMutualInductive(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Lean_Syntax_getArg(x_1, x_2);
x_4 = l_Lean_Syntax_getArgs(x_3);
lean_dec(x_3);
x_5 = lean_array_get_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Array_anyRangeMAux___main___at___private_Lean_Elab_Declaration_3__isMutualInductive___spec__1(x_1, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Elab_Declaration_3__isMutualInductive___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Array_anyRangeMAux___main___at___private_Lean_Elab_Declaration_3__isMutualInductive___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l___private_Lean_Elab_Declaration_3__isMutualInductive___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_Declaration_3__isMutualInductive(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_4__elabMutualInductive___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_1, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_8 = x_2;
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_array_fget(x_2, x_1);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_array_fset(x_2, x_1, x_11);
x_13 = x_10;
x_14 = l_Lean_Syntax_getArg(x_13, x_11);
lean_inc(x_3);
x_15 = l_Lean_Elab_Command_elabModifiers(x_14, x_3, x_4, x_5);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_unsigned_to_nat(1u);
x_19 = l_Lean_Syntax_getArg(x_13, x_18);
lean_dec(x_13);
lean_inc(x_4);
lean_inc(x_3);
x_20 = l___private_Lean_Elab_Declaration_1__inductiveSyntaxToView(x_16, x_19, x_18, x_3, x_4, x_17);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_nat_add(x_1, x_18);
x_24 = x_21;
x_25 = lean_array_fset(x_12, x_1, x_24);
lean_dec(x_1);
x_1 = x_23;
x_2 = x_25;
x_5 = x_22;
goto _start;
}
else
{
uint8_t x_27; 
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_20);
if (x_27 == 0)
{
return x_20;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_20, 0);
x_29 = lean_ctor_get(x_20, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_20);
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
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_15);
if (x_31 == 0)
{
return x_15;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_15, 0);
x_33 = lean_ctor_get(x_15, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_15);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Declaration_4__elabMutualInductive(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = x_1;
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_4__elabMutualInductive___spec__1), 5, 2);
lean_closure_set(x_7, 0, x_6);
lean_closure_set(x_7, 1, x_5);
x_8 = x_7;
lean_inc(x_3);
lean_inc(x_2);
x_9 = lean_apply_3(x_8, x_2, x_3, x_4);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Elab_Command_elabInductiveViews(x_10, x_2, x_3, x_11);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_3);
lean_dec(x_2);
x_13 = !lean_is_exclusive(x_9);
if (x_13 == 0)
{
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 0);
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_9);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
uint8_t l___private_Lean_Elab_Declaration_5__isMutualPreambleCommand(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l_Lean_Syntax_getKind(x_1);
x_3 = l_Lean_Parser_Command_variable___elambda__1___closed__2;
x_4 = lean_name_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Parser_Command_variables___elambda__1___closed__2;
x_6 = lean_name_eq(x_2, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_Parser_Command_universe___elambda__1___closed__2;
x_8 = lean_name_eq(x_2, x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_Parser_Command_universes___elambda__1___closed__2;
x_10 = lean_name_eq(x_2, x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Parser_Command_check___elambda__1___closed__2;
x_12 = lean_name_eq(x_2, x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_Lean_Parser_Command_set__option___elambda__1___closed__2;
x_14 = lean_name_eq(x_2, x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = l_Lean_Parser_Command_open___elambda__1___closed__2;
x_16 = lean_name_eq(x_2, x_15);
lean_dec(x_2);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_2);
x_17 = 1;
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec(x_2);
x_18 = 1;
return x_18;
}
}
else
{
uint8_t x_19; 
lean_dec(x_2);
x_19 = 1;
return x_19;
}
}
else
{
uint8_t x_20; 
lean_dec(x_2);
x_20 = 1;
return x_20;
}
}
else
{
uint8_t x_21; 
lean_dec(x_2);
x_21 = 1;
return x_21;
}
}
else
{
uint8_t x_22; 
lean_dec(x_2);
x_22 = 1;
return x_22;
}
}
}
lean_object* l___private_Lean_Elab_Declaration_5__isMutualPreambleCommand___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_Declaration_5__isMutualPreambleCommand(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Declaration_6__splitMutualPreamble___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_nat_dec_lt(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_fget(x_1, x_2);
x_7 = l___private_Lean_Elab_Declaration_5__isMutualPreambleCommand(x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_2, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_Array_extract___rarg(x_1, x_8, x_2);
x_11 = l_Array_extract___rarg(x_1, x_2, x_3);
lean_dec(x_3);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
else
{
lean_object* x_14; 
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_box(0);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_3);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_2, x_15);
lean_dec(x_2);
x_2 = x_16;
goto _start;
}
}
}
}
lean_object* l___private_Lean_Elab_Declaration_6__splitMutualPreamble___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Elab_Declaration_6__splitMutualPreamble___main(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Declaration_6__splitMutualPreamble(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Elab_Declaration_6__splitMutualPreamble___main(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Declaration_6__splitMutualPreamble___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Elab_Declaration_6__splitMutualPreamble(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Declaration_7__expandMutualPreamble_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SourceInfo_inhabited___closed__1;
x_2 = l_Lean_Parser_Command_section___elambda__1___closed__1;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Declaration_7__expandMutualPreamble_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l___private_Lean_Elab_Declaration_7__expandMutualPreamble_x3f___closed__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Declaration_7__expandMutualPreamble_x3f___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Declaration_7__expandMutualPreamble_x3f___closed__2;
x_2 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Declaration_7__expandMutualPreamble_x3f___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Command_section___elambda__1___closed__2;
x_2 = l___private_Lean_Elab_Declaration_7__expandMutualPreamble_x3f___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Declaration_7__expandMutualPreamble_x3f___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SourceInfo_inhabited___closed__1;
x_2 = l_Lean_Parser_Command_mutual___elambda__1___closed__1;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Declaration_7__expandMutualPreamble_x3f___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l___private_Lean_Elab_Declaration_7__expandMutualPreamble_x3f___closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Declaration_7__expandMutualPreamble_x3f___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SourceInfo_inhabited___closed__1;
x_2 = l_Lean_Parser_Term_tacticBlock___elambda__1___closed__7;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Declaration_7__expandMutualPreamble_x3f___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l___private_Lean_Elab_Declaration_7__expandMutualPreamble_x3f___closed__7;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Declaration_7__expandMutualPreamble_x3f___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Declaration_7__expandMutualPreamble_x3f___closed__8;
x_2 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Declaration_7__expandMutualPreamble_x3f___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Command_end___elambda__1___closed__1;
x_2 = l___private_Lean_Elab_Declaration_7__expandMutualPreamble_x3f___closed__9;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Declaration_7__expandMutualPreamble_x3f___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkOptionalNode___closed__2;
x_2 = l___private_Lean_Elab_Declaration_7__expandMutualPreamble_x3f___closed__4;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Declaration_7__expandMutualPreamble_x3f___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkOptionalNode___closed__2;
x_2 = l___private_Lean_Elab_Declaration_7__expandMutualPreamble_x3f___closed__10;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Declaration_7__expandMutualPreamble_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = l_Lean_Syntax_getArg(x_1, x_4);
x_6 = l_Lean_Syntax_getArgs(x_5);
lean_dec(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l___private_Lean_Elab_Declaration_6__splitMutualPreamble___main(x_6, x_7);
lean_dec(x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_3);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Array_empty___closed__1;
x_16 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_14, x_14, x_7, x_15);
lean_dec(x_14);
x_17 = l_Lean_nullKind___closed__2;
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l___private_Lean_Elab_Declaration_7__expandMutualPreamble_x3f___closed__6;
x_20 = lean_array_push(x_19, x_18);
x_21 = l___private_Lean_Elab_Declaration_7__expandMutualPreamble_x3f___closed__7;
x_22 = lean_array_push(x_20, x_21);
x_23 = l_Lean_Parser_Command_mutual___elambda__1___closed__2;
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = l___private_Lean_Elab_Declaration_7__expandMutualPreamble_x3f___closed__11;
x_26 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_13, x_13, x_7, x_25);
lean_dec(x_13);
x_27 = l_Lean_mkOptionalNode___closed__2;
x_28 = lean_array_push(x_27, x_24);
x_29 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_28, x_28, x_7, x_26);
lean_dec(x_28);
x_30 = l___private_Lean_Elab_Declaration_7__expandMutualPreamble_x3f___closed__12;
x_31 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_30, x_30, x_7, x_29);
x_32 = l_Lean_nullKind;
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
lean_ctor_set(x_8, 0, x_33);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_8);
lean_ctor_set(x_34, 1, x_3);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_35 = lean_ctor_get(x_8, 0);
lean_inc(x_35);
lean_dec(x_8);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Array_empty___closed__1;
x_39 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_37, x_37, x_7, x_38);
lean_dec(x_37);
x_40 = l_Lean_nullKind___closed__2;
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
x_42 = l___private_Lean_Elab_Declaration_7__expandMutualPreamble_x3f___closed__6;
x_43 = lean_array_push(x_42, x_41);
x_44 = l___private_Lean_Elab_Declaration_7__expandMutualPreamble_x3f___closed__7;
x_45 = lean_array_push(x_43, x_44);
x_46 = l_Lean_Parser_Command_mutual___elambda__1___closed__2;
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
x_48 = l___private_Lean_Elab_Declaration_7__expandMutualPreamble_x3f___closed__11;
x_49 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_36, x_36, x_7, x_48);
lean_dec(x_36);
x_50 = l_Lean_mkOptionalNode___closed__2;
x_51 = lean_array_push(x_50, x_47);
x_52 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_51, x_51, x_7, x_49);
lean_dec(x_51);
x_53 = l___private_Lean_Elab_Declaration_7__expandMutualPreamble_x3f___closed__12;
x_54 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_53, x_53, x_7, x_52);
x_55 = l_Lean_nullKind;
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_3);
return x_58;
}
}
}
}
lean_object* l___private_Lean_Elab_Declaration_7__expandMutualPreamble_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_Declaration_7__expandMutualPreamble_x3f(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l_Lean_Elab_Command_elabMutual___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid mutual block");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_elabMutual___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabMutual___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_elabMutual___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabMutual___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_elabMutual(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = l_Lean_Elab_Command_getCurrMacroScope(x_2, x_3, x_4);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l_Lean_Elab_Command_getEnv___rarg(x_3, x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_io_ref_get(x_3, x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_ctor_get(x_39, 3);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_ctor_get(x_2, 2);
lean_inc(x_42);
x_43 = lean_io_ref_get(x_3, x_40);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_ctor_get(x_44, 4);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_environment_main_module(x_36);
x_48 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_33);
lean_ctor_set(x_48, 2, x_42);
lean_ctor_set(x_48, 3, x_46);
x_49 = l___private_Lean_Elab_Declaration_7__expandMutualPreamble_x3f(x_1, x_48, x_41);
lean_dec(x_48);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_io_ref_take(x_3, x_45);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = !lean_is_exclusive(x_53);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_53, 3);
lean_dec(x_56);
lean_ctor_set(x_53, 3, x_51);
x_57 = lean_io_ref_set(x_3, x_53, x_54);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
x_5 = x_50;
x_6 = x_58;
goto block_31;
}
else
{
uint8_t x_59; 
lean_dec(x_50);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_57);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_60 = lean_ctor_get(x_57, 0);
x_61 = lean_box(0);
x_62 = lean_io_error_to_string(x_60);
x_63 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_63, 0, x_62);
x_64 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_64, 0, x_63);
x_65 = l_Lean_Elab_Command_monadIOAux___rarg___closed__1;
x_66 = l_Lean_PrettyPrinter_Formatter_withPosition_formatter___closed__1;
x_67 = 2;
x_68 = l_String_splitAux___main___closed__1;
x_69 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_69, 0, x_65);
lean_ctor_set(x_69, 1, x_66);
lean_ctor_set(x_69, 2, x_61);
lean_ctor_set(x_69, 3, x_68);
lean_ctor_set(x_69, 4, x_64);
lean_ctor_set_uint8(x_69, sizeof(void*)*5, x_67);
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_57, 0, x_70);
return x_57;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_71 = lean_ctor_get(x_57, 0);
x_72 = lean_ctor_get(x_57, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_57);
x_73 = lean_box(0);
x_74 = lean_io_error_to_string(x_71);
x_75 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_75, 0, x_74);
x_76 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_76, 0, x_75);
x_77 = l_Lean_Elab_Command_monadIOAux___rarg___closed__1;
x_78 = l_Lean_PrettyPrinter_Formatter_withPosition_formatter___closed__1;
x_79 = 2;
x_80 = l_String_splitAux___main___closed__1;
x_81 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_81, 0, x_77);
lean_ctor_set(x_81, 1, x_78);
lean_ctor_set(x_81, 2, x_73);
lean_ctor_set(x_81, 3, x_80);
lean_ctor_set(x_81, 4, x_76);
lean_ctor_set_uint8(x_81, sizeof(void*)*5, x_79);
x_82 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_82, 0, x_81);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_72);
return x_83;
}
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_84 = lean_ctor_get(x_53, 0);
x_85 = lean_ctor_get(x_53, 1);
x_86 = lean_ctor_get(x_53, 2);
x_87 = lean_ctor_get(x_53, 4);
x_88 = lean_ctor_get(x_53, 5);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_53);
x_89 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_89, 0, x_84);
lean_ctor_set(x_89, 1, x_85);
lean_ctor_set(x_89, 2, x_86);
lean_ctor_set(x_89, 3, x_51);
lean_ctor_set(x_89, 4, x_87);
lean_ctor_set(x_89, 5, x_88);
x_90 = lean_io_ref_set(x_3, x_89, x_54);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; 
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec(x_90);
x_5 = x_50;
x_6 = x_91;
goto block_31;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_50);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_92 = lean_ctor_get(x_90, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_90, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_94 = x_90;
} else {
 lean_dec_ref(x_90);
 x_94 = lean_box(0);
}
x_95 = lean_box(0);
x_96 = lean_io_error_to_string(x_92);
x_97 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_97, 0, x_96);
x_98 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_98, 0, x_97);
x_99 = l_Lean_Elab_Command_monadIOAux___rarg___closed__1;
x_100 = l_Lean_PrettyPrinter_Formatter_withPosition_formatter___closed__1;
x_101 = 2;
x_102 = l_String_splitAux___main___closed__1;
x_103 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_103, 0, x_99);
lean_ctor_set(x_103, 1, x_100);
lean_ctor_set(x_103, 2, x_95);
lean_ctor_set(x_103, 3, x_102);
lean_ctor_set(x_103, 4, x_98);
lean_ctor_set_uint8(x_103, sizeof(void*)*5, x_101);
x_104 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_104, 0, x_103);
if (lean_is_scalar(x_94)) {
 x_105 = lean_alloc_ctor(1, 2, 0);
} else {
 x_105 = x_94;
}
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_93);
return x_105;
}
}
}
else
{
uint8_t x_106; 
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_106 = !lean_is_exclusive(x_52);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_107 = lean_ctor_get(x_52, 0);
x_108 = lean_box(0);
x_109 = lean_io_error_to_string(x_107);
x_110 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_110, 0, x_109);
x_111 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_111, 0, x_110);
x_112 = l_Lean_Elab_Command_monadIOAux___rarg___closed__1;
x_113 = l_Lean_PrettyPrinter_Formatter_withPosition_formatter___closed__1;
x_114 = 2;
x_115 = l_String_splitAux___main___closed__1;
x_116 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_116, 0, x_112);
lean_ctor_set(x_116, 1, x_113);
lean_ctor_set(x_116, 2, x_108);
lean_ctor_set(x_116, 3, x_115);
lean_ctor_set(x_116, 4, x_111);
lean_ctor_set_uint8(x_116, sizeof(void*)*5, x_114);
x_117 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_52, 0, x_117);
return x_52;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_118 = lean_ctor_get(x_52, 0);
x_119 = lean_ctor_get(x_52, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_52);
x_120 = lean_box(0);
x_121 = lean_io_error_to_string(x_118);
x_122 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_122, 0, x_121);
x_123 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_123, 0, x_122);
x_124 = l_Lean_Elab_Command_monadIOAux___rarg___closed__1;
x_125 = l_Lean_PrettyPrinter_Formatter_withPosition_formatter___closed__1;
x_126 = 2;
x_127 = l_String_splitAux___main___closed__1;
x_128 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_128, 0, x_124);
lean_ctor_set(x_128, 1, x_125);
lean_ctor_set(x_128, 2, x_120);
lean_ctor_set(x_128, 3, x_127);
lean_ctor_set(x_128, 4, x_123);
lean_ctor_set_uint8(x_128, sizeof(void*)*5, x_126);
x_129 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_129, 0, x_128);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_119);
return x_130;
}
}
}
else
{
uint8_t x_131; 
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_36);
lean_dec(x_33);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_131 = !lean_is_exclusive(x_43);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_132 = lean_ctor_get(x_43, 0);
x_133 = lean_box(0);
x_134 = lean_io_error_to_string(x_132);
x_135 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_135, 0, x_134);
x_136 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_136, 0, x_135);
x_137 = l_Lean_Elab_Command_monadIOAux___rarg___closed__1;
x_138 = l_Lean_PrettyPrinter_Formatter_withPosition_formatter___closed__1;
x_139 = 2;
x_140 = l_String_splitAux___main___closed__1;
x_141 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_141, 0, x_137);
lean_ctor_set(x_141, 1, x_138);
lean_ctor_set(x_141, 2, x_133);
lean_ctor_set(x_141, 3, x_140);
lean_ctor_set(x_141, 4, x_136);
lean_ctor_set_uint8(x_141, sizeof(void*)*5, x_139);
x_142 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_43, 0, x_142);
return x_43;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_143 = lean_ctor_get(x_43, 0);
x_144 = lean_ctor_get(x_43, 1);
lean_inc(x_144);
lean_inc(x_143);
lean_dec(x_43);
x_145 = lean_box(0);
x_146 = lean_io_error_to_string(x_143);
x_147 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_147, 0, x_146);
x_148 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_148, 0, x_147);
x_149 = l_Lean_Elab_Command_monadIOAux___rarg___closed__1;
x_150 = l_Lean_PrettyPrinter_Formatter_withPosition_formatter___closed__1;
x_151 = 2;
x_152 = l_String_splitAux___main___closed__1;
x_153 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_153, 0, x_149);
lean_ctor_set(x_153, 1, x_150);
lean_ctor_set(x_153, 2, x_145);
lean_ctor_set(x_153, 3, x_152);
lean_ctor_set(x_153, 4, x_148);
lean_ctor_set_uint8(x_153, sizeof(void*)*5, x_151);
x_154 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_154, 0, x_153);
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_144);
return x_155;
}
}
}
else
{
uint8_t x_156; 
lean_dec(x_36);
lean_dec(x_33);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_156 = !lean_is_exclusive(x_38);
if (x_156 == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; uint8_t x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_157 = lean_ctor_get(x_38, 0);
x_158 = lean_box(0);
x_159 = lean_io_error_to_string(x_157);
x_160 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_160, 0, x_159);
x_161 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_161, 0, x_160);
x_162 = l_Lean_Elab_Command_monadIOAux___rarg___closed__1;
x_163 = l_Lean_PrettyPrinter_Formatter_withPosition_formatter___closed__1;
x_164 = 2;
x_165 = l_String_splitAux___main___closed__1;
x_166 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_166, 0, x_162);
lean_ctor_set(x_166, 1, x_163);
lean_ctor_set(x_166, 2, x_158);
lean_ctor_set(x_166, 3, x_165);
lean_ctor_set(x_166, 4, x_161);
lean_ctor_set_uint8(x_166, sizeof(void*)*5, x_164);
x_167 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_38, 0, x_167);
return x_38;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_168 = lean_ctor_get(x_38, 0);
x_169 = lean_ctor_get(x_38, 1);
lean_inc(x_169);
lean_inc(x_168);
lean_dec(x_38);
x_170 = lean_box(0);
x_171 = lean_io_error_to_string(x_168);
x_172 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_172, 0, x_171);
x_173 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_173, 0, x_172);
x_174 = l_Lean_Elab_Command_monadIOAux___rarg___closed__1;
x_175 = l_Lean_PrettyPrinter_Formatter_withPosition_formatter___closed__1;
x_176 = 2;
x_177 = l_String_splitAux___main___closed__1;
x_178 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_178, 0, x_174);
lean_ctor_set(x_178, 1, x_175);
lean_ctor_set(x_178, 2, x_170);
lean_ctor_set(x_178, 3, x_177);
lean_ctor_set(x_178, 4, x_173);
lean_ctor_set_uint8(x_178, sizeof(void*)*5, x_176);
x_179 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_179, 0, x_178);
x_180 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_169);
return x_180;
}
}
}
else
{
uint8_t x_181; 
lean_dec(x_33);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_181 = !lean_is_exclusive(x_35);
if (x_181 == 0)
{
return x_35;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_182 = lean_ctor_get(x_35, 0);
x_183 = lean_ctor_get(x_35, 1);
lean_inc(x_183);
lean_inc(x_182);
lean_dec(x_35);
x_184 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_184, 0, x_182);
lean_ctor_set(x_184, 1, x_183);
return x_184;
}
}
block_31:
{
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_7; 
x_7 = l___private_Lean_Elab_Declaration_3__isMutualInductive(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_1);
x_8 = l_Lean_Elab_Command_elabMutual___closed__3;
x_9 = l_Lean_Elab_Command_throwError___rarg(x_8, x_2, x_3, x_6);
lean_dec(x_3);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
lean_dec(x_1);
x_12 = l_Lean_Syntax_getArgs(x_11);
lean_dec(x_11);
x_13 = l___private_Lean_Elab_Declaration_4__elabMutualInductive(x_12, x_2, x_3, x_6);
return x_13;
}
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_5, 0);
lean_inc(x_14);
lean_dec(x_5);
x_15 = !lean_is_exclusive(x_2);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_2, 4);
lean_inc(x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_14);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
lean_ctor_set(x_2, 4, x_18);
x_19 = l_Lean_Elab_Command_elabCommand___main(x_14, x_2, x_3, x_6);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_20 = lean_ctor_get(x_2, 0);
x_21 = lean_ctor_get(x_2, 1);
x_22 = lean_ctor_get(x_2, 2);
x_23 = lean_ctor_get(x_2, 3);
x_24 = lean_ctor_get(x_2, 4);
x_25 = lean_ctor_get(x_2, 5);
x_26 = lean_ctor_get(x_2, 6);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_2);
lean_inc(x_14);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_1);
lean_ctor_set(x_27, 1, x_14);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_24);
x_29 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_29, 0, x_20);
lean_ctor_set(x_29, 1, x_21);
lean_ctor_set(x_29, 2, x_22);
lean_ctor_set(x_29, 3, x_23);
lean_ctor_set(x_29, 4, x_28);
lean_ctor_set(x_29, 5, x_25);
lean_ctor_set(x_29, 6, x_26);
x_30 = l_Lean_Elab_Command_elabCommand___main(x_14, x_29, x_3, x_6);
return x_30;
}
}
}
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabMutual___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabMutual), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Command_elabMutual(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = l_Lean_Parser_Command_mutual___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_elabMutual___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Util_CollectLevelParams(lean_object*);
lean_object* initialize_Lean_Elab_DeclUtil(lean_object*);
lean_object* initialize_Lean_Elab_Definition(lean_object*);
lean_object* initialize_Lean_Elab_Inductive(lean_object*);
lean_object* initialize_Lean_Elab_Structure(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Elab_Declaration(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_CollectLevelParams(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_DeclUtil(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Definition(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Inductive(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Structure(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Command_elabAbbrev___closed__1 = _init_l_Lean_Elab_Command_elabAbbrev___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabAbbrev___closed__1);
l_Lean_Elab_Command_elabAbbrev___closed__2 = _init_l_Lean_Elab_Command_elabAbbrev___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabAbbrev___closed__2);
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
l_Lean_Elab_Command_elabInstance___closed__1 = _init_l_Lean_Elab_Command_elabInstance___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabInstance___closed__1);
l_Lean_Elab_Command_elabInstance___closed__2 = _init_l_Lean_Elab_Command_elabInstance___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabInstance___closed__2);
l_Lean_Elab_Command_elabInstance___closed__3 = _init_l_Lean_Elab_Command_elabInstance___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabInstance___closed__3);
l_Lean_Elab_Command_elabInstance___closed__4 = _init_l_Lean_Elab_Command_elabInstance___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_elabInstance___closed__4);
l_Lean_Elab_Command_elabInstance___closed__5 = _init_l_Lean_Elab_Command_elabInstance___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_elabInstance___closed__5);
l_Lean_Elab_Command_elabExample___closed__1 = _init_l_Lean_Elab_Command_elabExample___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabExample___closed__1);
l_Lean_Elab_Command_elabExample___closed__2 = _init_l_Lean_Elab_Command_elabExample___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabExample___closed__2);
l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_1__inductiveSyntaxToView___spec__1___closed__1 = _init_l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_1__inductiveSyntaxToView___spec__1___closed__1();
lean_mark_persistent(l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_1__inductiveSyntaxToView___spec__1___closed__1);
l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_1__inductiveSyntaxToView___spec__1___closed__2 = _init_l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_1__inductiveSyntaxToView___spec__1___closed__2();
lean_mark_persistent(l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_1__inductiveSyntaxToView___spec__1___closed__2);
l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_1__inductiveSyntaxToView___spec__1___closed__3 = _init_l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_1__inductiveSyntaxToView___spec__1___closed__3();
lean_mark_persistent(l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_1__inductiveSyntaxToView___spec__1___closed__3);
l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_1__inductiveSyntaxToView___spec__1___closed__4 = _init_l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_1__inductiveSyntaxToView___spec__1___closed__4();
lean_mark_persistent(l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_1__inductiveSyntaxToView___spec__1___closed__4);
l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_1__inductiveSyntaxToView___spec__1___closed__5 = _init_l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_1__inductiveSyntaxToView___spec__1___closed__5();
lean_mark_persistent(l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_1__inductiveSyntaxToView___spec__1___closed__5);
l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_1__inductiveSyntaxToView___spec__1___closed__6 = _init_l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_1__inductiveSyntaxToView___spec__1___closed__6();
lean_mark_persistent(l_Array_umapMAux___main___at___private_Lean_Elab_Declaration_1__inductiveSyntaxToView___spec__1___closed__6);
l_Lean_Elab_Command_elabDeclaration___closed__1 = _init_l_Lean_Elab_Command_elabDeclaration___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabDeclaration___closed__1);
l_Lean_Elab_Command_elabDeclaration___closed__2 = _init_l_Lean_Elab_Command_elabDeclaration___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabDeclaration___closed__2);
l_Lean_Elab_Command_elabDeclaration___closed__3 = _init_l_Lean_Elab_Command_elabDeclaration___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabDeclaration___closed__3);
l___regBuiltin_Lean_Elab_Command_elabDeclaration___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabDeclaration___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabDeclaration___closed__1);
res = l___regBuiltin_Lean_Elab_Command_elabDeclaration(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Elab_Declaration_7__expandMutualPreamble_x3f___closed__1 = _init_l___private_Lean_Elab_Declaration_7__expandMutualPreamble_x3f___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Declaration_7__expandMutualPreamble_x3f___closed__1);
l___private_Lean_Elab_Declaration_7__expandMutualPreamble_x3f___closed__2 = _init_l___private_Lean_Elab_Declaration_7__expandMutualPreamble_x3f___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Declaration_7__expandMutualPreamble_x3f___closed__2);
l___private_Lean_Elab_Declaration_7__expandMutualPreamble_x3f___closed__3 = _init_l___private_Lean_Elab_Declaration_7__expandMutualPreamble_x3f___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Declaration_7__expandMutualPreamble_x3f___closed__3);
l___private_Lean_Elab_Declaration_7__expandMutualPreamble_x3f___closed__4 = _init_l___private_Lean_Elab_Declaration_7__expandMutualPreamble_x3f___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Declaration_7__expandMutualPreamble_x3f___closed__4);
l___private_Lean_Elab_Declaration_7__expandMutualPreamble_x3f___closed__5 = _init_l___private_Lean_Elab_Declaration_7__expandMutualPreamble_x3f___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Declaration_7__expandMutualPreamble_x3f___closed__5);
l___private_Lean_Elab_Declaration_7__expandMutualPreamble_x3f___closed__6 = _init_l___private_Lean_Elab_Declaration_7__expandMutualPreamble_x3f___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Declaration_7__expandMutualPreamble_x3f___closed__6);
l___private_Lean_Elab_Declaration_7__expandMutualPreamble_x3f___closed__7 = _init_l___private_Lean_Elab_Declaration_7__expandMutualPreamble_x3f___closed__7();
lean_mark_persistent(l___private_Lean_Elab_Declaration_7__expandMutualPreamble_x3f___closed__7);
l___private_Lean_Elab_Declaration_7__expandMutualPreamble_x3f___closed__8 = _init_l___private_Lean_Elab_Declaration_7__expandMutualPreamble_x3f___closed__8();
lean_mark_persistent(l___private_Lean_Elab_Declaration_7__expandMutualPreamble_x3f___closed__8);
l___private_Lean_Elab_Declaration_7__expandMutualPreamble_x3f___closed__9 = _init_l___private_Lean_Elab_Declaration_7__expandMutualPreamble_x3f___closed__9();
lean_mark_persistent(l___private_Lean_Elab_Declaration_7__expandMutualPreamble_x3f___closed__9);
l___private_Lean_Elab_Declaration_7__expandMutualPreamble_x3f___closed__10 = _init_l___private_Lean_Elab_Declaration_7__expandMutualPreamble_x3f___closed__10();
lean_mark_persistent(l___private_Lean_Elab_Declaration_7__expandMutualPreamble_x3f___closed__10);
l___private_Lean_Elab_Declaration_7__expandMutualPreamble_x3f___closed__11 = _init_l___private_Lean_Elab_Declaration_7__expandMutualPreamble_x3f___closed__11();
lean_mark_persistent(l___private_Lean_Elab_Declaration_7__expandMutualPreamble_x3f___closed__11);
l___private_Lean_Elab_Declaration_7__expandMutualPreamble_x3f___closed__12 = _init_l___private_Lean_Elab_Declaration_7__expandMutualPreamble_x3f___closed__12();
lean_mark_persistent(l___private_Lean_Elab_Declaration_7__expandMutualPreamble_x3f___closed__12);
l_Lean_Elab_Command_elabMutual___closed__1 = _init_l_Lean_Elab_Command_elabMutual___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabMutual___closed__1);
l_Lean_Elab_Command_elabMutual___closed__2 = _init_l_Lean_Elab_Command_elabMutual___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabMutual___closed__2);
l_Lean_Elab_Command_elabMutual___closed__3 = _init_l_Lean_Elab_Command_elabMutual___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabMutual___closed__3);
l___regBuiltin_Lean_Elab_Command_elabMutual___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabMutual___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabMutual___closed__1);
res = l___regBuiltin_Lean_Elab_Command_elabMutual(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
