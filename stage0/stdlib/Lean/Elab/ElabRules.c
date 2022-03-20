// Lean compiler output
// Module: Lean.Elab.ElabRules
// Imports: Init Lean.Elab.MacroArgUtil Lean.Elab.AuxDef
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
uint8_t l_Lean_Syntax_isQuot(lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__31;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__59;
static lean_object* l___regBuiltin_Lean_Elab_Command_expandElab_declRange___closed__3;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__82;
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__12;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabElabRules___closed__3;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__102;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabElabRules___closed__2;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__90;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__10;
lean_object* l_Lean_Elab_Command_expandMacroArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRules___lambda__7___closed__2;
lean_object* l_Lean_Elab_Command_expandNoKindMacroRulesAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRules___lambda__3___closed__1;
extern lean_object* l_Lean_nullKind;
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Command_elabCommand___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Macro_getCurrNamespace(lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__3;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__92;
static lean_object* l_Lean_Elab_Command_elabElabRules___lambda__7___closed__1;
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__112;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabElabRules___closed__4;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__61;
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__7;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__68;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_withExpectedType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__87;
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Command_elabAuxDef___spec__4(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__21;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__38;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__1(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__107;
static lean_object* l_Lean_Elab_Command_elabElabRules___lambda__3___closed__2;
uint8_t lean_name_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_expandElab___lambda__1___closed__7;
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*);
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at___aux__Init__Notation______macroRules__precMax__1___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__44;
static lean_object* l_Lean_Elab_Command_elabElabRules___lambda__6___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__94;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__8;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__1___boxed(lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__4;
static lean_object* l_Lean_Elab_Command_elabElabRules___lambda__7___closed__4;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__57;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__8;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__1;
static lean_object* l_Lean_Elab_Command_expandElab___lambda__1___closed__3;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_expandElab(lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__111;
lean_object* lean_string_utf8_byte_size(lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__48;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRules___lambda__3___closed__4;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__13;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__89;
lean_object* l_Lean_Elab_Command_mkNameFromParserSyntax(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__74;
uint8_t l_Lean_Elab_Command_checkRuleKind(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__60;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__47;
static lean_object* l_Lean_Elab_Command_expandElab___lambda__3___closed__1;
static lean_object* l_Lean_Elab_Command_expandElab___lambda__1___closed__5;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRulesAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_resolveSyntaxKind(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_SepArray_ofElems(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange___closed__3;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__27;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__67;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__40;
static lean_object* l_Lean_Elab_Command_expandElab___lambda__1___closed__1;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__45;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_expandElab___closed__4;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__4;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__65;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__109;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandElab___lambda__1___boxed(lean_object**);
lean_object* l_Array_mapMUnsafe_map___at___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___spec__3(size_t, size_t, lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__9;
lean_object* l_Lean_Elab_Term_tryPostponeIfNoneOrMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__51;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandElab___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange___closed__7;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__39;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__64;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__97;
static lean_object* l_Lean_Elab_Command_elabElabRules___closed__1;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_expandElab___closed__2;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__17;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabElabRules(lean_object*);
extern lean_object* l_Lean_numLitKind;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__1;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__83;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__6;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__76;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__18;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__30;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__5;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__14;
static lean_object* l_Lean_Elab_Command_expandElab___lambda__1___closed__6;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__28;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__15;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__29;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabElabRules___closed__1;
lean_object* l_Nat_repr(lean_object*);
static lean_object* l_Lean_Elab_Command_withExpectedType___closed__1;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__52;
lean_object* l_Lean_Syntax_getId(lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__55;
static lean_object* l_Lean_Elab_Command_expandElab___lambda__1___closed__2;
lean_object* l_Lean_throwError___at_Lean_Elab_Command_resolveSyntaxKind___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___at_Lean_Elab_Command_elabElabRulesAux___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_adaptExpander(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_choiceKind;
static lean_object* l___regBuiltin_Lean_Elab_Command_expandElab_declRange___closed__5;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__42;
lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabCommand___spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__100;
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__103;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__6;
static lean_object* l_Lean_Elab_Command_withExpectedType___closed__2;
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___at_Lean_Elab_Command_elabElabRulesAux___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__37;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__11;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__78;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__91;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__93;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__9;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__22;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRules___lambda__3___closed__7;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__25;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__86;
lean_object* l_Array_unzip___rarg(lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__46;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__7;
extern lean_object* l_Lean_instInhabitedSyntax;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandElab___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__34;
lean_object* l_Lean_evalOptPrio(lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange___closed__6;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__8;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__13;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__41;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__88;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__23;
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__96;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__72;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__4;
static lean_object* l_Lean_Elab_Command_elabElabRules___lambda__3___closed__3;
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__84;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__62;
static lean_object* l_Lean_Elab_Command_expandElab___closed__1;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__33;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__110;
uint8_t l_Lean_Syntax_isNodeOf(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRules___lambda__7___closed__3;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__54;
static lean_object* l_Lean_Elab_Command_elabElabRules___lambda__3___closed__5;
lean_object* l_Lean_Syntax_getQuotContent(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange___closed__1;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__99;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__50;
static lean_object* l___regBuiltin_Lean_Elab_Command_expandElab_declRange___closed__6;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__6;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__80;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__79;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__95;
extern lean_object* l_Lean_Elab_macroAttribute;
lean_object* l_Lean_Syntax_setArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__66;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__56;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__115;
lean_object* l_Lean_Elab_Command_getCurrMacroScope(lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_expandElab___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__105;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__85;
lean_object* l_Lean_Syntax_getKind(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange___closed__2;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__16;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabElabRulesAux___spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_inferMacroRulesAltKind___spec__2___rarg(lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__101;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__43;
lean_object* l_Lean_Elab_Command_getMainModule___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__20;
lean_object* l_Lean_Elab_Command_getRef(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_expandElab___lambda__1___closed__8;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__73;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRules___lambda__3___closed__6;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__32;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandElab___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__10;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__49;
uint8_t l_Lean_Syntax_isNone(lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__24;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__63;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__106;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__53;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_expandElab___lambda__1___closed__9;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandElab___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_expandElab_declRange___closed__2;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__3;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_expandElab___lambda__1___closed__4;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__98;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__81;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandElab(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__12;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_expandElab___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_expandElab_declRange___closed__1;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__77;
lean_object* lean_mk_syntax_ident(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___at_Lean_Elab_Command_expandElab___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandElab___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__108;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_expandElab_declRange(lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__5;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__7;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__71;
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabCommand___spec__14___rarg(lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__69;
static lean_object* l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange___closed__4;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__113;
static lean_object* l___regBuiltin_Lean_Elab_Command_expandElab_declRange___closed__7;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__11;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_expandElab___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Command_expandElab_declRange___closed__4;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___closed__2;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__58;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_expandElab___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__75;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__26;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__114;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandElab___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__104;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__36;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabElabRulesAux___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__3;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__19;
static lean_object* l___regBuiltin_Lean_Elab_Command_expandElab___closed__3;
lean_object* l_Lean_throwError___at_Lean_Elab_Term_synthesizeInst___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__70;
static lean_object* l_Lean_Elab_Command_expandElab___lambda__1___closed__10;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkLit(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__35;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__14;
static lean_object* _init_l_Lean_Elab_Command_withExpectedType___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("expected type must be known");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_withExpectedType___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_withExpectedType___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_withExpectedType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_1);
x_10 = l_Lean_Elab_Term_tryPostponeIfNoneOrMVar(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_2);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_Lean_Elab_Command_withExpectedType___closed__2;
x_13 = l_Lean_throwError___at_Lean_Elab_Term_synthesizeInst___spec__1(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_apply_8(x_2, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_14);
return x_16;
}
}
else
{
uint8_t x_17; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_10);
if (x_17 == 0)
{
return x_10;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_10, 0);
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_10);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabElabRulesAux___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_5, x_4);
if (x_7 == 0)
{
lean_inc(x_6);
return x_6;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_array_uget(x_3, x_5);
lean_inc(x_8);
x_9 = l_Lean_Syntax_getKind(x_8);
x_10 = l_Lean_Elab_Command_checkRuleKind(x_9, x_1);
lean_dec(x_9);
if (x_10 == 0)
{
size_t x_11; size_t x_12; 
lean_dec(x_8);
x_11 = 1;
x_12 = lean_usize_add(x_5, x_11);
{
size_t _tmp_4 = x_12;
lean_object* _tmp_5 = x_2;
x_5 = _tmp_4;
x_6 = _tmp_5;
}
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_8);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("|");
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("null");
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(",");
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("=>");
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid elab_rules alternative, unexpected syntax node kind '");
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__8;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("'");
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__10;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__12() {
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
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid elab_rules alternative, expected syntax node kind '");
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__13;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
lean_inc(x_1);
x_11 = l_Lean_Syntax_getQuotContent(x_1);
lean_inc(x_11);
x_12 = l_Lean_Syntax_getKind(x_11);
x_13 = l_Lean_Elab_Command_checkRuleKind(x_12, x_5);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = l_Lean_choiceKind;
x_15 = lean_name_eq(x_12, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_16 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_16, 0, x_12);
x_17 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__9;
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__11;
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_throwErrorAt___at_Lean_Elab_Command_elabCommand___spec__11(x_6, x_20, x_8, x_9, x_10);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_12);
x_22 = l_Lean_Syntax_getArgs(x_11);
lean_dec(x_11);
x_23 = lean_array_get_size(x_22);
x_24 = lean_usize_of_nat(x_23);
lean_dec(x_23);
x_25 = 0;
x_26 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__12;
x_27 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabElabRulesAux___spec__1(x_5, x_26, x_22, x_24, x_25, x_26);
lean_dec(x_22);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec(x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_29 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_29, 0, x_5);
x_30 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__14;
x_31 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
x_32 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__11;
x_33 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Lean_throwErrorAt___at_Lean_Elab_Command_elabCommand___spec__11(x_6, x_33, x_8, x_9, x_10);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
lean_dec(x_6);
lean_dec(x_5);
x_35 = lean_ctor_get(x_28, 0);
lean_inc(x_35);
lean_dec(x_28);
x_36 = lean_unsigned_to_nat(1u);
x_37 = l_Lean_Syntax_setArg(x_1, x_36, x_35);
x_38 = lean_unsigned_to_nat(0u);
x_39 = lean_array_set(x_2, x_38, x_37);
x_40 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Command_elabAuxDef___spec__4(x_8, x_9, x_10);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = l_Lean_Elab_Command_getCurrMacroScope(x_8, x_9, x_42);
lean_dec(x_8);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_45 = l_Lean_Elab_Command_getMainModule___rarg(x_9, x_44);
lean_dec(x_9);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_47 = lean_ctor_get(x_45, 0);
lean_dec(x_47);
x_48 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__1;
lean_inc(x_41);
x_49 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_49, 0, x_41);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__5;
x_51 = l_Lean_Syntax_SepArray_ofElems(x_50, x_39);
lean_dec(x_39);
x_52 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__4;
x_53 = l_Array_append___rarg(x_52, x_51);
x_54 = lean_box(2);
x_55 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__3;
x_56 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
lean_ctor_set(x_56, 2, x_53);
x_57 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__6;
x_58 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_58, 0, x_41);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__7;
x_60 = lean_array_push(x_59, x_49);
x_61 = lean_array_push(x_60, x_56);
x_62 = lean_array_push(x_61, x_58);
x_63 = lean_array_push(x_62, x_3);
x_64 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_64, 0, x_54);
lean_ctor_set(x_64, 1, x_4);
lean_ctor_set(x_64, 2, x_63);
lean_ctor_set(x_45, 0, x_64);
return x_45;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_65 = lean_ctor_get(x_45, 1);
lean_inc(x_65);
lean_dec(x_45);
x_66 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__1;
lean_inc(x_41);
x_67 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_67, 0, x_41);
lean_ctor_set(x_67, 1, x_66);
x_68 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__5;
x_69 = l_Lean_Syntax_SepArray_ofElems(x_68, x_39);
lean_dec(x_39);
x_70 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__4;
x_71 = l_Array_append___rarg(x_70, x_69);
x_72 = lean_box(2);
x_73 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__3;
x_74 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
lean_ctor_set(x_74, 2, x_71);
x_75 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__6;
x_76 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_76, 0, x_41);
lean_ctor_set(x_76, 1, x_75);
x_77 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__7;
x_78 = lean_array_push(x_77, x_67);
x_79 = lean_array_push(x_78, x_74);
x_80 = lean_array_push(x_79, x_76);
x_81 = lean_array_push(x_80, x_3);
x_82 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_82, 0, x_72);
lean_ctor_set(x_82, 1, x_4);
lean_ctor_set(x_82, 2, x_81);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_65);
return x_83;
}
}
}
}
else
{
lean_object* x_84; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_6);
lean_ctor_set(x_84, 1, x_10);
return x_84;
}
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean");
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Parser");
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__2;
x_2 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Term");
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__4;
x_2 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("matchAlt");
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__6;
x_2 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_3, x_2);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_array_uget(x_4, x_3);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_array_uset(x_4, x_3, x_11);
x_13 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__8;
lean_inc(x_10);
x_14 = l_Lean_Syntax_isOfKind(x_10, x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_15 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabCommand___spec__14___rarg(x_7);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
return x_15;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_15);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_20 = lean_unsigned_to_nat(1u);
x_21 = l_Lean_Syntax_getArg(x_10, x_20);
x_22 = lean_unsigned_to_nat(3u);
x_23 = l_Lean_Syntax_getArg(x_10, x_22);
x_24 = l_Lean_Syntax_getArgs(x_21);
lean_dec(x_21);
x_25 = l_Lean_instInhabitedSyntax;
x_26 = lean_array_get(x_25, x_24, x_11);
x_27 = l_Lean_Syntax_isQuot(x_26);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_28 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_inferMacroRulesAltKind___spec__2___rarg(x_7);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
return x_28;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_28);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_box(0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_34 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2(x_26, x_24, x_23, x_13, x_1, x_10, x_33, x_5, x_6, x_7);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; size_t x_37; size_t x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = 1;
x_38 = lean_usize_add(x_3, x_37);
x_39 = lean_array_uset(x_12, x_3, x_35);
x_3 = x_38;
x_4 = x_39;
x_7 = x_36;
goto _start;
}
else
{
uint8_t x_41; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_34);
if (x_41 == 0)
{
return x_34;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_34, 0);
x_43 = lean_ctor_get(x_34, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_34);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___at_Lean_Elab_Command_elabElabRulesAux___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Elab_Command_getRef(x_2, x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = l_Lean_mkIdentFrom(x_7, x_1);
lean_ctor_set(x_5, 0, x_8);
return x_5;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_5, 0);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_5);
x_11 = l_Lean_mkIdentFrom(x_9, x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("term");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("command");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("tactic");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unsupported syntax category '");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Elab");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__2;
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__9;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Command");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__10;
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__11;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("aux_def");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__12;
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__13;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("attributes");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__6;
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__15;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("@[");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("attrInstance");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__6;
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__18;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Attr");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__4;
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__20;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__22() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("simple");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__21;
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__22;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__5;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__24;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__28() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("]");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__30() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabRules");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__30;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__30;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__31;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__30;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__34() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(":");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__35() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Elab.Tactic.Tactic");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__36() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__35;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__37() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__35;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__36;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__38() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Tactic");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__39() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__10;
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__38;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__40() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__39;
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__38;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__41() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__40;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__42() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__41;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__43() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(":=");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__44() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("fun");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__45() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__6;
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__44;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__46() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("matchAlts");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__47() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__6;
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__46;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__48() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("hole");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__49() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__6;
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__48;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__50() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__51() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("throwUnsupportedSyntax");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__52() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__51;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__53() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__51;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__52;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__54() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__51;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__55() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__10;
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__51;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__56() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__55;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__57() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__56;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__58() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__59() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__4;
x_2 = l_Array_append___rarg(x_1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__60() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__3;
x_3 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__59;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__61() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__58;
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__60;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__62() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("commandElab");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__63() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__62;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__64() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__62;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__63;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__65() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__62;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__66() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Elab.Command.CommandElab");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__67() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__66;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__68() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__66;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__67;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__69() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("CommandElab");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__70() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__12;
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__69;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__71() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__70;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__72() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__71;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__73() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("termElab");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__74() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__73;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__75() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__73;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__74;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__76() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__73;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__77() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Elab.Term.TermElab");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__78() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__77;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__79() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__77;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__78;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__80() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__10;
x_2 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__81() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("TermElab");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__82() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__80;
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__81;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__83() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__82;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__84() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__83;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__85() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("basicFun");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__86() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__6;
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__85;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__87() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("stx");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__88() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__87;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__89() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__87;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__88;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__90() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__87;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__91() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("match");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__92() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__6;
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__91;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__93() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__3;
x_3 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__4;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__94() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("matchDiscr");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__95() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__6;
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__94;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__96() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__27;
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__93;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__97() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("with");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__98() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(6u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__99() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("syntax category '");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__100() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__99;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__101() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' does not support expected type specification");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__102() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__101;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__103() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("expectedType?");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__104() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__103;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__105() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__103;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__104;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__106() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__103;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__107() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("app");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__108() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__6;
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__107;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__109() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Elab.Command.withExpectedType");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__110() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__109;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__111() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__109;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__110;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__112() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("withExpectedType");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__113() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__12;
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__112;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__114() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__113;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__115() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__114;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__2;
x_11 = lean_name_eq(x_6, x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__4;
x_13 = lean_name_eq(x_6, x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__6;
x_15 = lean_name_eq(x_6, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_16 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_16, 0, x_6);
x_17 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__8;
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__11;
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_throwError___at_Lean_Elab_Command_elabCommand___spec__12(x_20, x_7, x_8, x_9);
lean_dec(x_8);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
lean_dec(x_6);
lean_inc(x_2);
x_22 = l_Lean_mkIdentFromRef___at_Lean_Elab_Command_elabElabRulesAux___spec__3(x_2, x_7, x_8, x_9);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Command_elabAuxDef___spec__4(x_7, x_8, x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_Elab_Command_getCurrMacroScope(x_7, x_8, x_27);
lean_dec(x_7);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Lean_Elab_Command_getMainModule___rarg(x_8, x_30);
lean_dec(x_8);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__17;
lean_inc(x_26);
x_35 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_35, 0, x_26);
lean_ctor_set(x_35, 1, x_34);
lean_inc(x_29);
lean_inc(x_33);
x_36 = l_Lean_addMacroScope(x_33, x_14, x_29);
x_37 = lean_box(0);
x_38 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__25;
lean_inc(x_26);
x_39 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_39, 0, x_26);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set(x_39, 2, x_36);
lean_ctor_set(x_39, 3, x_37);
x_40 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__26;
x_41 = lean_array_push(x_40, x_23);
x_42 = lean_box(2);
x_43 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__3;
x_44 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set(x_44, 2, x_41);
x_45 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__27;
x_46 = lean_array_push(x_45, x_39);
x_47 = lean_array_push(x_46, x_44);
x_48 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__23;
x_49 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_49, 0, x_42);
lean_ctor_set(x_49, 1, x_48);
lean_ctor_set(x_49, 2, x_47);
x_50 = lean_array_push(x_45, x_3);
x_51 = lean_array_push(x_50, x_49);
x_52 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__19;
x_53 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_53, 0, x_42);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set(x_53, 2, x_51);
x_54 = lean_array_push(x_40, x_53);
x_55 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_55, 0, x_42);
lean_ctor_set(x_55, 1, x_43);
lean_ctor_set(x_55, 2, x_54);
x_56 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__28;
lean_inc(x_26);
x_57 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_57, 0, x_26);
lean_ctor_set(x_57, 1, x_56);
x_58 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__29;
x_59 = lean_array_push(x_58, x_35);
x_60 = lean_array_push(x_59, x_55);
x_61 = lean_array_push(x_60, x_57);
x_62 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__16;
x_63 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_63, 0, x_42);
lean_ctor_set(x_63, 1, x_62);
lean_ctor_set(x_63, 2, x_61);
x_64 = lean_array_push(x_40, x_63);
x_65 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_65, 0, x_42);
lean_ctor_set(x_65, 1, x_43);
lean_ctor_set(x_65, 2, x_64);
x_66 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__13;
lean_inc(x_26);
x_67 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_67, 0, x_26);
lean_ctor_set(x_67, 1, x_66);
x_68 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__33;
lean_inc(x_29);
lean_inc(x_33);
x_69 = l_Lean_addMacroScope(x_33, x_68, x_29);
x_70 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__32;
lean_inc(x_26);
x_71 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_71, 0, x_26);
lean_ctor_set(x_71, 1, x_70);
lean_ctor_set(x_71, 2, x_69);
lean_ctor_set(x_71, 3, x_37);
x_72 = lean_mk_syntax_ident(x_2);
x_73 = lean_array_push(x_45, x_71);
x_74 = lean_array_push(x_73, x_72);
x_75 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_75, 0, x_42);
lean_ctor_set(x_75, 1, x_43);
lean_ctor_set(x_75, 2, x_74);
x_76 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__34;
lean_inc(x_26);
x_77 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_77, 0, x_26);
lean_ctor_set(x_77, 1, x_76);
x_78 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__40;
lean_inc(x_29);
lean_inc(x_33);
x_79 = l_Lean_addMacroScope(x_33, x_78, x_29);
x_80 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__37;
x_81 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__42;
lean_inc(x_26);
x_82 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_82, 0, x_26);
lean_ctor_set(x_82, 1, x_80);
lean_ctor_set(x_82, 2, x_79);
lean_ctor_set(x_82, 3, x_81);
x_83 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__43;
lean_inc(x_26);
x_84 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_84, 0, x_26);
lean_ctor_set(x_84, 1, x_83);
x_85 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__44;
lean_inc(x_26);
x_86 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_86, 0, x_26);
lean_ctor_set(x_86, 1, x_85);
x_87 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__4;
x_88 = l_Array_append___rarg(x_87, x_4);
x_89 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__1;
lean_inc(x_26);
x_90 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_90, 0, x_26);
lean_ctor_set(x_90, 1, x_89);
x_91 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__50;
lean_inc(x_26);
x_92 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_92, 0, x_26);
lean_ctor_set(x_92, 1, x_91);
x_93 = lean_array_push(x_40, x_92);
x_94 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__49;
x_95 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_95, 0, x_42);
lean_ctor_set(x_95, 1, x_94);
lean_ctor_set(x_95, 2, x_93);
x_96 = lean_array_push(x_40, x_95);
x_97 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_97, 0, x_42);
lean_ctor_set(x_97, 1, x_43);
lean_ctor_set(x_97, 2, x_96);
x_98 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__6;
lean_inc(x_26);
x_99 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_99, 0, x_26);
lean_ctor_set(x_99, 1, x_98);
x_100 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__54;
x_101 = l_Lean_addMacroScope(x_33, x_100, x_29);
x_102 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__53;
x_103 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__57;
x_104 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_104, 0, x_26);
lean_ctor_set(x_104, 1, x_102);
lean_ctor_set(x_104, 2, x_101);
lean_ctor_set(x_104, 3, x_103);
x_105 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__7;
x_106 = lean_array_push(x_105, x_90);
x_107 = lean_array_push(x_106, x_97);
x_108 = lean_array_push(x_107, x_99);
x_109 = lean_array_push(x_108, x_104);
x_110 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__8;
x_111 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_111, 0, x_42);
lean_ctor_set(x_111, 1, x_110);
lean_ctor_set(x_111, 2, x_109);
x_112 = lean_array_push(x_88, x_111);
x_113 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_113, 0, x_42);
lean_ctor_set(x_113, 1, x_43);
lean_ctor_set(x_113, 2, x_112);
x_114 = lean_array_push(x_40, x_113);
x_115 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__47;
x_116 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_116, 0, x_42);
lean_ctor_set(x_116, 1, x_115);
lean_ctor_set(x_116, 2, x_114);
x_117 = lean_array_push(x_45, x_86);
x_118 = lean_array_push(x_117, x_116);
x_119 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__45;
x_120 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_120, 0, x_42);
lean_ctor_set(x_120, 1, x_119);
lean_ctor_set(x_120, 2, x_118);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_121 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__61;
x_122 = lean_array_push(x_121, x_65);
x_123 = lean_array_push(x_122, x_67);
x_124 = lean_array_push(x_123, x_75);
x_125 = lean_array_push(x_124, x_77);
x_126 = lean_array_push(x_125, x_82);
x_127 = lean_array_push(x_126, x_84);
x_128 = lean_array_push(x_127, x_120);
x_129 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__14;
x_130 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_130, 0, x_42);
lean_ctor_set(x_130, 1, x_129);
lean_ctor_set(x_130, 2, x_128);
lean_ctor_set(x_31, 0, x_130);
return x_31;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_131 = lean_ctor_get(x_5, 0);
lean_inc(x_131);
lean_dec(x_5);
x_132 = lean_array_push(x_40, x_131);
x_133 = l_Array_append___rarg(x_87, x_132);
x_134 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_134, 0, x_42);
lean_ctor_set(x_134, 1, x_43);
lean_ctor_set(x_134, 2, x_133);
x_135 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__58;
x_136 = lean_array_push(x_135, x_134);
x_137 = lean_array_push(x_136, x_65);
x_138 = lean_array_push(x_137, x_67);
x_139 = lean_array_push(x_138, x_75);
x_140 = lean_array_push(x_139, x_77);
x_141 = lean_array_push(x_140, x_82);
x_142 = lean_array_push(x_141, x_84);
x_143 = lean_array_push(x_142, x_120);
x_144 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__14;
x_145 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_145, 0, x_42);
lean_ctor_set(x_145, 1, x_144);
lean_ctor_set(x_145, 2, x_143);
lean_ctor_set(x_31, 0, x_145);
return x_31;
}
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_146 = lean_ctor_get(x_31, 0);
x_147 = lean_ctor_get(x_31, 1);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_31);
x_148 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__17;
lean_inc(x_26);
x_149 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_149, 0, x_26);
lean_ctor_set(x_149, 1, x_148);
lean_inc(x_29);
lean_inc(x_146);
x_150 = l_Lean_addMacroScope(x_146, x_14, x_29);
x_151 = lean_box(0);
x_152 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__25;
lean_inc(x_26);
x_153 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_153, 0, x_26);
lean_ctor_set(x_153, 1, x_152);
lean_ctor_set(x_153, 2, x_150);
lean_ctor_set(x_153, 3, x_151);
x_154 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__26;
x_155 = lean_array_push(x_154, x_23);
x_156 = lean_box(2);
x_157 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__3;
x_158 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_158, 0, x_156);
lean_ctor_set(x_158, 1, x_157);
lean_ctor_set(x_158, 2, x_155);
x_159 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__27;
x_160 = lean_array_push(x_159, x_153);
x_161 = lean_array_push(x_160, x_158);
x_162 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__23;
x_163 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_163, 0, x_156);
lean_ctor_set(x_163, 1, x_162);
lean_ctor_set(x_163, 2, x_161);
x_164 = lean_array_push(x_159, x_3);
x_165 = lean_array_push(x_164, x_163);
x_166 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__19;
x_167 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_167, 0, x_156);
lean_ctor_set(x_167, 1, x_166);
lean_ctor_set(x_167, 2, x_165);
x_168 = lean_array_push(x_154, x_167);
x_169 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_169, 0, x_156);
lean_ctor_set(x_169, 1, x_157);
lean_ctor_set(x_169, 2, x_168);
x_170 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__28;
lean_inc(x_26);
x_171 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_171, 0, x_26);
lean_ctor_set(x_171, 1, x_170);
x_172 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__29;
x_173 = lean_array_push(x_172, x_149);
x_174 = lean_array_push(x_173, x_169);
x_175 = lean_array_push(x_174, x_171);
x_176 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__16;
x_177 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_177, 0, x_156);
lean_ctor_set(x_177, 1, x_176);
lean_ctor_set(x_177, 2, x_175);
x_178 = lean_array_push(x_154, x_177);
x_179 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_179, 0, x_156);
lean_ctor_set(x_179, 1, x_157);
lean_ctor_set(x_179, 2, x_178);
x_180 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__13;
lean_inc(x_26);
x_181 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_181, 0, x_26);
lean_ctor_set(x_181, 1, x_180);
x_182 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__33;
lean_inc(x_29);
lean_inc(x_146);
x_183 = l_Lean_addMacroScope(x_146, x_182, x_29);
x_184 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__32;
lean_inc(x_26);
x_185 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_185, 0, x_26);
lean_ctor_set(x_185, 1, x_184);
lean_ctor_set(x_185, 2, x_183);
lean_ctor_set(x_185, 3, x_151);
x_186 = lean_mk_syntax_ident(x_2);
x_187 = lean_array_push(x_159, x_185);
x_188 = lean_array_push(x_187, x_186);
x_189 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_189, 0, x_156);
lean_ctor_set(x_189, 1, x_157);
lean_ctor_set(x_189, 2, x_188);
x_190 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__34;
lean_inc(x_26);
x_191 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_191, 0, x_26);
lean_ctor_set(x_191, 1, x_190);
x_192 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__40;
lean_inc(x_29);
lean_inc(x_146);
x_193 = l_Lean_addMacroScope(x_146, x_192, x_29);
x_194 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__37;
x_195 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__42;
lean_inc(x_26);
x_196 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_196, 0, x_26);
lean_ctor_set(x_196, 1, x_194);
lean_ctor_set(x_196, 2, x_193);
lean_ctor_set(x_196, 3, x_195);
x_197 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__43;
lean_inc(x_26);
x_198 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_198, 0, x_26);
lean_ctor_set(x_198, 1, x_197);
x_199 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__44;
lean_inc(x_26);
x_200 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_200, 0, x_26);
lean_ctor_set(x_200, 1, x_199);
x_201 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__4;
x_202 = l_Array_append___rarg(x_201, x_4);
x_203 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__1;
lean_inc(x_26);
x_204 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_204, 0, x_26);
lean_ctor_set(x_204, 1, x_203);
x_205 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__50;
lean_inc(x_26);
x_206 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_206, 0, x_26);
lean_ctor_set(x_206, 1, x_205);
x_207 = lean_array_push(x_154, x_206);
x_208 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__49;
x_209 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_209, 0, x_156);
lean_ctor_set(x_209, 1, x_208);
lean_ctor_set(x_209, 2, x_207);
x_210 = lean_array_push(x_154, x_209);
x_211 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_211, 0, x_156);
lean_ctor_set(x_211, 1, x_157);
lean_ctor_set(x_211, 2, x_210);
x_212 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__6;
lean_inc(x_26);
x_213 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_213, 0, x_26);
lean_ctor_set(x_213, 1, x_212);
x_214 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__54;
x_215 = l_Lean_addMacroScope(x_146, x_214, x_29);
x_216 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__53;
x_217 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__57;
x_218 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_218, 0, x_26);
lean_ctor_set(x_218, 1, x_216);
lean_ctor_set(x_218, 2, x_215);
lean_ctor_set(x_218, 3, x_217);
x_219 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__7;
x_220 = lean_array_push(x_219, x_204);
x_221 = lean_array_push(x_220, x_211);
x_222 = lean_array_push(x_221, x_213);
x_223 = lean_array_push(x_222, x_218);
x_224 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__8;
x_225 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_225, 0, x_156);
lean_ctor_set(x_225, 1, x_224);
lean_ctor_set(x_225, 2, x_223);
x_226 = lean_array_push(x_202, x_225);
x_227 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_227, 0, x_156);
lean_ctor_set(x_227, 1, x_157);
lean_ctor_set(x_227, 2, x_226);
x_228 = lean_array_push(x_154, x_227);
x_229 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__47;
x_230 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_230, 0, x_156);
lean_ctor_set(x_230, 1, x_229);
lean_ctor_set(x_230, 2, x_228);
x_231 = lean_array_push(x_159, x_200);
x_232 = lean_array_push(x_231, x_230);
x_233 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__45;
x_234 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_234, 0, x_156);
lean_ctor_set(x_234, 1, x_233);
lean_ctor_set(x_234, 2, x_232);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_235 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__61;
x_236 = lean_array_push(x_235, x_179);
x_237 = lean_array_push(x_236, x_181);
x_238 = lean_array_push(x_237, x_189);
x_239 = lean_array_push(x_238, x_191);
x_240 = lean_array_push(x_239, x_196);
x_241 = lean_array_push(x_240, x_198);
x_242 = lean_array_push(x_241, x_234);
x_243 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__14;
x_244 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_244, 0, x_156);
lean_ctor_set(x_244, 1, x_243);
lean_ctor_set(x_244, 2, x_242);
x_245 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_245, 0, x_244);
lean_ctor_set(x_245, 1, x_147);
return x_245;
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_246 = lean_ctor_get(x_5, 0);
lean_inc(x_246);
lean_dec(x_5);
x_247 = lean_array_push(x_154, x_246);
x_248 = l_Array_append___rarg(x_201, x_247);
x_249 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_249, 0, x_156);
lean_ctor_set(x_249, 1, x_157);
lean_ctor_set(x_249, 2, x_248);
x_250 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__58;
x_251 = lean_array_push(x_250, x_249);
x_252 = lean_array_push(x_251, x_179);
x_253 = lean_array_push(x_252, x_181);
x_254 = lean_array_push(x_253, x_189);
x_255 = lean_array_push(x_254, x_191);
x_256 = lean_array_push(x_255, x_196);
x_257 = lean_array_push(x_256, x_198);
x_258 = lean_array_push(x_257, x_234);
x_259 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__14;
x_260 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_260, 0, x_156);
lean_ctor_set(x_260, 1, x_259);
lean_ctor_set(x_260, 2, x_258);
x_261 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_261, 0, x_260);
lean_ctor_set(x_261, 1, x_147);
return x_261;
}
}
}
}
else
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; uint8_t x_272; 
lean_dec(x_6);
lean_inc(x_2);
x_262 = l_Lean_mkIdentFromRef___at_Lean_Elab_Command_elabElabRulesAux___spec__3(x_2, x_7, x_8, x_9);
x_263 = lean_ctor_get(x_262, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_262, 1);
lean_inc(x_264);
lean_dec(x_262);
x_265 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Command_elabAuxDef___spec__4(x_7, x_8, x_264);
x_266 = lean_ctor_get(x_265, 0);
lean_inc(x_266);
x_267 = lean_ctor_get(x_265, 1);
lean_inc(x_267);
lean_dec(x_265);
x_268 = l_Lean_Elab_Command_getCurrMacroScope(x_7, x_8, x_267);
lean_dec(x_7);
x_269 = lean_ctor_get(x_268, 0);
lean_inc(x_269);
x_270 = lean_ctor_get(x_268, 1);
lean_inc(x_270);
lean_dec(x_268);
x_271 = l_Lean_Elab_Command_getMainModule___rarg(x_8, x_270);
lean_dec(x_8);
x_272 = !lean_is_exclusive(x_271);
if (x_272 == 0)
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; 
x_273 = lean_ctor_get(x_271, 0);
x_274 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__17;
lean_inc(x_266);
x_275 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_275, 0, x_266);
lean_ctor_set(x_275, 1, x_274);
x_276 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__65;
lean_inc(x_269);
lean_inc(x_273);
x_277 = l_Lean_addMacroScope(x_273, x_276, x_269);
x_278 = lean_box(0);
x_279 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__64;
lean_inc(x_266);
x_280 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_280, 0, x_266);
lean_ctor_set(x_280, 1, x_279);
lean_ctor_set(x_280, 2, x_277);
lean_ctor_set(x_280, 3, x_278);
x_281 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__26;
x_282 = lean_array_push(x_281, x_263);
x_283 = lean_box(2);
x_284 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__3;
x_285 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_285, 0, x_283);
lean_ctor_set(x_285, 1, x_284);
lean_ctor_set(x_285, 2, x_282);
x_286 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__27;
x_287 = lean_array_push(x_286, x_280);
x_288 = lean_array_push(x_287, x_285);
x_289 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__23;
x_290 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_290, 0, x_283);
lean_ctor_set(x_290, 1, x_289);
lean_ctor_set(x_290, 2, x_288);
x_291 = lean_array_push(x_286, x_3);
x_292 = lean_array_push(x_291, x_290);
x_293 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__19;
x_294 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_294, 0, x_283);
lean_ctor_set(x_294, 1, x_293);
lean_ctor_set(x_294, 2, x_292);
x_295 = lean_array_push(x_281, x_294);
x_296 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_296, 0, x_283);
lean_ctor_set(x_296, 1, x_284);
lean_ctor_set(x_296, 2, x_295);
x_297 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__28;
lean_inc(x_266);
x_298 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_298, 0, x_266);
lean_ctor_set(x_298, 1, x_297);
x_299 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__29;
x_300 = lean_array_push(x_299, x_275);
x_301 = lean_array_push(x_300, x_296);
x_302 = lean_array_push(x_301, x_298);
x_303 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__16;
x_304 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_304, 0, x_283);
lean_ctor_set(x_304, 1, x_303);
lean_ctor_set(x_304, 2, x_302);
x_305 = lean_array_push(x_281, x_304);
x_306 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_306, 0, x_283);
lean_ctor_set(x_306, 1, x_284);
lean_ctor_set(x_306, 2, x_305);
x_307 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__13;
lean_inc(x_266);
x_308 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_308, 0, x_266);
lean_ctor_set(x_308, 1, x_307);
x_309 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__33;
lean_inc(x_269);
lean_inc(x_273);
x_310 = l_Lean_addMacroScope(x_273, x_309, x_269);
x_311 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__32;
lean_inc(x_266);
x_312 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_312, 0, x_266);
lean_ctor_set(x_312, 1, x_311);
lean_ctor_set(x_312, 2, x_310);
lean_ctor_set(x_312, 3, x_278);
x_313 = lean_mk_syntax_ident(x_2);
x_314 = lean_array_push(x_286, x_312);
x_315 = lean_array_push(x_314, x_313);
x_316 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_316, 0, x_283);
lean_ctor_set(x_316, 1, x_284);
lean_ctor_set(x_316, 2, x_315);
x_317 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__34;
lean_inc(x_266);
x_318 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_318, 0, x_266);
lean_ctor_set(x_318, 1, x_317);
x_319 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__70;
lean_inc(x_269);
lean_inc(x_273);
x_320 = l_Lean_addMacroScope(x_273, x_319, x_269);
x_321 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__68;
x_322 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__72;
lean_inc(x_266);
x_323 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_323, 0, x_266);
lean_ctor_set(x_323, 1, x_321);
lean_ctor_set(x_323, 2, x_320);
lean_ctor_set(x_323, 3, x_322);
x_324 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__43;
lean_inc(x_266);
x_325 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_325, 0, x_266);
lean_ctor_set(x_325, 1, x_324);
x_326 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__44;
lean_inc(x_266);
x_327 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_327, 0, x_266);
lean_ctor_set(x_327, 1, x_326);
x_328 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__4;
x_329 = l_Array_append___rarg(x_328, x_4);
x_330 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__1;
lean_inc(x_266);
x_331 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_331, 0, x_266);
lean_ctor_set(x_331, 1, x_330);
x_332 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__50;
lean_inc(x_266);
x_333 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_333, 0, x_266);
lean_ctor_set(x_333, 1, x_332);
x_334 = lean_array_push(x_281, x_333);
x_335 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__49;
x_336 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_336, 0, x_283);
lean_ctor_set(x_336, 1, x_335);
lean_ctor_set(x_336, 2, x_334);
x_337 = lean_array_push(x_281, x_336);
x_338 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_338, 0, x_283);
lean_ctor_set(x_338, 1, x_284);
lean_ctor_set(x_338, 2, x_337);
x_339 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__6;
lean_inc(x_266);
x_340 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_340, 0, x_266);
lean_ctor_set(x_340, 1, x_339);
x_341 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__54;
x_342 = l_Lean_addMacroScope(x_273, x_341, x_269);
x_343 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__53;
x_344 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__57;
x_345 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_345, 0, x_266);
lean_ctor_set(x_345, 1, x_343);
lean_ctor_set(x_345, 2, x_342);
lean_ctor_set(x_345, 3, x_344);
x_346 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__7;
x_347 = lean_array_push(x_346, x_331);
x_348 = lean_array_push(x_347, x_338);
x_349 = lean_array_push(x_348, x_340);
x_350 = lean_array_push(x_349, x_345);
x_351 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__8;
x_352 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_352, 0, x_283);
lean_ctor_set(x_352, 1, x_351);
lean_ctor_set(x_352, 2, x_350);
x_353 = lean_array_push(x_329, x_352);
x_354 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_354, 0, x_283);
lean_ctor_set(x_354, 1, x_284);
lean_ctor_set(x_354, 2, x_353);
x_355 = lean_array_push(x_281, x_354);
x_356 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__47;
x_357 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_357, 0, x_283);
lean_ctor_set(x_357, 1, x_356);
lean_ctor_set(x_357, 2, x_355);
x_358 = lean_array_push(x_286, x_327);
x_359 = lean_array_push(x_358, x_357);
x_360 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__45;
x_361 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_361, 0, x_283);
lean_ctor_set(x_361, 1, x_360);
lean_ctor_set(x_361, 2, x_359);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; 
x_362 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__61;
x_363 = lean_array_push(x_362, x_306);
x_364 = lean_array_push(x_363, x_308);
x_365 = lean_array_push(x_364, x_316);
x_366 = lean_array_push(x_365, x_318);
x_367 = lean_array_push(x_366, x_323);
x_368 = lean_array_push(x_367, x_325);
x_369 = lean_array_push(x_368, x_361);
x_370 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__14;
x_371 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_371, 0, x_283);
lean_ctor_set(x_371, 1, x_370);
lean_ctor_set(x_371, 2, x_369);
lean_ctor_set(x_271, 0, x_371);
return x_271;
}
else
{
lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; 
x_372 = lean_ctor_get(x_5, 0);
lean_inc(x_372);
lean_dec(x_5);
x_373 = lean_array_push(x_281, x_372);
x_374 = l_Array_append___rarg(x_328, x_373);
x_375 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_375, 0, x_283);
lean_ctor_set(x_375, 1, x_284);
lean_ctor_set(x_375, 2, x_374);
x_376 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__58;
x_377 = lean_array_push(x_376, x_375);
x_378 = lean_array_push(x_377, x_306);
x_379 = lean_array_push(x_378, x_308);
x_380 = lean_array_push(x_379, x_316);
x_381 = lean_array_push(x_380, x_318);
x_382 = lean_array_push(x_381, x_323);
x_383 = lean_array_push(x_382, x_325);
x_384 = lean_array_push(x_383, x_361);
x_385 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__14;
x_386 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_386, 0, x_283);
lean_ctor_set(x_386, 1, x_385);
lean_ctor_set(x_386, 2, x_384);
lean_ctor_set(x_271, 0, x_386);
return x_271;
}
}
else
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; 
x_387 = lean_ctor_get(x_271, 0);
x_388 = lean_ctor_get(x_271, 1);
lean_inc(x_388);
lean_inc(x_387);
lean_dec(x_271);
x_389 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__17;
lean_inc(x_266);
x_390 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_390, 0, x_266);
lean_ctor_set(x_390, 1, x_389);
x_391 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__65;
lean_inc(x_269);
lean_inc(x_387);
x_392 = l_Lean_addMacroScope(x_387, x_391, x_269);
x_393 = lean_box(0);
x_394 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__64;
lean_inc(x_266);
x_395 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_395, 0, x_266);
lean_ctor_set(x_395, 1, x_394);
lean_ctor_set(x_395, 2, x_392);
lean_ctor_set(x_395, 3, x_393);
x_396 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__26;
x_397 = lean_array_push(x_396, x_263);
x_398 = lean_box(2);
x_399 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__3;
x_400 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_400, 0, x_398);
lean_ctor_set(x_400, 1, x_399);
lean_ctor_set(x_400, 2, x_397);
x_401 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__27;
x_402 = lean_array_push(x_401, x_395);
x_403 = lean_array_push(x_402, x_400);
x_404 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__23;
x_405 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_405, 0, x_398);
lean_ctor_set(x_405, 1, x_404);
lean_ctor_set(x_405, 2, x_403);
x_406 = lean_array_push(x_401, x_3);
x_407 = lean_array_push(x_406, x_405);
x_408 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__19;
x_409 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_409, 0, x_398);
lean_ctor_set(x_409, 1, x_408);
lean_ctor_set(x_409, 2, x_407);
x_410 = lean_array_push(x_396, x_409);
x_411 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_411, 0, x_398);
lean_ctor_set(x_411, 1, x_399);
lean_ctor_set(x_411, 2, x_410);
x_412 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__28;
lean_inc(x_266);
x_413 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_413, 0, x_266);
lean_ctor_set(x_413, 1, x_412);
x_414 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__29;
x_415 = lean_array_push(x_414, x_390);
x_416 = lean_array_push(x_415, x_411);
x_417 = lean_array_push(x_416, x_413);
x_418 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__16;
x_419 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_419, 0, x_398);
lean_ctor_set(x_419, 1, x_418);
lean_ctor_set(x_419, 2, x_417);
x_420 = lean_array_push(x_396, x_419);
x_421 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_421, 0, x_398);
lean_ctor_set(x_421, 1, x_399);
lean_ctor_set(x_421, 2, x_420);
x_422 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__13;
lean_inc(x_266);
x_423 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_423, 0, x_266);
lean_ctor_set(x_423, 1, x_422);
x_424 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__33;
lean_inc(x_269);
lean_inc(x_387);
x_425 = l_Lean_addMacroScope(x_387, x_424, x_269);
x_426 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__32;
lean_inc(x_266);
x_427 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_427, 0, x_266);
lean_ctor_set(x_427, 1, x_426);
lean_ctor_set(x_427, 2, x_425);
lean_ctor_set(x_427, 3, x_393);
x_428 = lean_mk_syntax_ident(x_2);
x_429 = lean_array_push(x_401, x_427);
x_430 = lean_array_push(x_429, x_428);
x_431 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_431, 0, x_398);
lean_ctor_set(x_431, 1, x_399);
lean_ctor_set(x_431, 2, x_430);
x_432 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__34;
lean_inc(x_266);
x_433 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_433, 0, x_266);
lean_ctor_set(x_433, 1, x_432);
x_434 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__70;
lean_inc(x_269);
lean_inc(x_387);
x_435 = l_Lean_addMacroScope(x_387, x_434, x_269);
x_436 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__68;
x_437 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__72;
lean_inc(x_266);
x_438 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_438, 0, x_266);
lean_ctor_set(x_438, 1, x_436);
lean_ctor_set(x_438, 2, x_435);
lean_ctor_set(x_438, 3, x_437);
x_439 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__43;
lean_inc(x_266);
x_440 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_440, 0, x_266);
lean_ctor_set(x_440, 1, x_439);
x_441 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__44;
lean_inc(x_266);
x_442 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_442, 0, x_266);
lean_ctor_set(x_442, 1, x_441);
x_443 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__4;
x_444 = l_Array_append___rarg(x_443, x_4);
x_445 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__1;
lean_inc(x_266);
x_446 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_446, 0, x_266);
lean_ctor_set(x_446, 1, x_445);
x_447 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__50;
lean_inc(x_266);
x_448 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_448, 0, x_266);
lean_ctor_set(x_448, 1, x_447);
x_449 = lean_array_push(x_396, x_448);
x_450 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__49;
x_451 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_451, 0, x_398);
lean_ctor_set(x_451, 1, x_450);
lean_ctor_set(x_451, 2, x_449);
x_452 = lean_array_push(x_396, x_451);
x_453 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_453, 0, x_398);
lean_ctor_set(x_453, 1, x_399);
lean_ctor_set(x_453, 2, x_452);
x_454 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__6;
lean_inc(x_266);
x_455 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_455, 0, x_266);
lean_ctor_set(x_455, 1, x_454);
x_456 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__54;
x_457 = l_Lean_addMacroScope(x_387, x_456, x_269);
x_458 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__53;
x_459 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__57;
x_460 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_460, 0, x_266);
lean_ctor_set(x_460, 1, x_458);
lean_ctor_set(x_460, 2, x_457);
lean_ctor_set(x_460, 3, x_459);
x_461 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__7;
x_462 = lean_array_push(x_461, x_446);
x_463 = lean_array_push(x_462, x_453);
x_464 = lean_array_push(x_463, x_455);
x_465 = lean_array_push(x_464, x_460);
x_466 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__8;
x_467 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_467, 0, x_398);
lean_ctor_set(x_467, 1, x_466);
lean_ctor_set(x_467, 2, x_465);
x_468 = lean_array_push(x_444, x_467);
x_469 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_469, 0, x_398);
lean_ctor_set(x_469, 1, x_399);
lean_ctor_set(x_469, 2, x_468);
x_470 = lean_array_push(x_396, x_469);
x_471 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__47;
x_472 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_472, 0, x_398);
lean_ctor_set(x_472, 1, x_471);
lean_ctor_set(x_472, 2, x_470);
x_473 = lean_array_push(x_401, x_442);
x_474 = lean_array_push(x_473, x_472);
x_475 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__45;
x_476 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_476, 0, x_398);
lean_ctor_set(x_476, 1, x_475);
lean_ctor_set(x_476, 2, x_474);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; 
x_477 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__61;
x_478 = lean_array_push(x_477, x_421);
x_479 = lean_array_push(x_478, x_423);
x_480 = lean_array_push(x_479, x_431);
x_481 = lean_array_push(x_480, x_433);
x_482 = lean_array_push(x_481, x_438);
x_483 = lean_array_push(x_482, x_440);
x_484 = lean_array_push(x_483, x_476);
x_485 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__14;
x_486 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_486, 0, x_398);
lean_ctor_set(x_486, 1, x_485);
lean_ctor_set(x_486, 2, x_484);
x_487 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_487, 0, x_486);
lean_ctor_set(x_487, 1, x_388);
return x_487;
}
else
{
lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; 
x_488 = lean_ctor_get(x_5, 0);
lean_inc(x_488);
lean_dec(x_5);
x_489 = lean_array_push(x_396, x_488);
x_490 = l_Array_append___rarg(x_443, x_489);
x_491 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_491, 0, x_398);
lean_ctor_set(x_491, 1, x_399);
lean_ctor_set(x_491, 2, x_490);
x_492 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__58;
x_493 = lean_array_push(x_492, x_491);
x_494 = lean_array_push(x_493, x_421);
x_495 = lean_array_push(x_494, x_423);
x_496 = lean_array_push(x_495, x_431);
x_497 = lean_array_push(x_496, x_433);
x_498 = lean_array_push(x_497, x_438);
x_499 = lean_array_push(x_498, x_440);
x_500 = lean_array_push(x_499, x_476);
x_501 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__14;
x_502 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_502, 0, x_398);
lean_ctor_set(x_502, 1, x_501);
lean_ctor_set(x_502, 2, x_500);
x_503 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_503, 0, x_502);
lean_ctor_set(x_503, 1, x_388);
return x_503;
}
}
}
}
else
{
lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; uint8_t x_514; 
lean_dec(x_6);
lean_inc(x_2);
x_504 = l_Lean_mkIdentFromRef___at_Lean_Elab_Command_elabElabRulesAux___spec__3(x_2, x_7, x_8, x_9);
x_505 = lean_ctor_get(x_504, 0);
lean_inc(x_505);
x_506 = lean_ctor_get(x_504, 1);
lean_inc(x_506);
lean_dec(x_504);
x_507 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Command_elabAuxDef___spec__4(x_7, x_8, x_506);
x_508 = lean_ctor_get(x_507, 0);
lean_inc(x_508);
x_509 = lean_ctor_get(x_507, 1);
lean_inc(x_509);
lean_dec(x_507);
x_510 = l_Lean_Elab_Command_getCurrMacroScope(x_7, x_8, x_509);
lean_dec(x_7);
x_511 = lean_ctor_get(x_510, 0);
lean_inc(x_511);
x_512 = lean_ctor_get(x_510, 1);
lean_inc(x_512);
lean_dec(x_510);
x_513 = l_Lean_Elab_Command_getMainModule___rarg(x_8, x_512);
lean_dec(x_8);
x_514 = !lean_is_exclusive(x_513);
if (x_514 == 0)
{
lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; 
x_515 = lean_ctor_get(x_513, 0);
x_516 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__17;
lean_inc(x_508);
x_517 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_517, 0, x_508);
lean_ctor_set(x_517, 1, x_516);
x_518 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__76;
lean_inc(x_511);
lean_inc(x_515);
x_519 = l_Lean_addMacroScope(x_515, x_518, x_511);
x_520 = lean_box(0);
x_521 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__75;
lean_inc(x_508);
x_522 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_522, 0, x_508);
lean_ctor_set(x_522, 1, x_521);
lean_ctor_set(x_522, 2, x_519);
lean_ctor_set(x_522, 3, x_520);
x_523 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__26;
x_524 = lean_array_push(x_523, x_505);
x_525 = lean_box(2);
x_526 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__3;
x_527 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_527, 0, x_525);
lean_ctor_set(x_527, 1, x_526);
lean_ctor_set(x_527, 2, x_524);
x_528 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__27;
x_529 = lean_array_push(x_528, x_522);
x_530 = lean_array_push(x_529, x_527);
x_531 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__23;
x_532 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_532, 0, x_525);
lean_ctor_set(x_532, 1, x_531);
lean_ctor_set(x_532, 2, x_530);
x_533 = lean_array_push(x_528, x_3);
x_534 = lean_array_push(x_533, x_532);
x_535 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__19;
x_536 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_536, 0, x_525);
lean_ctor_set(x_536, 1, x_535);
lean_ctor_set(x_536, 2, x_534);
x_537 = lean_array_push(x_523, x_536);
x_538 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_538, 0, x_525);
lean_ctor_set(x_538, 1, x_526);
lean_ctor_set(x_538, 2, x_537);
x_539 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__28;
lean_inc(x_508);
x_540 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_540, 0, x_508);
lean_ctor_set(x_540, 1, x_539);
x_541 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__29;
x_542 = lean_array_push(x_541, x_517);
x_543 = lean_array_push(x_542, x_538);
x_544 = lean_array_push(x_543, x_540);
x_545 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__16;
x_546 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_546, 0, x_525);
lean_ctor_set(x_546, 1, x_545);
lean_ctor_set(x_546, 2, x_544);
x_547 = lean_array_push(x_523, x_546);
x_548 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_548, 0, x_525);
lean_ctor_set(x_548, 1, x_526);
lean_ctor_set(x_548, 2, x_547);
x_549 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__13;
lean_inc(x_508);
x_550 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_550, 0, x_508);
lean_ctor_set(x_550, 1, x_549);
x_551 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__33;
lean_inc(x_511);
lean_inc(x_515);
x_552 = l_Lean_addMacroScope(x_515, x_551, x_511);
x_553 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__32;
lean_inc(x_508);
x_554 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_554, 0, x_508);
lean_ctor_set(x_554, 1, x_553);
lean_ctor_set(x_554, 2, x_552);
lean_ctor_set(x_554, 3, x_520);
x_555 = lean_mk_syntax_ident(x_2);
x_556 = lean_array_push(x_528, x_554);
x_557 = lean_array_push(x_556, x_555);
x_558 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_558, 0, x_525);
lean_ctor_set(x_558, 1, x_526);
lean_ctor_set(x_558, 2, x_557);
x_559 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__34;
lean_inc(x_508);
x_560 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_560, 0, x_508);
lean_ctor_set(x_560, 1, x_559);
x_561 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__82;
lean_inc(x_511);
lean_inc(x_515);
x_562 = l_Lean_addMacroScope(x_515, x_561, x_511);
x_563 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__79;
x_564 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__84;
lean_inc(x_508);
x_565 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_565, 0, x_508);
lean_ctor_set(x_565, 1, x_563);
lean_ctor_set(x_565, 2, x_562);
lean_ctor_set(x_565, 3, x_564);
x_566 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__43;
lean_inc(x_508);
x_567 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_567, 0, x_508);
lean_ctor_set(x_567, 1, x_566);
x_568 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__44;
lean_inc(x_508);
x_569 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_569, 0, x_508);
lean_ctor_set(x_569, 1, x_568);
x_570 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__90;
lean_inc(x_511);
lean_inc(x_515);
x_571 = l_Lean_addMacroScope(x_515, x_570, x_511);
x_572 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__89;
lean_inc(x_508);
x_573 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_573, 0, x_508);
lean_ctor_set(x_573, 1, x_572);
lean_ctor_set(x_573, 2, x_571);
lean_ctor_set(x_573, 3, x_520);
x_574 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__50;
lean_inc(x_508);
x_575 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_575, 0, x_508);
lean_ctor_set(x_575, 1, x_574);
x_576 = lean_array_push(x_523, x_575);
x_577 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__49;
x_578 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_578, 0, x_525);
lean_ctor_set(x_578, 1, x_577);
lean_ctor_set(x_578, 2, x_576);
lean_inc(x_573);
x_579 = lean_array_push(x_528, x_573);
lean_inc(x_578);
x_580 = lean_array_push(x_579, x_578);
x_581 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_581, 0, x_525);
lean_ctor_set(x_581, 1, x_526);
lean_ctor_set(x_581, 2, x_580);
x_582 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__6;
lean_inc(x_508);
x_583 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_583, 0, x_508);
lean_ctor_set(x_583, 1, x_582);
x_584 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__91;
lean_inc(x_508);
x_585 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_585, 0, x_508);
lean_ctor_set(x_585, 1, x_584);
x_586 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__96;
x_587 = lean_array_push(x_586, x_573);
x_588 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__95;
x_589 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_589, 0, x_525);
lean_ctor_set(x_589, 1, x_588);
lean_ctor_set(x_589, 2, x_587);
x_590 = lean_array_push(x_523, x_589);
x_591 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_591, 0, x_525);
lean_ctor_set(x_591, 1, x_526);
lean_ctor_set(x_591, 2, x_590);
x_592 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__97;
lean_inc(x_508);
x_593 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_593, 0, x_508);
lean_ctor_set(x_593, 1, x_592);
x_594 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__4;
x_595 = l_Array_append___rarg(x_594, x_4);
x_596 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__1;
lean_inc(x_508);
x_597 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_597, 0, x_508);
lean_ctor_set(x_597, 1, x_596);
x_598 = lean_array_push(x_523, x_578);
x_599 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_599, 0, x_525);
lean_ctor_set(x_599, 1, x_526);
lean_ctor_set(x_599, 2, x_598);
x_600 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__54;
x_601 = l_Lean_addMacroScope(x_515, x_600, x_511);
x_602 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__53;
x_603 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__57;
x_604 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_604, 0, x_508);
lean_ctor_set(x_604, 1, x_602);
lean_ctor_set(x_604, 2, x_601);
lean_ctor_set(x_604, 3, x_603);
x_605 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__7;
x_606 = lean_array_push(x_605, x_597);
x_607 = lean_array_push(x_606, x_599);
lean_inc(x_583);
x_608 = lean_array_push(x_607, x_583);
x_609 = lean_array_push(x_608, x_604);
x_610 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__8;
x_611 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_611, 0, x_525);
lean_ctor_set(x_611, 1, x_610);
lean_ctor_set(x_611, 2, x_609);
x_612 = lean_array_push(x_595, x_611);
x_613 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_613, 0, x_525);
lean_ctor_set(x_613, 1, x_526);
lean_ctor_set(x_613, 2, x_612);
x_614 = lean_array_push(x_523, x_613);
x_615 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__47;
x_616 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_616, 0, x_525);
lean_ctor_set(x_616, 1, x_615);
lean_ctor_set(x_616, 2, x_614);
x_617 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__98;
x_618 = lean_array_push(x_617, x_585);
x_619 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__93;
x_620 = lean_array_push(x_618, x_619);
x_621 = lean_array_push(x_620, x_619);
x_622 = lean_array_push(x_621, x_591);
x_623 = lean_array_push(x_622, x_593);
x_624 = lean_array_push(x_623, x_616);
x_625 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__92;
x_626 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_626, 0, x_525);
lean_ctor_set(x_626, 1, x_625);
lean_ctor_set(x_626, 2, x_624);
x_627 = lean_array_push(x_541, x_581);
x_628 = lean_array_push(x_627, x_583);
x_629 = lean_array_push(x_628, x_626);
x_630 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__86;
x_631 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_631, 0, x_525);
lean_ctor_set(x_631, 1, x_630);
lean_ctor_set(x_631, 2, x_629);
x_632 = lean_array_push(x_528, x_569);
x_633 = lean_array_push(x_632, x_631);
x_634 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__45;
x_635 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_635, 0, x_525);
lean_ctor_set(x_635, 1, x_634);
lean_ctor_set(x_635, 2, x_633);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; 
x_636 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__61;
x_637 = lean_array_push(x_636, x_548);
x_638 = lean_array_push(x_637, x_550);
x_639 = lean_array_push(x_638, x_558);
x_640 = lean_array_push(x_639, x_560);
x_641 = lean_array_push(x_640, x_565);
x_642 = lean_array_push(x_641, x_567);
x_643 = lean_array_push(x_642, x_635);
x_644 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__14;
x_645 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_645, 0, x_525);
lean_ctor_set(x_645, 1, x_644);
lean_ctor_set(x_645, 2, x_643);
lean_ctor_set(x_513, 0, x_645);
return x_513;
}
else
{
lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; 
x_646 = lean_ctor_get(x_5, 0);
lean_inc(x_646);
lean_dec(x_5);
x_647 = lean_array_push(x_523, x_646);
x_648 = l_Array_append___rarg(x_594, x_647);
x_649 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_649, 0, x_525);
lean_ctor_set(x_649, 1, x_526);
lean_ctor_set(x_649, 2, x_648);
x_650 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__58;
x_651 = lean_array_push(x_650, x_649);
x_652 = lean_array_push(x_651, x_548);
x_653 = lean_array_push(x_652, x_550);
x_654 = lean_array_push(x_653, x_558);
x_655 = lean_array_push(x_654, x_560);
x_656 = lean_array_push(x_655, x_565);
x_657 = lean_array_push(x_656, x_567);
x_658 = lean_array_push(x_657, x_635);
x_659 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__14;
x_660 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_660, 0, x_525);
lean_ctor_set(x_660, 1, x_659);
lean_ctor_set(x_660, 2, x_658);
lean_ctor_set(x_513, 0, x_660);
return x_513;
}
}
else
{
lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; 
x_661 = lean_ctor_get(x_513, 0);
x_662 = lean_ctor_get(x_513, 1);
lean_inc(x_662);
lean_inc(x_661);
lean_dec(x_513);
x_663 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__17;
lean_inc(x_508);
x_664 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_664, 0, x_508);
lean_ctor_set(x_664, 1, x_663);
x_665 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__76;
lean_inc(x_511);
lean_inc(x_661);
x_666 = l_Lean_addMacroScope(x_661, x_665, x_511);
x_667 = lean_box(0);
x_668 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__75;
lean_inc(x_508);
x_669 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_669, 0, x_508);
lean_ctor_set(x_669, 1, x_668);
lean_ctor_set(x_669, 2, x_666);
lean_ctor_set(x_669, 3, x_667);
x_670 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__26;
x_671 = lean_array_push(x_670, x_505);
x_672 = lean_box(2);
x_673 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__3;
x_674 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_674, 0, x_672);
lean_ctor_set(x_674, 1, x_673);
lean_ctor_set(x_674, 2, x_671);
x_675 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__27;
x_676 = lean_array_push(x_675, x_669);
x_677 = lean_array_push(x_676, x_674);
x_678 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__23;
x_679 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_679, 0, x_672);
lean_ctor_set(x_679, 1, x_678);
lean_ctor_set(x_679, 2, x_677);
x_680 = lean_array_push(x_675, x_3);
x_681 = lean_array_push(x_680, x_679);
x_682 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__19;
x_683 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_683, 0, x_672);
lean_ctor_set(x_683, 1, x_682);
lean_ctor_set(x_683, 2, x_681);
x_684 = lean_array_push(x_670, x_683);
x_685 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_685, 0, x_672);
lean_ctor_set(x_685, 1, x_673);
lean_ctor_set(x_685, 2, x_684);
x_686 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__28;
lean_inc(x_508);
x_687 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_687, 0, x_508);
lean_ctor_set(x_687, 1, x_686);
x_688 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__29;
x_689 = lean_array_push(x_688, x_664);
x_690 = lean_array_push(x_689, x_685);
x_691 = lean_array_push(x_690, x_687);
x_692 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__16;
x_693 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_693, 0, x_672);
lean_ctor_set(x_693, 1, x_692);
lean_ctor_set(x_693, 2, x_691);
x_694 = lean_array_push(x_670, x_693);
x_695 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_695, 0, x_672);
lean_ctor_set(x_695, 1, x_673);
lean_ctor_set(x_695, 2, x_694);
x_696 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__13;
lean_inc(x_508);
x_697 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_697, 0, x_508);
lean_ctor_set(x_697, 1, x_696);
x_698 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__33;
lean_inc(x_511);
lean_inc(x_661);
x_699 = l_Lean_addMacroScope(x_661, x_698, x_511);
x_700 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__32;
lean_inc(x_508);
x_701 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_701, 0, x_508);
lean_ctor_set(x_701, 1, x_700);
lean_ctor_set(x_701, 2, x_699);
lean_ctor_set(x_701, 3, x_667);
x_702 = lean_mk_syntax_ident(x_2);
x_703 = lean_array_push(x_675, x_701);
x_704 = lean_array_push(x_703, x_702);
x_705 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_705, 0, x_672);
lean_ctor_set(x_705, 1, x_673);
lean_ctor_set(x_705, 2, x_704);
x_706 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__34;
lean_inc(x_508);
x_707 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_707, 0, x_508);
lean_ctor_set(x_707, 1, x_706);
x_708 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__82;
lean_inc(x_511);
lean_inc(x_661);
x_709 = l_Lean_addMacroScope(x_661, x_708, x_511);
x_710 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__79;
x_711 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__84;
lean_inc(x_508);
x_712 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_712, 0, x_508);
lean_ctor_set(x_712, 1, x_710);
lean_ctor_set(x_712, 2, x_709);
lean_ctor_set(x_712, 3, x_711);
x_713 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__43;
lean_inc(x_508);
x_714 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_714, 0, x_508);
lean_ctor_set(x_714, 1, x_713);
x_715 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__44;
lean_inc(x_508);
x_716 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_716, 0, x_508);
lean_ctor_set(x_716, 1, x_715);
x_717 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__90;
lean_inc(x_511);
lean_inc(x_661);
x_718 = l_Lean_addMacroScope(x_661, x_717, x_511);
x_719 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__89;
lean_inc(x_508);
x_720 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_720, 0, x_508);
lean_ctor_set(x_720, 1, x_719);
lean_ctor_set(x_720, 2, x_718);
lean_ctor_set(x_720, 3, x_667);
x_721 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__50;
lean_inc(x_508);
x_722 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_722, 0, x_508);
lean_ctor_set(x_722, 1, x_721);
x_723 = lean_array_push(x_670, x_722);
x_724 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__49;
x_725 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_725, 0, x_672);
lean_ctor_set(x_725, 1, x_724);
lean_ctor_set(x_725, 2, x_723);
lean_inc(x_720);
x_726 = lean_array_push(x_675, x_720);
lean_inc(x_725);
x_727 = lean_array_push(x_726, x_725);
x_728 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_728, 0, x_672);
lean_ctor_set(x_728, 1, x_673);
lean_ctor_set(x_728, 2, x_727);
x_729 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__6;
lean_inc(x_508);
x_730 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_730, 0, x_508);
lean_ctor_set(x_730, 1, x_729);
x_731 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__91;
lean_inc(x_508);
x_732 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_732, 0, x_508);
lean_ctor_set(x_732, 1, x_731);
x_733 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__96;
x_734 = lean_array_push(x_733, x_720);
x_735 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__95;
x_736 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_736, 0, x_672);
lean_ctor_set(x_736, 1, x_735);
lean_ctor_set(x_736, 2, x_734);
x_737 = lean_array_push(x_670, x_736);
x_738 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_738, 0, x_672);
lean_ctor_set(x_738, 1, x_673);
lean_ctor_set(x_738, 2, x_737);
x_739 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__97;
lean_inc(x_508);
x_740 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_740, 0, x_508);
lean_ctor_set(x_740, 1, x_739);
x_741 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__4;
x_742 = l_Array_append___rarg(x_741, x_4);
x_743 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__1;
lean_inc(x_508);
x_744 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_744, 0, x_508);
lean_ctor_set(x_744, 1, x_743);
x_745 = lean_array_push(x_670, x_725);
x_746 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_746, 0, x_672);
lean_ctor_set(x_746, 1, x_673);
lean_ctor_set(x_746, 2, x_745);
x_747 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__54;
x_748 = l_Lean_addMacroScope(x_661, x_747, x_511);
x_749 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__53;
x_750 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__57;
x_751 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_751, 0, x_508);
lean_ctor_set(x_751, 1, x_749);
lean_ctor_set(x_751, 2, x_748);
lean_ctor_set(x_751, 3, x_750);
x_752 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__7;
x_753 = lean_array_push(x_752, x_744);
x_754 = lean_array_push(x_753, x_746);
lean_inc(x_730);
x_755 = lean_array_push(x_754, x_730);
x_756 = lean_array_push(x_755, x_751);
x_757 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__8;
x_758 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_758, 0, x_672);
lean_ctor_set(x_758, 1, x_757);
lean_ctor_set(x_758, 2, x_756);
x_759 = lean_array_push(x_742, x_758);
x_760 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_760, 0, x_672);
lean_ctor_set(x_760, 1, x_673);
lean_ctor_set(x_760, 2, x_759);
x_761 = lean_array_push(x_670, x_760);
x_762 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__47;
x_763 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_763, 0, x_672);
lean_ctor_set(x_763, 1, x_762);
lean_ctor_set(x_763, 2, x_761);
x_764 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__98;
x_765 = lean_array_push(x_764, x_732);
x_766 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__93;
x_767 = lean_array_push(x_765, x_766);
x_768 = lean_array_push(x_767, x_766);
x_769 = lean_array_push(x_768, x_738);
x_770 = lean_array_push(x_769, x_740);
x_771 = lean_array_push(x_770, x_763);
x_772 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__92;
x_773 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_773, 0, x_672);
lean_ctor_set(x_773, 1, x_772);
lean_ctor_set(x_773, 2, x_771);
x_774 = lean_array_push(x_688, x_728);
x_775 = lean_array_push(x_774, x_730);
x_776 = lean_array_push(x_775, x_773);
x_777 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__86;
x_778 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_778, 0, x_672);
lean_ctor_set(x_778, 1, x_777);
lean_ctor_set(x_778, 2, x_776);
x_779 = lean_array_push(x_675, x_716);
x_780 = lean_array_push(x_779, x_778);
x_781 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__45;
x_782 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_782, 0, x_672);
lean_ctor_set(x_782, 1, x_781);
lean_ctor_set(x_782, 2, x_780);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; 
x_783 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__61;
x_784 = lean_array_push(x_783, x_695);
x_785 = lean_array_push(x_784, x_697);
x_786 = lean_array_push(x_785, x_705);
x_787 = lean_array_push(x_786, x_707);
x_788 = lean_array_push(x_787, x_712);
x_789 = lean_array_push(x_788, x_714);
x_790 = lean_array_push(x_789, x_782);
x_791 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__14;
x_792 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_792, 0, x_672);
lean_ctor_set(x_792, 1, x_791);
lean_ctor_set(x_792, 2, x_790);
x_793 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_793, 0, x_792);
lean_ctor_set(x_793, 1, x_662);
return x_793;
}
else
{
lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; 
x_794 = lean_ctor_get(x_5, 0);
lean_inc(x_794);
lean_dec(x_5);
x_795 = lean_array_push(x_670, x_794);
x_796 = l_Array_append___rarg(x_741, x_795);
x_797 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_797, 0, x_672);
lean_ctor_set(x_797, 1, x_673);
lean_ctor_set(x_797, 2, x_796);
x_798 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__58;
x_799 = lean_array_push(x_798, x_797);
x_800 = lean_array_push(x_799, x_695);
x_801 = lean_array_push(x_800, x_697);
x_802 = lean_array_push(x_801, x_705);
x_803 = lean_array_push(x_802, x_707);
x_804 = lean_array_push(x_803, x_712);
x_805 = lean_array_push(x_804, x_714);
x_806 = lean_array_push(x_805, x_782);
x_807 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__14;
x_808 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_808, 0, x_672);
lean_ctor_set(x_808, 1, x_807);
lean_ctor_set(x_808, 2, x_806);
x_809 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_809, 0, x_808);
lean_ctor_set(x_809, 1, x_662);
return x_809;
}
}
}
}
else
{
lean_object* x_810; lean_object* x_811; uint8_t x_812; 
x_810 = lean_ctor_get(x_1, 0);
lean_inc(x_810);
lean_dec(x_1);
x_811 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__2;
x_812 = lean_name_eq(x_6, x_811);
if (x_812 == 0)
{
lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_813 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_813, 0, x_6);
x_814 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__100;
x_815 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_815, 0, x_814);
lean_ctor_set(x_815, 1, x_813);
x_816 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__102;
x_817 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_817, 0, x_815);
lean_ctor_set(x_817, 1, x_816);
x_818 = l_Lean_throwErrorAt___at_Lean_Elab_Command_elabCommand___spec__11(x_810, x_817, x_7, x_8, x_9);
return x_818;
}
else
{
lean_object* x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; uint8_t x_829; 
lean_dec(x_6);
lean_inc(x_2);
x_819 = l_Lean_mkIdentFromRef___at_Lean_Elab_Command_elabElabRulesAux___spec__3(x_2, x_7, x_8, x_9);
x_820 = lean_ctor_get(x_819, 0);
lean_inc(x_820);
x_821 = lean_ctor_get(x_819, 1);
lean_inc(x_821);
lean_dec(x_819);
x_822 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Command_elabAuxDef___spec__4(x_7, x_8, x_821);
x_823 = lean_ctor_get(x_822, 0);
lean_inc(x_823);
x_824 = lean_ctor_get(x_822, 1);
lean_inc(x_824);
lean_dec(x_822);
x_825 = l_Lean_Elab_Command_getCurrMacroScope(x_7, x_8, x_824);
lean_dec(x_7);
x_826 = lean_ctor_get(x_825, 0);
lean_inc(x_826);
x_827 = lean_ctor_get(x_825, 1);
lean_inc(x_827);
lean_dec(x_825);
x_828 = l_Lean_Elab_Command_getMainModule___rarg(x_8, x_827);
lean_dec(x_8);
x_829 = !lean_is_exclusive(x_828);
if (x_829 == 0)
{
lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; lean_object* x_874; lean_object* x_875; lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; lean_object* x_895; lean_object* x_896; lean_object* x_897; lean_object* x_898; lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; lean_object* x_903; lean_object* x_904; lean_object* x_905; lean_object* x_906; lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; lean_object* x_911; lean_object* x_912; lean_object* x_913; lean_object* x_914; lean_object* x_915; lean_object* x_916; lean_object* x_917; lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; lean_object* x_925; lean_object* x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; lean_object* x_932; lean_object* x_933; lean_object* x_934; lean_object* x_935; lean_object* x_936; lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; lean_object* x_941; lean_object* x_942; lean_object* x_943; lean_object* x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; lean_object* x_949; lean_object* x_950; lean_object* x_951; lean_object* x_952; lean_object* x_953; lean_object* x_954; lean_object* x_955; lean_object* x_956; lean_object* x_957; lean_object* x_958; lean_object* x_959; lean_object* x_960; lean_object* x_961; lean_object* x_962; lean_object* x_963; lean_object* x_964; lean_object* x_965; lean_object* x_966; lean_object* x_967; lean_object* x_968; lean_object* x_969; lean_object* x_970; lean_object* x_971; lean_object* x_972; lean_object* x_973; lean_object* x_974; 
x_830 = lean_ctor_get(x_828, 0);
x_831 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__17;
lean_inc(x_823);
x_832 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_832, 0, x_823);
lean_ctor_set(x_832, 1, x_831);
x_833 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__76;
lean_inc(x_826);
lean_inc(x_830);
x_834 = l_Lean_addMacroScope(x_830, x_833, x_826);
x_835 = lean_box(0);
x_836 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__75;
lean_inc(x_823);
x_837 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_837, 0, x_823);
lean_ctor_set(x_837, 1, x_836);
lean_ctor_set(x_837, 2, x_834);
lean_ctor_set(x_837, 3, x_835);
x_838 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__26;
x_839 = lean_array_push(x_838, x_820);
x_840 = lean_box(2);
x_841 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__3;
x_842 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_842, 0, x_840);
lean_ctor_set(x_842, 1, x_841);
lean_ctor_set(x_842, 2, x_839);
x_843 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__27;
x_844 = lean_array_push(x_843, x_837);
x_845 = lean_array_push(x_844, x_842);
x_846 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__23;
x_847 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_847, 0, x_840);
lean_ctor_set(x_847, 1, x_846);
lean_ctor_set(x_847, 2, x_845);
x_848 = lean_array_push(x_843, x_3);
x_849 = lean_array_push(x_848, x_847);
x_850 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__19;
x_851 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_851, 0, x_840);
lean_ctor_set(x_851, 1, x_850);
lean_ctor_set(x_851, 2, x_849);
x_852 = lean_array_push(x_838, x_851);
x_853 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_853, 0, x_840);
lean_ctor_set(x_853, 1, x_841);
lean_ctor_set(x_853, 2, x_852);
x_854 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__28;
lean_inc(x_823);
x_855 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_855, 0, x_823);
lean_ctor_set(x_855, 1, x_854);
x_856 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__29;
x_857 = lean_array_push(x_856, x_832);
x_858 = lean_array_push(x_857, x_853);
x_859 = lean_array_push(x_858, x_855);
x_860 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__16;
x_861 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_861, 0, x_840);
lean_ctor_set(x_861, 1, x_860);
lean_ctor_set(x_861, 2, x_859);
x_862 = lean_array_push(x_838, x_861);
x_863 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_863, 0, x_840);
lean_ctor_set(x_863, 1, x_841);
lean_ctor_set(x_863, 2, x_862);
x_864 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__13;
lean_inc(x_823);
x_865 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_865, 0, x_823);
lean_ctor_set(x_865, 1, x_864);
x_866 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__33;
lean_inc(x_826);
lean_inc(x_830);
x_867 = l_Lean_addMacroScope(x_830, x_866, x_826);
x_868 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__32;
lean_inc(x_823);
x_869 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_869, 0, x_823);
lean_ctor_set(x_869, 1, x_868);
lean_ctor_set(x_869, 2, x_867);
lean_ctor_set(x_869, 3, x_835);
x_870 = lean_mk_syntax_ident(x_2);
x_871 = lean_array_push(x_843, x_869);
x_872 = lean_array_push(x_871, x_870);
x_873 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_873, 0, x_840);
lean_ctor_set(x_873, 1, x_841);
lean_ctor_set(x_873, 2, x_872);
x_874 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__34;
lean_inc(x_823);
x_875 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_875, 0, x_823);
lean_ctor_set(x_875, 1, x_874);
x_876 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__82;
lean_inc(x_826);
lean_inc(x_830);
x_877 = l_Lean_addMacroScope(x_830, x_876, x_826);
x_878 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__79;
x_879 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__84;
lean_inc(x_823);
x_880 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_880, 0, x_823);
lean_ctor_set(x_880, 1, x_878);
lean_ctor_set(x_880, 2, x_877);
lean_ctor_set(x_880, 3, x_879);
x_881 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__43;
lean_inc(x_823);
x_882 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_882, 0, x_823);
lean_ctor_set(x_882, 1, x_881);
x_883 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__44;
lean_inc(x_823);
x_884 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_884, 0, x_823);
lean_ctor_set(x_884, 1, x_883);
x_885 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__90;
lean_inc(x_826);
lean_inc(x_830);
x_886 = l_Lean_addMacroScope(x_830, x_885, x_826);
x_887 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__89;
lean_inc(x_823);
x_888 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_888, 0, x_823);
lean_ctor_set(x_888, 1, x_887);
lean_ctor_set(x_888, 2, x_886);
lean_ctor_set(x_888, 3, x_835);
x_889 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__106;
lean_inc(x_826);
lean_inc(x_830);
x_890 = l_Lean_addMacroScope(x_830, x_889, x_826);
x_891 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__105;
lean_inc(x_823);
x_892 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_892, 0, x_823);
lean_ctor_set(x_892, 1, x_891);
lean_ctor_set(x_892, 2, x_890);
lean_ctor_set(x_892, 3, x_835);
lean_inc(x_888);
x_893 = lean_array_push(x_843, x_888);
lean_inc(x_892);
x_894 = lean_array_push(x_893, x_892);
x_895 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_895, 0, x_840);
lean_ctor_set(x_895, 1, x_841);
lean_ctor_set(x_895, 2, x_894);
x_896 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__6;
lean_inc(x_823);
x_897 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_897, 0, x_823);
lean_ctor_set(x_897, 1, x_896);
x_898 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__113;
lean_inc(x_826);
lean_inc(x_830);
x_899 = l_Lean_addMacroScope(x_830, x_898, x_826);
x_900 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__111;
x_901 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__115;
lean_inc(x_823);
x_902 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_902, 0, x_823);
lean_ctor_set(x_902, 1, x_900);
lean_ctor_set(x_902, 2, x_899);
lean_ctor_set(x_902, 3, x_901);
x_903 = lean_array_push(x_838, x_810);
x_904 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_904, 0, x_840);
lean_ctor_set(x_904, 1, x_841);
lean_ctor_set(x_904, 2, x_903);
x_905 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__91;
lean_inc(x_823);
x_906 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_906, 0, x_823);
lean_ctor_set(x_906, 1, x_905);
x_907 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__96;
x_908 = lean_array_push(x_907, x_888);
x_909 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__95;
x_910 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_910, 0, x_840);
lean_ctor_set(x_910, 1, x_909);
lean_ctor_set(x_910, 2, x_908);
x_911 = lean_array_push(x_838, x_910);
x_912 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_912, 0, x_840);
lean_ctor_set(x_912, 1, x_841);
lean_ctor_set(x_912, 2, x_911);
x_913 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__97;
lean_inc(x_823);
x_914 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_914, 0, x_823);
lean_ctor_set(x_914, 1, x_913);
x_915 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__4;
x_916 = l_Array_append___rarg(x_915, x_4);
x_917 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__1;
lean_inc(x_823);
x_918 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_918, 0, x_823);
lean_ctor_set(x_918, 1, x_917);
x_919 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__50;
lean_inc(x_823);
x_920 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_920, 0, x_823);
lean_ctor_set(x_920, 1, x_919);
x_921 = lean_array_push(x_838, x_920);
x_922 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__49;
x_923 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_923, 0, x_840);
lean_ctor_set(x_923, 1, x_922);
lean_ctor_set(x_923, 2, x_921);
x_924 = lean_array_push(x_838, x_923);
x_925 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_925, 0, x_840);
lean_ctor_set(x_925, 1, x_841);
lean_ctor_set(x_925, 2, x_924);
x_926 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__54;
x_927 = l_Lean_addMacroScope(x_830, x_926, x_826);
x_928 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__53;
x_929 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__57;
x_930 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_930, 0, x_823);
lean_ctor_set(x_930, 1, x_928);
lean_ctor_set(x_930, 2, x_927);
lean_ctor_set(x_930, 3, x_929);
x_931 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__7;
x_932 = lean_array_push(x_931, x_918);
x_933 = lean_array_push(x_932, x_925);
lean_inc(x_897);
x_934 = lean_array_push(x_933, x_897);
x_935 = lean_array_push(x_934, x_930);
x_936 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__8;
x_937 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_937, 0, x_840);
lean_ctor_set(x_937, 1, x_936);
lean_ctor_set(x_937, 2, x_935);
x_938 = lean_array_push(x_916, x_937);
x_939 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_939, 0, x_840);
lean_ctor_set(x_939, 1, x_841);
lean_ctor_set(x_939, 2, x_938);
x_940 = lean_array_push(x_838, x_939);
x_941 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__47;
x_942 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_942, 0, x_840);
lean_ctor_set(x_942, 1, x_941);
lean_ctor_set(x_942, 2, x_940);
x_943 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__98;
x_944 = lean_array_push(x_943, x_906);
x_945 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__93;
x_946 = lean_array_push(x_944, x_945);
x_947 = lean_array_push(x_946, x_945);
x_948 = lean_array_push(x_947, x_912);
x_949 = lean_array_push(x_948, x_914);
x_950 = lean_array_push(x_949, x_942);
x_951 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__92;
x_952 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_952, 0, x_840);
lean_ctor_set(x_952, 1, x_951);
lean_ctor_set(x_952, 2, x_950);
x_953 = lean_array_push(x_856, x_904);
lean_inc(x_897);
x_954 = lean_array_push(x_953, x_897);
x_955 = lean_array_push(x_954, x_952);
x_956 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__86;
x_957 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_957, 0, x_840);
lean_ctor_set(x_957, 1, x_956);
lean_ctor_set(x_957, 2, x_955);
x_958 = lean_array_push(x_843, x_884);
lean_inc(x_958);
x_959 = lean_array_push(x_958, x_957);
x_960 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__45;
x_961 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_961, 0, x_840);
lean_ctor_set(x_961, 1, x_960);
lean_ctor_set(x_961, 2, x_959);
x_962 = lean_array_push(x_843, x_892);
x_963 = lean_array_push(x_962, x_961);
x_964 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_964, 0, x_840);
lean_ctor_set(x_964, 1, x_841);
lean_ctor_set(x_964, 2, x_963);
x_965 = lean_array_push(x_843, x_902);
x_966 = lean_array_push(x_965, x_964);
x_967 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__108;
x_968 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_968, 0, x_840);
lean_ctor_set(x_968, 1, x_967);
lean_ctor_set(x_968, 2, x_966);
x_969 = lean_array_push(x_856, x_895);
x_970 = lean_array_push(x_969, x_897);
x_971 = lean_array_push(x_970, x_968);
x_972 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_972, 0, x_840);
lean_ctor_set(x_972, 1, x_956);
lean_ctor_set(x_972, 2, x_971);
x_973 = lean_array_push(x_958, x_972);
x_974 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_974, 0, x_840);
lean_ctor_set(x_974, 1, x_960);
lean_ctor_set(x_974, 2, x_973);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_975; lean_object* x_976; lean_object* x_977; lean_object* x_978; lean_object* x_979; lean_object* x_980; lean_object* x_981; lean_object* x_982; lean_object* x_983; lean_object* x_984; 
x_975 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__61;
x_976 = lean_array_push(x_975, x_863);
x_977 = lean_array_push(x_976, x_865);
x_978 = lean_array_push(x_977, x_873);
x_979 = lean_array_push(x_978, x_875);
x_980 = lean_array_push(x_979, x_880);
x_981 = lean_array_push(x_980, x_882);
x_982 = lean_array_push(x_981, x_974);
x_983 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__14;
x_984 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_984, 0, x_840);
lean_ctor_set(x_984, 1, x_983);
lean_ctor_set(x_984, 2, x_982);
lean_ctor_set(x_828, 0, x_984);
return x_828;
}
else
{
lean_object* x_985; lean_object* x_986; lean_object* x_987; lean_object* x_988; lean_object* x_989; lean_object* x_990; lean_object* x_991; lean_object* x_992; lean_object* x_993; lean_object* x_994; lean_object* x_995; lean_object* x_996; lean_object* x_997; lean_object* x_998; lean_object* x_999; 
x_985 = lean_ctor_get(x_5, 0);
lean_inc(x_985);
lean_dec(x_5);
x_986 = lean_array_push(x_838, x_985);
x_987 = l_Array_append___rarg(x_915, x_986);
x_988 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_988, 0, x_840);
lean_ctor_set(x_988, 1, x_841);
lean_ctor_set(x_988, 2, x_987);
x_989 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__58;
x_990 = lean_array_push(x_989, x_988);
x_991 = lean_array_push(x_990, x_863);
x_992 = lean_array_push(x_991, x_865);
x_993 = lean_array_push(x_992, x_873);
x_994 = lean_array_push(x_993, x_875);
x_995 = lean_array_push(x_994, x_880);
x_996 = lean_array_push(x_995, x_882);
x_997 = lean_array_push(x_996, x_974);
x_998 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__14;
x_999 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_999, 0, x_840);
lean_ctor_set(x_999, 1, x_998);
lean_ctor_set(x_999, 2, x_997);
lean_ctor_set(x_828, 0, x_999);
return x_828;
}
}
else
{
lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; lean_object* x_1010; lean_object* x_1011; lean_object* x_1012; lean_object* x_1013; lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; lean_object* x_1020; lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; lean_object* x_1024; lean_object* x_1025; lean_object* x_1026; lean_object* x_1027; lean_object* x_1028; lean_object* x_1029; lean_object* x_1030; lean_object* x_1031; lean_object* x_1032; lean_object* x_1033; lean_object* x_1034; lean_object* x_1035; lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; lean_object* x_1039; lean_object* x_1040; lean_object* x_1041; lean_object* x_1042; lean_object* x_1043; lean_object* x_1044; lean_object* x_1045; lean_object* x_1046; lean_object* x_1047; lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; lean_object* x_1052; lean_object* x_1053; lean_object* x_1054; lean_object* x_1055; lean_object* x_1056; lean_object* x_1057; lean_object* x_1058; lean_object* x_1059; lean_object* x_1060; lean_object* x_1061; lean_object* x_1062; lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; lean_object* x_1066; lean_object* x_1067; lean_object* x_1068; lean_object* x_1069; lean_object* x_1070; lean_object* x_1071; lean_object* x_1072; lean_object* x_1073; lean_object* x_1074; lean_object* x_1075; lean_object* x_1076; lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; lean_object* x_1080; lean_object* x_1081; lean_object* x_1082; lean_object* x_1083; lean_object* x_1084; lean_object* x_1085; lean_object* x_1086; lean_object* x_1087; lean_object* x_1088; lean_object* x_1089; lean_object* x_1090; lean_object* x_1091; lean_object* x_1092; lean_object* x_1093; lean_object* x_1094; lean_object* x_1095; lean_object* x_1096; lean_object* x_1097; lean_object* x_1098; lean_object* x_1099; lean_object* x_1100; lean_object* x_1101; lean_object* x_1102; lean_object* x_1103; lean_object* x_1104; lean_object* x_1105; lean_object* x_1106; lean_object* x_1107; lean_object* x_1108; lean_object* x_1109; lean_object* x_1110; lean_object* x_1111; lean_object* x_1112; lean_object* x_1113; lean_object* x_1114; lean_object* x_1115; lean_object* x_1116; lean_object* x_1117; lean_object* x_1118; lean_object* x_1119; lean_object* x_1120; lean_object* x_1121; lean_object* x_1122; lean_object* x_1123; lean_object* x_1124; lean_object* x_1125; lean_object* x_1126; lean_object* x_1127; lean_object* x_1128; lean_object* x_1129; lean_object* x_1130; lean_object* x_1131; lean_object* x_1132; lean_object* x_1133; lean_object* x_1134; lean_object* x_1135; lean_object* x_1136; lean_object* x_1137; lean_object* x_1138; lean_object* x_1139; lean_object* x_1140; lean_object* x_1141; lean_object* x_1142; lean_object* x_1143; lean_object* x_1144; lean_object* x_1145; 
x_1000 = lean_ctor_get(x_828, 0);
x_1001 = lean_ctor_get(x_828, 1);
lean_inc(x_1001);
lean_inc(x_1000);
lean_dec(x_828);
x_1002 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__17;
lean_inc(x_823);
x_1003 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1003, 0, x_823);
lean_ctor_set(x_1003, 1, x_1002);
x_1004 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__76;
lean_inc(x_826);
lean_inc(x_1000);
x_1005 = l_Lean_addMacroScope(x_1000, x_1004, x_826);
x_1006 = lean_box(0);
x_1007 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__75;
lean_inc(x_823);
x_1008 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_1008, 0, x_823);
lean_ctor_set(x_1008, 1, x_1007);
lean_ctor_set(x_1008, 2, x_1005);
lean_ctor_set(x_1008, 3, x_1006);
x_1009 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__26;
x_1010 = lean_array_push(x_1009, x_820);
x_1011 = lean_box(2);
x_1012 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__3;
x_1013 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1013, 0, x_1011);
lean_ctor_set(x_1013, 1, x_1012);
lean_ctor_set(x_1013, 2, x_1010);
x_1014 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__27;
x_1015 = lean_array_push(x_1014, x_1008);
x_1016 = lean_array_push(x_1015, x_1013);
x_1017 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__23;
x_1018 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1018, 0, x_1011);
lean_ctor_set(x_1018, 1, x_1017);
lean_ctor_set(x_1018, 2, x_1016);
x_1019 = lean_array_push(x_1014, x_3);
x_1020 = lean_array_push(x_1019, x_1018);
x_1021 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__19;
x_1022 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1022, 0, x_1011);
lean_ctor_set(x_1022, 1, x_1021);
lean_ctor_set(x_1022, 2, x_1020);
x_1023 = lean_array_push(x_1009, x_1022);
x_1024 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1024, 0, x_1011);
lean_ctor_set(x_1024, 1, x_1012);
lean_ctor_set(x_1024, 2, x_1023);
x_1025 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__28;
lean_inc(x_823);
x_1026 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1026, 0, x_823);
lean_ctor_set(x_1026, 1, x_1025);
x_1027 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__29;
x_1028 = lean_array_push(x_1027, x_1003);
x_1029 = lean_array_push(x_1028, x_1024);
x_1030 = lean_array_push(x_1029, x_1026);
x_1031 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__16;
x_1032 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1032, 0, x_1011);
lean_ctor_set(x_1032, 1, x_1031);
lean_ctor_set(x_1032, 2, x_1030);
x_1033 = lean_array_push(x_1009, x_1032);
x_1034 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1034, 0, x_1011);
lean_ctor_set(x_1034, 1, x_1012);
lean_ctor_set(x_1034, 2, x_1033);
x_1035 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__13;
lean_inc(x_823);
x_1036 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1036, 0, x_823);
lean_ctor_set(x_1036, 1, x_1035);
x_1037 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__33;
lean_inc(x_826);
lean_inc(x_1000);
x_1038 = l_Lean_addMacroScope(x_1000, x_1037, x_826);
x_1039 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__32;
lean_inc(x_823);
x_1040 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_1040, 0, x_823);
lean_ctor_set(x_1040, 1, x_1039);
lean_ctor_set(x_1040, 2, x_1038);
lean_ctor_set(x_1040, 3, x_1006);
x_1041 = lean_mk_syntax_ident(x_2);
x_1042 = lean_array_push(x_1014, x_1040);
x_1043 = lean_array_push(x_1042, x_1041);
x_1044 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1044, 0, x_1011);
lean_ctor_set(x_1044, 1, x_1012);
lean_ctor_set(x_1044, 2, x_1043);
x_1045 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__34;
lean_inc(x_823);
x_1046 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1046, 0, x_823);
lean_ctor_set(x_1046, 1, x_1045);
x_1047 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__82;
lean_inc(x_826);
lean_inc(x_1000);
x_1048 = l_Lean_addMacroScope(x_1000, x_1047, x_826);
x_1049 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__79;
x_1050 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__84;
lean_inc(x_823);
x_1051 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_1051, 0, x_823);
lean_ctor_set(x_1051, 1, x_1049);
lean_ctor_set(x_1051, 2, x_1048);
lean_ctor_set(x_1051, 3, x_1050);
x_1052 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__43;
lean_inc(x_823);
x_1053 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1053, 0, x_823);
lean_ctor_set(x_1053, 1, x_1052);
x_1054 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__44;
lean_inc(x_823);
x_1055 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1055, 0, x_823);
lean_ctor_set(x_1055, 1, x_1054);
x_1056 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__90;
lean_inc(x_826);
lean_inc(x_1000);
x_1057 = l_Lean_addMacroScope(x_1000, x_1056, x_826);
x_1058 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__89;
lean_inc(x_823);
x_1059 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_1059, 0, x_823);
lean_ctor_set(x_1059, 1, x_1058);
lean_ctor_set(x_1059, 2, x_1057);
lean_ctor_set(x_1059, 3, x_1006);
x_1060 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__106;
lean_inc(x_826);
lean_inc(x_1000);
x_1061 = l_Lean_addMacroScope(x_1000, x_1060, x_826);
x_1062 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__105;
lean_inc(x_823);
x_1063 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_1063, 0, x_823);
lean_ctor_set(x_1063, 1, x_1062);
lean_ctor_set(x_1063, 2, x_1061);
lean_ctor_set(x_1063, 3, x_1006);
lean_inc(x_1059);
x_1064 = lean_array_push(x_1014, x_1059);
lean_inc(x_1063);
x_1065 = lean_array_push(x_1064, x_1063);
x_1066 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1066, 0, x_1011);
lean_ctor_set(x_1066, 1, x_1012);
lean_ctor_set(x_1066, 2, x_1065);
x_1067 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__6;
lean_inc(x_823);
x_1068 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1068, 0, x_823);
lean_ctor_set(x_1068, 1, x_1067);
x_1069 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__113;
lean_inc(x_826);
lean_inc(x_1000);
x_1070 = l_Lean_addMacroScope(x_1000, x_1069, x_826);
x_1071 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__111;
x_1072 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__115;
lean_inc(x_823);
x_1073 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_1073, 0, x_823);
lean_ctor_set(x_1073, 1, x_1071);
lean_ctor_set(x_1073, 2, x_1070);
lean_ctor_set(x_1073, 3, x_1072);
x_1074 = lean_array_push(x_1009, x_810);
x_1075 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1075, 0, x_1011);
lean_ctor_set(x_1075, 1, x_1012);
lean_ctor_set(x_1075, 2, x_1074);
x_1076 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__91;
lean_inc(x_823);
x_1077 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1077, 0, x_823);
lean_ctor_set(x_1077, 1, x_1076);
x_1078 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__96;
x_1079 = lean_array_push(x_1078, x_1059);
x_1080 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__95;
x_1081 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1081, 0, x_1011);
lean_ctor_set(x_1081, 1, x_1080);
lean_ctor_set(x_1081, 2, x_1079);
x_1082 = lean_array_push(x_1009, x_1081);
x_1083 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1083, 0, x_1011);
lean_ctor_set(x_1083, 1, x_1012);
lean_ctor_set(x_1083, 2, x_1082);
x_1084 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__97;
lean_inc(x_823);
x_1085 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1085, 0, x_823);
lean_ctor_set(x_1085, 1, x_1084);
x_1086 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__4;
x_1087 = l_Array_append___rarg(x_1086, x_4);
x_1088 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__1;
lean_inc(x_823);
x_1089 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1089, 0, x_823);
lean_ctor_set(x_1089, 1, x_1088);
x_1090 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__50;
lean_inc(x_823);
x_1091 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1091, 0, x_823);
lean_ctor_set(x_1091, 1, x_1090);
x_1092 = lean_array_push(x_1009, x_1091);
x_1093 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__49;
x_1094 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1094, 0, x_1011);
lean_ctor_set(x_1094, 1, x_1093);
lean_ctor_set(x_1094, 2, x_1092);
x_1095 = lean_array_push(x_1009, x_1094);
x_1096 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1096, 0, x_1011);
lean_ctor_set(x_1096, 1, x_1012);
lean_ctor_set(x_1096, 2, x_1095);
x_1097 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__54;
x_1098 = l_Lean_addMacroScope(x_1000, x_1097, x_826);
x_1099 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__53;
x_1100 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__57;
x_1101 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_1101, 0, x_823);
lean_ctor_set(x_1101, 1, x_1099);
lean_ctor_set(x_1101, 2, x_1098);
lean_ctor_set(x_1101, 3, x_1100);
x_1102 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__7;
x_1103 = lean_array_push(x_1102, x_1089);
x_1104 = lean_array_push(x_1103, x_1096);
lean_inc(x_1068);
x_1105 = lean_array_push(x_1104, x_1068);
x_1106 = lean_array_push(x_1105, x_1101);
x_1107 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__8;
x_1108 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1108, 0, x_1011);
lean_ctor_set(x_1108, 1, x_1107);
lean_ctor_set(x_1108, 2, x_1106);
x_1109 = lean_array_push(x_1087, x_1108);
x_1110 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1110, 0, x_1011);
lean_ctor_set(x_1110, 1, x_1012);
lean_ctor_set(x_1110, 2, x_1109);
x_1111 = lean_array_push(x_1009, x_1110);
x_1112 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__47;
x_1113 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1113, 0, x_1011);
lean_ctor_set(x_1113, 1, x_1112);
lean_ctor_set(x_1113, 2, x_1111);
x_1114 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__98;
x_1115 = lean_array_push(x_1114, x_1077);
x_1116 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__93;
x_1117 = lean_array_push(x_1115, x_1116);
x_1118 = lean_array_push(x_1117, x_1116);
x_1119 = lean_array_push(x_1118, x_1083);
x_1120 = lean_array_push(x_1119, x_1085);
x_1121 = lean_array_push(x_1120, x_1113);
x_1122 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__92;
x_1123 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1123, 0, x_1011);
lean_ctor_set(x_1123, 1, x_1122);
lean_ctor_set(x_1123, 2, x_1121);
x_1124 = lean_array_push(x_1027, x_1075);
lean_inc(x_1068);
x_1125 = lean_array_push(x_1124, x_1068);
x_1126 = lean_array_push(x_1125, x_1123);
x_1127 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__86;
x_1128 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1128, 0, x_1011);
lean_ctor_set(x_1128, 1, x_1127);
lean_ctor_set(x_1128, 2, x_1126);
x_1129 = lean_array_push(x_1014, x_1055);
lean_inc(x_1129);
x_1130 = lean_array_push(x_1129, x_1128);
x_1131 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__45;
x_1132 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1132, 0, x_1011);
lean_ctor_set(x_1132, 1, x_1131);
lean_ctor_set(x_1132, 2, x_1130);
x_1133 = lean_array_push(x_1014, x_1063);
x_1134 = lean_array_push(x_1133, x_1132);
x_1135 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1135, 0, x_1011);
lean_ctor_set(x_1135, 1, x_1012);
lean_ctor_set(x_1135, 2, x_1134);
x_1136 = lean_array_push(x_1014, x_1073);
x_1137 = lean_array_push(x_1136, x_1135);
x_1138 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__108;
x_1139 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1139, 0, x_1011);
lean_ctor_set(x_1139, 1, x_1138);
lean_ctor_set(x_1139, 2, x_1137);
x_1140 = lean_array_push(x_1027, x_1066);
x_1141 = lean_array_push(x_1140, x_1068);
x_1142 = lean_array_push(x_1141, x_1139);
x_1143 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1143, 0, x_1011);
lean_ctor_set(x_1143, 1, x_1127);
lean_ctor_set(x_1143, 2, x_1142);
x_1144 = lean_array_push(x_1129, x_1143);
x_1145 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1145, 0, x_1011);
lean_ctor_set(x_1145, 1, x_1131);
lean_ctor_set(x_1145, 2, x_1144);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_1146; lean_object* x_1147; lean_object* x_1148; lean_object* x_1149; lean_object* x_1150; lean_object* x_1151; lean_object* x_1152; lean_object* x_1153; lean_object* x_1154; lean_object* x_1155; lean_object* x_1156; 
x_1146 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__61;
x_1147 = lean_array_push(x_1146, x_1034);
x_1148 = lean_array_push(x_1147, x_1036);
x_1149 = lean_array_push(x_1148, x_1044);
x_1150 = lean_array_push(x_1149, x_1046);
x_1151 = lean_array_push(x_1150, x_1051);
x_1152 = lean_array_push(x_1151, x_1053);
x_1153 = lean_array_push(x_1152, x_1145);
x_1154 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__14;
x_1155 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1155, 0, x_1011);
lean_ctor_set(x_1155, 1, x_1154);
lean_ctor_set(x_1155, 2, x_1153);
x_1156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1156, 0, x_1155);
lean_ctor_set(x_1156, 1, x_1001);
return x_1156;
}
else
{
lean_object* x_1157; lean_object* x_1158; lean_object* x_1159; lean_object* x_1160; lean_object* x_1161; lean_object* x_1162; lean_object* x_1163; lean_object* x_1164; lean_object* x_1165; lean_object* x_1166; lean_object* x_1167; lean_object* x_1168; lean_object* x_1169; lean_object* x_1170; lean_object* x_1171; lean_object* x_1172; 
x_1157 = lean_ctor_get(x_5, 0);
lean_inc(x_1157);
lean_dec(x_5);
x_1158 = lean_array_push(x_1009, x_1157);
x_1159 = l_Array_append___rarg(x_1086, x_1158);
x_1160 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1160, 0, x_1011);
lean_ctor_set(x_1160, 1, x_1012);
lean_ctor_set(x_1160, 2, x_1159);
x_1161 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__58;
x_1162 = lean_array_push(x_1161, x_1160);
x_1163 = lean_array_push(x_1162, x_1034);
x_1164 = lean_array_push(x_1163, x_1036);
x_1165 = lean_array_push(x_1164, x_1044);
x_1166 = lean_array_push(x_1165, x_1046);
x_1167 = lean_array_push(x_1166, x_1051);
x_1168 = lean_array_push(x_1167, x_1053);
x_1169 = lean_array_push(x_1168, x_1145);
x_1170 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__14;
x_1171 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1171, 0, x_1011);
lean_ctor_set(x_1171, 1, x_1170);
lean_ctor_set(x_1171, 2, x_1169);
x_1172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1172, 0, x_1171);
lean_ctor_set(x_1172, 1, x_1001);
return x_1172;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid elab_rules command, specify category using `elab_rules : <cat> ...`");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRulesAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_10 = lean_array_get_size(x_6);
x_11 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_12 = 0;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_3);
x_13 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2(x_3, x_11, x_12, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
if (lean_obj_tag(x_4) == 0)
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lean_Elab_Command_elabElabRulesAux___closed__2;
x_16 = l_Lean_throwError___at_Lean_Elab_Command_resolveSyntaxKind___spec__3(x_15, x_7, x_8, x_14);
lean_dec(x_8);
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
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_13, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_13, 1);
lean_inc(x_22);
lean_dec(x_13);
x_23 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__2;
x_24 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1(x_5, x_3, x_2, x_21, x_1, x_23, x_7, x_8, x_22);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_13, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_13, 1);
lean_inc(x_26);
lean_dec(x_13);
x_27 = lean_ctor_get(x_4, 0);
lean_inc(x_27);
lean_dec(x_4);
x_28 = l_Lean_Syntax_getId(x_27);
lean_dec(x_27);
x_29 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1(x_5, x_3, x_2, x_25, x_1, x_28, x_7, x_8, x_26);
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_13);
if (x_30 == 0)
{
return x_13;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_13, 0);
x_32 = lean_ctor_get(x_13, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_13);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabElabRulesAux___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_forInUnsafe_loop___at_Lean_Elab_Command_elabElabRulesAux___spec__1(x_1, x_2, x_3, x_7, x_8, x_6);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___at_Lean_Elab_Command_elabElabRulesAux___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_mkIdentFromRef___at_Lean_Elab_Command_elabElabRulesAux___spec__3(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_unsigned_to_nat(6u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
x_14 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__46;
x_15 = lean_name_mk_string(x_2, x_14);
lean_inc(x_13);
x_16 = l_Lean_Syntax_isOfKind(x_13, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_17 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabCommand___spec__14___rarg(x_11);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Lean_Syntax_getArg(x_13, x_18);
lean_dec(x_13);
x_20 = l_Lean_Syntax_getArgs(x_19);
lean_dec(x_19);
x_21 = l_Lean_Syntax_getId(x_3);
lean_inc(x_10);
lean_inc(x_9);
x_22 = l_Lean_Elab_Command_resolveSyntaxKind(x_21, x_9, x_10, x_11);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_Elab_Command_elabElabRulesAux(x_4, x_5, x_23, x_6, x_8, x_20, x_9, x_10, x_24);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_20);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_26 = !lean_is_exclusive(x_22);
if (x_26 == 0)
{
return x_22;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_22, 0);
x_28 = lean_ctor_get(x_22, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_22);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
lean_dec(x_6);
x_11 = lean_unsigned_to_nat(5u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = l_Lean_Syntax_isNone(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = l_Lean_nullKind;
x_15 = lean_unsigned_to_nat(2u);
lean_inc(x_12);
x_16 = l_Lean_Syntax_isNodeOf(x_12, x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_17 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabCommand___spec__14___rarg(x_10);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = l_Lean_Syntax_getArg(x_12, x_18);
lean_dec(x_12);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_box(0);
x_22 = l_Lean_Elab_Command_elabElabRules___lambda__1(x_1, x_2, x_3, x_4, x_5, x_7, x_21, x_20, x_8, x_9, x_10);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_12);
x_23 = lean_box(0);
x_24 = lean_box(0);
x_25 = l_Lean_Elab_Command_elabElabRules___lambda__1(x_1, x_2, x_3, x_4, x_5, x_7, x_24, x_23, x_8, x_9, x_10);
return x_25;
}
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRules___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elab_rules");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRules___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(7u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRules___lambda__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("<=");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRules___lambda__3___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("(");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRules___lambda__3___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("kind");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRules___lambda__3___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(")");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRules___lambda__3___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(5u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_12 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Command_elabAuxDef___spec__4(x_9, x_10, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Elab_Command_getCurrMacroScope(x_9, x_10, x_14);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_Elab_Command_getMainModule___rarg(x_10, x_16);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_19 = x_17;
} else {
 lean_dec_ref(x_17);
 x_19 = lean_box(0);
}
x_20 = l_Lean_Elab_Command_elabElabRules___lambda__3___closed__1;
lean_inc(x_13);
x_21 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_21, 0, x_13);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__4;
x_23 = l_Array_append___rarg(x_22, x_8);
x_24 = lean_box(2);
x_25 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__3;
x_26 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_26, 2, x_23);
x_27 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__26;
x_28 = lean_array_push(x_27, x_26);
x_29 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_29, 0, x_24);
lean_ctor_set(x_29, 1, x_1);
lean_ctor_set(x_29, 2, x_28);
if (lean_obj_tag(x_6) == 0)
{
x_30 = x_22;
goto block_86;
}
else
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_6, 0);
lean_inc(x_87);
lean_dec(x_6);
x_88 = lean_array_push(x_27, x_87);
x_30 = x_88;
goto block_86;
}
block_86:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_31 = l_Array_append___rarg(x_22, x_30);
x_32 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_32, 0, x_24);
lean_ctor_set(x_32, 1, x_25);
lean_ctor_set(x_32, 2, x_31);
x_33 = l_Lean_Elab_Command_elabElabRules___lambda__3___closed__2;
x_34 = lean_array_push(x_33, x_32);
x_35 = lean_array_push(x_34, x_2);
x_36 = lean_array_push(x_35, x_21);
if (lean_obj_tag(x_7) == 0)
{
x_37 = x_22;
goto block_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_70 = lean_ctor_get(x_7, 0);
lean_inc(x_70);
lean_dec(x_7);
x_71 = lean_mk_syntax_ident(x_70);
x_72 = l_Lean_Elab_Command_elabElabRules___lambda__3___closed__4;
lean_inc(x_13);
x_73 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_73, 0, x_13);
lean_ctor_set(x_73, 1, x_72);
x_74 = l_Lean_Elab_Command_elabElabRules___lambda__3___closed__5;
lean_inc(x_13);
x_75 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_75, 0, x_13);
lean_ctor_set(x_75, 1, x_74);
x_76 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__43;
lean_inc(x_13);
x_77 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_77, 0, x_13);
lean_ctor_set(x_77, 1, x_76);
x_78 = l_Lean_Elab_Command_elabElabRules___lambda__3___closed__6;
lean_inc(x_13);
x_79 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_79, 0, x_13);
lean_ctor_set(x_79, 1, x_78);
x_80 = l_Lean_Elab_Command_elabElabRules___lambda__3___closed__7;
x_81 = lean_array_push(x_80, x_73);
x_82 = lean_array_push(x_81, x_75);
x_83 = lean_array_push(x_82, x_77);
x_84 = lean_array_push(x_83, x_71);
x_85 = lean_array_push(x_84, x_79);
x_37 = x_85;
goto block_69;
}
block_69:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = l_Array_append___rarg(x_22, x_37);
x_39 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_39, 0, x_24);
lean_ctor_set(x_39, 1, x_25);
lean_ctor_set(x_39, 2, x_38);
x_40 = lean_array_push(x_36, x_39);
if (lean_obj_tag(x_5) == 0)
{
x_41 = x_22;
goto block_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_63 = lean_ctor_get(x_5, 0);
lean_inc(x_63);
lean_dec(x_5);
x_64 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__34;
lean_inc(x_13);
x_65 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_65, 0, x_13);
lean_ctor_set(x_65, 1, x_64);
x_66 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__27;
x_67 = lean_array_push(x_66, x_65);
x_68 = lean_array_push(x_67, x_63);
x_41 = x_68;
goto block_62;
}
block_62:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = l_Array_append___rarg(x_22, x_41);
x_43 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_43, 0, x_24);
lean_ctor_set(x_43, 1, x_25);
lean_ctor_set(x_43, 2, x_42);
x_44 = lean_array_push(x_40, x_43);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_13);
x_45 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__60;
x_46 = lean_array_push(x_44, x_45);
x_47 = lean_array_push(x_46, x_29);
x_48 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_48, 0, x_24);
lean_ctor_set(x_48, 1, x_4);
lean_ctor_set(x_48, 2, x_47);
if (lean_is_scalar(x_19)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_19;
}
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_18);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_50 = lean_ctor_get(x_3, 0);
lean_inc(x_50);
lean_dec(x_3);
x_51 = l_Lean_Elab_Command_elabElabRules___lambda__3___closed__3;
x_52 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_52, 0, x_13);
lean_ctor_set(x_52, 1, x_51);
x_53 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__27;
x_54 = lean_array_push(x_53, x_52);
x_55 = lean_array_push(x_54, x_50);
x_56 = l_Array_append___rarg(x_22, x_55);
x_57 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_57, 0, x_24);
lean_ctor_set(x_57, 1, x_25);
lean_ctor_set(x_57, 2, x_56);
x_58 = lean_array_push(x_44, x_57);
x_59 = lean_array_push(x_58, x_29);
x_60 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_60, 0, x_24);
lean_ctor_set(x_60, 1, x_4);
lean_ctor_set(x_60, 2, x_59);
if (lean_is_scalar(x_19)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_19;
}
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_18);
return x_61;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_unsigned_to_nat(6u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
x_14 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__46;
x_15 = lean_name_mk_string(x_2, x_14);
lean_inc(x_13);
x_16 = l_Lean_Syntax_isOfKind(x_13, x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_17 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabCommand___spec__14___rarg(x_11);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Lean_Syntax_getArg(x_13, x_18);
lean_dec(x_13);
x_20 = l_Lean_Syntax_getArgs(x_19);
lean_dec(x_19);
x_21 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabElabRules___lambda__3___boxed), 11, 6);
lean_closure_set(x_21, 0, x_15);
lean_closure_set(x_21, 1, x_3);
lean_closure_set(x_21, 2, x_8);
lean_closure_set(x_21, 3, x_4);
lean_closure_set(x_21, 4, x_5);
lean_closure_set(x_21, 5, x_6);
x_22 = l_Lean_Elab_Command_elabElabRules___lambda__3___closed__1;
x_23 = l_Lean_Elab_Command_expandNoKindMacroRulesAux(x_20, x_22, x_21, x_9, x_10, x_11);
lean_dec(x_20);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
lean_dec(x_6);
x_11 = lean_unsigned_to_nat(5u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = l_Lean_Syntax_isNone(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = l_Lean_nullKind;
x_15 = lean_unsigned_to_nat(2u);
lean_inc(x_12);
x_16 = l_Lean_Syntax_isNodeOf(x_12, x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_17 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabCommand___spec__14___rarg(x_10);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = l_Lean_Syntax_getArg(x_12, x_18);
lean_dec(x_12);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_box(0);
x_22 = l_Lean_Elab_Command_elabElabRules___lambda__4(x_1, x_2, x_3, x_4, x_7, x_5, x_21, x_20, x_8, x_9, x_10);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_12);
x_23 = lean_box(0);
x_24 = lean_box(0);
x_25 = l_Lean_Elab_Command_elabElabRules___lambda__4(x_1, x_2, x_3, x_4, x_7, x_5, x_24, x_23, x_8, x_9, x_10);
return x_25;
}
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRules___lambda__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("attrKind");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_dec(x_4);
x_9 = lean_unsigned_to_nat(1u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
x_11 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__5;
x_12 = lean_name_mk_string(x_2, x_11);
x_13 = l_Lean_Elab_Command_elabElabRules___lambda__6___closed__1;
lean_inc(x_12);
x_14 = lean_name_mk_string(x_12, x_13);
lean_inc(x_10);
x_15 = l_Lean_Syntax_isOfKind(x_10, x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_16 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabCommand___spec__14___rarg(x_8);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_unsigned_to_nat(3u);
x_18 = l_Lean_Syntax_getArg(x_1, x_17);
x_19 = l_Lean_nullKind;
x_20 = lean_unsigned_to_nat(0u);
lean_inc(x_18);
x_21 = l_Lean_Syntax_isNodeOf(x_18, x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
lean_dec(x_3);
x_22 = lean_unsigned_to_nat(5u);
lean_inc(x_18);
x_23 = l_Lean_Syntax_isNodeOf(x_18, x_19, x_22);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_24 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabCommand___spec__14___rarg(x_8);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = l_Lean_Syntax_getArg(x_18, x_17);
lean_dec(x_18);
x_26 = lean_unsigned_to_nat(4u);
x_27 = l_Lean_Syntax_getArg(x_1, x_26);
x_28 = l_Lean_Syntax_isNone(x_27);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_unsigned_to_nat(2u);
lean_inc(x_27);
x_30 = l_Lean_Syntax_isNodeOf(x_27, x_19, x_29);
if (x_30 == 0)
{
lean_object* x_31; 
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_31 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabCommand___spec__14___rarg(x_8);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = l_Lean_Syntax_getArg(x_27, x_9);
lean_dec(x_27);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_box(0);
x_35 = l_Lean_Elab_Command_elabElabRules___lambda__2(x_1, x_12, x_25, x_5, x_10, x_34, x_33, x_6, x_7, x_8);
lean_dec(x_25);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_27);
x_36 = lean_box(0);
x_37 = lean_box(0);
x_38 = l_Lean_Elab_Command_elabElabRules___lambda__2(x_1, x_12, x_25, x_5, x_10, x_37, x_36, x_6, x_7, x_8);
lean_dec(x_25);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
lean_dec(x_18);
x_39 = lean_unsigned_to_nat(4u);
x_40 = l_Lean_Syntax_getArg(x_1, x_39);
x_41 = l_Lean_Syntax_isNone(x_40);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_unsigned_to_nat(2u);
lean_inc(x_40);
x_43 = l_Lean_Syntax_isNodeOf(x_40, x_19, x_42);
if (x_43 == 0)
{
lean_object* x_44; 
lean_dec(x_40);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_44 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabCommand___spec__14___rarg(x_8);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = l_Lean_Syntax_getArg(x_40, x_9);
lean_dec(x_40);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_47 = lean_box(0);
x_48 = l_Lean_Elab_Command_elabElabRules___lambda__5(x_1, x_12, x_10, x_3, x_5, x_47, x_46, x_6, x_7, x_8);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_40);
x_49 = lean_box(0);
x_50 = lean_box(0);
x_51 = l_Lean_Elab_Command_elabElabRules___lambda__5(x_1, x_12, x_10, x_3, x_5, x_50, x_49, x_6, x_7, x_8);
return x_51;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRules___lambda__7___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__4;
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__11;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRules___lambda__7___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabElabRules___lambda__7___closed__1;
x_2 = l_Lean_Elab_Command_elabElabRules___lambda__3___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRules___lambda__7___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("docComment");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRules___lambda__7___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabElabRules___lambda__7___closed__1;
x_2 = l_Lean_Elab_Command_elabElabRules___lambda__7___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Elab_Command_elabElabRules___lambda__7___closed__2;
lean_inc(x_1);
x_6 = l_Lean_Syntax_isOfKind(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabCommand___spec__14___rarg(x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = l_Lean_Syntax_isNone(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = l_Lean_nullKind;
x_12 = lean_unsigned_to_nat(1u);
lean_inc(x_9);
x_13 = l_Lean_Syntax_isNodeOf(x_9, x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_14 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabCommand___spec__14___rarg(x_4);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = l_Lean_Syntax_getArg(x_9, x_8);
lean_dec(x_9);
x_16 = l_Lean_Elab_Command_elabElabRules___lambda__7___closed__4;
lean_inc(x_15);
x_17 = l_Lean_Syntax_isOfKind(x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Command_elabCommand___spec__14___rarg(x_4);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_15);
x_20 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__4;
x_21 = lean_box(0);
x_22 = l_Lean_Elab_Command_elabElabRules___lambda__6(x_1, x_20, x_5, x_21, x_19, x_2, x_3, x_4);
lean_dec(x_1);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_9);
x_23 = lean_box(0);
x_24 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__4;
x_25 = lean_box(0);
x_26 = l_Lean_Elab_Command_elabElabRules___lambda__6(x_1, x_24, x_5, x_25, x_23, x_2, x_3, x_4);
lean_dec(x_1);
return x_26;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRules___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabElabRules___lambda__7), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Elab_Command_elabElabRules___closed__1;
x_6 = l_Lean_Elab_Command_adaptExpander(x_5, x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Command_elabElabRules___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Command_elabElabRules___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Command_elabElabRules___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Command_elabElabRules___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Command_elabElabRules___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Command_elabElabRules___lambda__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabElabRules___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabElabRules");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabElabRules___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__12;
x_2 = l___regBuiltin_Lean_Elab_Command_elabElabRules___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabElabRules___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_commandElabAttribute;
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabElabRules___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabElabRules), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabElabRules(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Command_elabElabRules___closed__3;
x_3 = l_Lean_Elab_Command_elabElabRules___lambda__7___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_elabElabRules___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Command_elabElabRules___closed__4;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(70u);
x_2 = lean_unsigned_to_nat(35u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(77u);
x_2 = lean_unsigned_to_nat(32u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange___closed__1;
x_2 = lean_unsigned_to_nat(35u);
x_3 = l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange___closed__2;
x_4 = lean_unsigned_to_nat(32u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(70u);
x_2 = lean_unsigned_to_nat(39u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(70u);
x_2 = lean_unsigned_to_nat(52u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange___closed__4;
x_2 = lean_unsigned_to_nat(39u);
x_3 = l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange___closed__5;
x_4 = lean_unsigned_to_nat(52u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Command_elabElabRules___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_expandElab___spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_2, x_1);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_4);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_array_uget(x_3, x_2);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_array_uset(x_3, x_2, x_9);
lean_inc(x_4);
x_11 = l_Lean_Elab_Command_expandMacroArg(x_8, x_4, x_5);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = 1;
x_15 = lean_usize_add(x_2, x_14);
x_16 = lean_array_uset(x_10, x_2, x_12);
x_2 = x_15;
x_3 = x_16;
x_5 = x_13;
goto _start;
}
else
{
uint8_t x_18; 
lean_dec(x_10);
lean_dec(x_4);
x_18 = !lean_is_exclusive(x_11);
if (x_18 == 0)
{
return x_11;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_11, 0);
x_20 = lean_ctor_get(x_11, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_11);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkIdentFromRef___at_Lean_Elab_Command_expandElab___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 5);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Lean_mkIdentFrom(x_4, x_1);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandElab___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("syntax");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandElab___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("namedName");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandElab___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("name");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandElab___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("namedPrio");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandElab___lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("priority");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandElab___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(9u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandElab___lambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__26;
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__93;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandElab___lambda__1___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("quot");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandElab___lambda__1___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("`(");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandElab___lambda__1___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("precedence");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandElab___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; 
lean_inc(x_16);
x_18 = l_Lean_Macro_getCurrNamespace(x_16, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; size_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_15);
x_21 = l_Lean_Name_append(x_19, x_15);
lean_dec(x_19);
x_22 = lean_box(2);
x_23 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
lean_ctor_set(x_23, 2, x_1);
lean_inc(x_16);
x_24 = l_Lean_mkIdentFromRef___at_Lean_Elab_Command_expandElab___spec__2(x_15, x_16, x_20);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_MonadRef_mkInfoFromRefPos___at___aux__Init__Notation______macroRules__precMax__1___spec__1(x_16, x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_30 = x_27;
} else {
 lean_dec_ref(x_27);
 x_30 = lean_box(0);
}
x_31 = l_Lean_Elab_Command_expandElab___lambda__1___closed__1;
lean_inc(x_2);
x_32 = lean_name_mk_string(x_2, x_31);
lean_inc(x_28);
x_33 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_33, 0, x_28);
lean_ctor_set(x_33, 1, x_31);
x_34 = l_Lean_Elab_Command_expandElab___lambda__1___closed__2;
lean_inc(x_2);
x_35 = lean_name_mk_string(x_2, x_34);
x_36 = l_Lean_Elab_Command_elabElabRules___lambda__3___closed__4;
lean_inc(x_28);
x_37 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_37, 0, x_28);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Lean_Elab_Command_expandElab___lambda__1___closed__3;
lean_inc(x_28);
x_39 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_39, 0, x_28);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__43;
lean_inc(x_28);
x_41 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_41, 0, x_28);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_Elab_Command_elabElabRules___lambda__3___closed__6;
lean_inc(x_28);
x_43 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_43, 0, x_28);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_Elab_Command_elabElabRules___lambda__3___closed__7;
x_45 = lean_array_push(x_44, x_37);
lean_inc(x_45);
x_46 = lean_array_push(x_45, x_39);
lean_inc(x_41);
x_47 = lean_array_push(x_46, x_41);
x_48 = lean_array_push(x_47, x_25);
lean_inc(x_43);
x_49 = lean_array_push(x_48, x_43);
x_50 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_50, 0, x_22);
lean_ctor_set(x_50, 1, x_35);
lean_ctor_set(x_50, 2, x_49);
x_51 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__26;
x_52 = lean_array_push(x_51, x_50);
x_53 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__3;
x_54 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_54, 0, x_22);
lean_ctor_set(x_54, 1, x_53);
lean_ctor_set(x_54, 2, x_52);
x_55 = l_Lean_Elab_Command_expandElab___lambda__1___closed__4;
lean_inc(x_2);
x_56 = lean_name_mk_string(x_2, x_55);
x_57 = l_Lean_Elab_Command_expandElab___lambda__1___closed__5;
lean_inc(x_28);
x_58 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_58, 0, x_28);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Nat_repr(x_3);
x_60 = l_Lean_numLitKind;
x_61 = l_Lean_Syntax_mkLit(x_60, x_59, x_22);
x_62 = lean_array_push(x_45, x_58);
x_63 = lean_array_push(x_62, x_41);
x_64 = lean_array_push(x_63, x_61);
lean_inc(x_43);
x_65 = lean_array_push(x_64, x_43);
x_66 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_66, 0, x_22);
lean_ctor_set(x_66, 1, x_56);
lean_ctor_set(x_66, 2, x_65);
x_67 = lean_array_push(x_51, x_66);
x_68 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_68, 0, x_22);
lean_ctor_set(x_68, 1, x_53);
lean_ctor_set(x_68, 2, x_67);
x_69 = lean_array_get_size(x_4);
x_70 = lean_usize_of_nat(x_69);
lean_dec(x_69);
x_71 = l_Array_mapMUnsafe_map___at___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___spec__3(x_70, x_5, x_4);
x_72 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__4;
x_73 = l_Array_append___rarg(x_72, x_71);
x_74 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_74, 0, x_22);
lean_ctor_set(x_74, 1, x_53);
lean_ctor_set(x_74, 2, x_73);
x_75 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__34;
lean_inc(x_28);
x_76 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_76, 0, x_28);
lean_ctor_set(x_76, 1, x_75);
x_77 = l_Lean_Elab_Command_elabElabRules___lambda__3___closed__1;
x_78 = lean_name_mk_string(x_2, x_77);
x_79 = l_Lean_Elab_Command_expandElab___lambda__1___closed__7;
x_80 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_80, 0, x_22);
lean_ctor_set(x_80, 1, x_6);
lean_ctor_set(x_80, 2, x_79);
lean_inc(x_28);
x_81 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_81, 0, x_28);
lean_ctor_set(x_81, 1, x_77);
x_82 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__27;
lean_inc(x_76);
x_83 = lean_array_push(x_82, x_76);
lean_inc(x_7);
lean_inc(x_83);
x_84 = lean_array_push(x_83, x_7);
x_85 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_85, 0, x_22);
lean_ctor_set(x_85, 1, x_53);
lean_ctor_set(x_85, 2, x_84);
x_86 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__46;
lean_inc(x_8);
x_87 = lean_name_mk_string(x_8, x_86);
x_88 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__7;
lean_inc(x_8);
x_89 = lean_name_mk_string(x_8, x_88);
x_90 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__1;
lean_inc(x_28);
x_91 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_91, 0, x_28);
lean_ctor_set(x_91, 1, x_90);
x_92 = l_Lean_Elab_Command_expandElab___lambda__1___closed__8;
x_93 = lean_name_mk_string(x_8, x_92);
x_94 = l_Lean_Elab_Command_expandElab___lambda__1___closed__9;
lean_inc(x_28);
x_95 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_95, 0, x_28);
lean_ctor_set(x_95, 1, x_94);
x_96 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__29;
x_97 = lean_array_push(x_96, x_95);
x_98 = lean_array_push(x_97, x_23);
x_99 = lean_array_push(x_98, x_43);
x_100 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_100, 0, x_22);
lean_ctor_set(x_100, 1, x_93);
lean_ctor_set(x_100, 2, x_99);
x_101 = lean_array_push(x_51, x_100);
x_102 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_102, 0, x_22);
lean_ctor_set(x_102, 1, x_53);
lean_ctor_set(x_102, 2, x_101);
x_103 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__6;
lean_inc(x_28);
x_104 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_104, 0, x_28);
lean_ctor_set(x_104, 1, x_103);
x_105 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__7;
x_106 = lean_array_push(x_105, x_91);
x_107 = lean_array_push(x_106, x_102);
x_108 = lean_array_push(x_107, x_104);
x_109 = lean_array_push(x_108, x_9);
x_110 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_110, 0, x_22);
lean_ctor_set(x_110, 1, x_89);
lean_ctor_set(x_110, 2, x_109);
x_111 = lean_array_push(x_51, x_110);
x_112 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_112, 0, x_22);
lean_ctor_set(x_112, 1, x_53);
lean_ctor_set(x_112, 2, x_111);
x_113 = lean_array_push(x_51, x_112);
x_114 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_114, 0, x_22);
lean_ctor_set(x_114, 1, x_87);
lean_ctor_set(x_114, 2, x_113);
if (lean_obj_tag(x_14) == 0)
{
x_115 = x_72;
goto block_167;
}
else
{
lean_object* x_168; lean_object* x_169; 
x_168 = lean_ctor_get(x_14, 0);
lean_inc(x_168);
lean_dec(x_14);
x_169 = lean_array_push(x_51, x_168);
x_115 = x_169;
goto block_167;
}
block_167:
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_116 = l_Array_append___rarg(x_72, x_115);
x_117 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_117, 0, x_22);
lean_ctor_set(x_117, 1, x_53);
lean_ctor_set(x_117, 2, x_116);
x_118 = l_Lean_Elab_Command_expandElab___lambda__1___closed__6;
lean_inc(x_117);
x_119 = lean_array_push(x_118, x_117);
x_120 = lean_array_push(x_119, x_10);
x_121 = lean_array_push(x_120, x_33);
x_122 = l_Lean_Elab_Command_elabElabRules___lambda__3___closed__2;
x_123 = lean_array_push(x_122, x_117);
x_124 = lean_array_push(x_123, x_80);
x_125 = lean_array_push(x_124, x_81);
x_126 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__93;
x_127 = lean_array_push(x_125, x_126);
x_128 = lean_array_push(x_127, x_85);
if (lean_obj_tag(x_12) == 0)
{
lean_dec(x_83);
lean_dec(x_13);
x_129 = x_72;
goto block_160;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_161 = lean_ctor_get(x_12, 0);
lean_inc(x_161);
lean_dec(x_12);
x_162 = l_Lean_Elab_Command_expandElab___lambda__1___closed__10;
x_163 = lean_name_mk_string(x_13, x_162);
x_164 = lean_array_push(x_83, x_161);
x_165 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_165, 0, x_22);
lean_ctor_set(x_165, 1, x_163);
lean_ctor_set(x_165, 2, x_164);
x_166 = lean_array_push(x_51, x_165);
x_129 = x_166;
goto block_160;
}
block_160:
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_130 = l_Array_append___rarg(x_72, x_129);
x_131 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_131, 0, x_22);
lean_ctor_set(x_131, 1, x_53);
lean_ctor_set(x_131, 2, x_130);
x_132 = lean_array_push(x_121, x_131);
x_133 = lean_array_push(x_132, x_54);
x_134 = lean_array_push(x_133, x_68);
x_135 = lean_array_push(x_134, x_74);
x_136 = lean_array_push(x_135, x_76);
x_137 = lean_array_push(x_136, x_7);
x_138 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_138, 0, x_22);
lean_ctor_set(x_138, 1, x_32);
lean_ctor_set(x_138, 2, x_137);
x_139 = lean_array_push(x_82, x_138);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_dec(x_28);
x_140 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__60;
x_141 = lean_array_push(x_128, x_140);
x_142 = lean_array_push(x_141, x_114);
x_143 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_143, 0, x_22);
lean_ctor_set(x_143, 1, x_78);
lean_ctor_set(x_143, 2, x_142);
x_144 = lean_array_push(x_139, x_143);
x_145 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_145, 0, x_22);
lean_ctor_set(x_145, 1, x_53);
lean_ctor_set(x_145, 2, x_144);
if (lean_is_scalar(x_30)) {
 x_146 = lean_alloc_ctor(0, 2, 0);
} else {
 x_146 = x_30;
}
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_29);
return x_146;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_147 = lean_ctor_get(x_11, 0);
lean_inc(x_147);
lean_dec(x_11);
x_148 = l_Lean_Elab_Command_elabElabRules___lambda__3___closed__3;
x_149 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_149, 0, x_28);
lean_ctor_set(x_149, 1, x_148);
x_150 = lean_array_push(x_82, x_149);
x_151 = lean_array_push(x_150, x_147);
x_152 = l_Array_append___rarg(x_72, x_151);
x_153 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_153, 0, x_22);
lean_ctor_set(x_153, 1, x_53);
lean_ctor_set(x_153, 2, x_152);
x_154 = lean_array_push(x_128, x_153);
x_155 = lean_array_push(x_154, x_114);
x_156 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_156, 0, x_22);
lean_ctor_set(x_156, 1, x_78);
lean_ctor_set(x_156, 2, x_155);
x_157 = lean_array_push(x_139, x_156);
x_158 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_158, 0, x_22);
lean_ctor_set(x_158, 1, x_53);
lean_ctor_set(x_158, 2, x_157);
if (lean_is_scalar(x_30)) {
 x_159 = lean_alloc_ctor(0, 2, 0);
} else {
 x_159 = x_30;
}
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_29);
return x_159;
}
}
}
}
else
{
uint8_t x_170; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_170 = !lean_is_exclusive(x_18);
if (x_170 == 0)
{
return x_18;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_171 = lean_ctor_get(x_18, 0);
x_172 = lean_ctor_get(x_18, 1);
lean_inc(x_172);
lean_inc(x_171);
lean_dec(x_18);
x_173 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_173, 0, x_171);
lean_ctor_set(x_173, 1, x_172);
return x_173;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandElab___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_13);
x_17 = lean_unsigned_to_nat(4u);
x_18 = l_Lean_Syntax_getArg(x_1, x_17);
lean_dec(x_1);
x_19 = l_Lean_Syntax_getArgs(x_2);
lean_dec(x_2);
lean_inc(x_15);
x_20 = l_Lean_evalOptPrio(x_3, x_15, x_16);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Syntax_getId(x_4);
x_24 = lean_array_get_size(x_19);
x_25 = lean_usize_of_nat(x_24);
lean_dec(x_24);
x_26 = 0;
lean_inc(x_15);
x_27 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_expandElab___spec__1(x_25, x_26, x_19, x_15, x_22);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Array_unzip___rarg(x_28);
lean_dec(x_28);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_box(2);
x_34 = l_Lean_nullKind;
lean_inc(x_31);
x_35 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set(x_35, 2, x_31);
lean_inc(x_15);
x_36 = l_Lean_Elab_Command_mkNameFromParserSyntax(x_23, x_35, x_15, x_29);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Lean_Elab_Command_expandElab___lambda__1(x_32, x_5, x_21, x_31, x_26, x_6, x_4, x_7, x_18, x_8, x_14, x_9, x_10, x_11, x_37, x_15, x_38);
return x_39;
}
else
{
uint8_t x_40; 
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_40 = !lean_is_exclusive(x_36);
if (x_40 == 0)
{
return x_36;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_36, 0);
x_42 = lean_ctor_get(x_36, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_36);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_23);
x_44 = lean_ctor_get(x_30, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_30, 1);
lean_inc(x_45);
lean_dec(x_30);
x_46 = lean_ctor_get(x_12, 0);
lean_inc(x_46);
lean_dec(x_12);
x_47 = l_Lean_Syntax_getId(x_46);
lean_dec(x_46);
x_48 = l_Lean_Elab_Command_expandElab___lambda__1(x_45, x_5, x_21, x_44, x_26, x_6, x_4, x_7, x_18, x_8, x_14, x_9, x_10, x_11, x_47, x_15, x_29);
return x_48;
}
}
else
{
uint8_t x_49; 
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_49 = !lean_is_exclusive(x_27);
if (x_49 == 0)
{
return x_27;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_27, 0);
x_51 = lean_ctor_get(x_27, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_27);
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
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_53 = !lean_is_exclusive(x_20);
if (x_53 == 0)
{
return x_20;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_20, 0);
x_55 = lean_ctor_get(x_20, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_20);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_expandElab___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabTail");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandElab___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_dec(x_10);
x_14 = lean_unsigned_to_nat(6u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
x_16 = lean_unsigned_to_nat(7u);
x_17 = l_Lean_Syntax_getArg(x_1, x_16);
lean_dec(x_1);
x_18 = l_Lean_Elab_Command_expandElab___lambda__3___closed__1;
lean_inc(x_2);
x_19 = lean_name_mk_string(x_2, x_18);
lean_inc(x_17);
x_20 = l_Lean_Syntax_isOfKind(x_17, x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_21 = lean_box(1);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_13);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_23 = lean_unsigned_to_nat(1u);
x_24 = l_Lean_Syntax_getArg(x_17, x_23);
x_25 = lean_unsigned_to_nat(2u);
x_26 = l_Lean_Syntax_getArg(x_17, x_25);
x_27 = l_Lean_Syntax_isNone(x_26);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = l_Lean_nullKind;
lean_inc(x_26);
x_29 = l_Lean_Syntax_isNodeOf(x_26, x_28, x_25);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_30 = lean_box(1);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_13);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = l_Lean_Syntax_getArg(x_26, x_23);
lean_dec(x_26);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_box(0);
x_35 = l_Lean_Elab_Command_expandElab___lambda__2(x_17, x_15, x_11, x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_34, x_33, x_12, x_13);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_26);
x_36 = lean_box(0);
x_37 = lean_box(0);
x_38 = l_Lean_Elab_Command_expandElab___lambda__2(x_17, x_15, x_11, x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_37, x_36, x_12, x_13);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandElab___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_dec(x_9);
x_13 = lean_unsigned_to_nat(5u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
x_15 = l_Lean_Syntax_isNone(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = l_Lean_nullKind;
x_17 = lean_unsigned_to_nat(1u);
lean_inc(x_14);
x_18 = l_Lean_Syntax_isNodeOf(x_14, x_16, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_19 = lean_box(1);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_12);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_unsigned_to_nat(0u);
x_22 = l_Lean_Syntax_getArg(x_14, x_21);
lean_dec(x_14);
x_23 = l_Lean_Elab_Command_expandElab___lambda__1___closed__4;
lean_inc(x_2);
x_24 = lean_name_mk_string(x_2, x_23);
lean_inc(x_22);
x_25 = l_Lean_Syntax_isOfKind(x_22, x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_26 = lean_box(1);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_12);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_unsigned_to_nat(3u);
x_29 = l_Lean_Syntax_getArg(x_22, x_28);
lean_dec(x_22);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_box(0);
x_32 = l_Lean_Elab_Command_expandElab___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_10, x_31, x_30, x_11, x_12);
return x_32;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_14);
x_33 = lean_box(0);
x_34 = lean_box(0);
x_35 = l_Lean_Elab_Command_expandElab___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_10, x_34, x_33, x_11, x_12);
return x_35;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandElab___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_dec(x_8);
x_12 = lean_unsigned_to_nat(4u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
x_14 = l_Lean_Syntax_isNone(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = l_Lean_nullKind;
x_16 = lean_unsigned_to_nat(1u);
lean_inc(x_13);
x_17 = l_Lean_Syntax_isNodeOf(x_13, x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = lean_box(1);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_11);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_unsigned_to_nat(0u);
x_21 = l_Lean_Syntax_getArg(x_13, x_20);
lean_dec(x_13);
x_22 = l_Lean_Elab_Command_expandElab___lambda__1___closed__2;
lean_inc(x_2);
x_23 = lean_name_mk_string(x_2, x_22);
lean_inc(x_21);
x_24 = l_Lean_Syntax_isOfKind(x_21, x_23);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_25 = lean_box(1);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_11);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_unsigned_to_nat(3u);
x_28 = l_Lean_Syntax_getArg(x_21, x_27);
lean_dec(x_21);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_box(0);
x_31 = l_Lean_Elab_Command_expandElab___lambda__4(x_1, x_2, x_3, x_4, x_5, x_9, x_6, x_7, x_30, x_29, x_10, x_11);
return x_31;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_13);
x_32 = lean_box(0);
x_33 = lean_box(0);
x_34 = l_Lean_Elab_Command_expandElab___lambda__4(x_1, x_2, x_3, x_4, x_5, x_9, x_6, x_7, x_33, x_32, x_10, x_11);
return x_34;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandElab___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_dec(x_4);
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__5;
lean_inc(x_2);
x_11 = lean_name_mk_string(x_2, x_10);
x_12 = l_Lean_Elab_Command_elabElabRules___lambda__6___closed__1;
lean_inc(x_11);
x_13 = lean_name_mk_string(x_11, x_12);
lean_inc(x_9);
x_14 = l_Lean_Syntax_isOfKind(x_9, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_box(1);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_7);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_unsigned_to_nat(3u);
x_18 = l_Lean_Syntax_getArg(x_1, x_17);
x_19 = l_Lean_Syntax_isNone(x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = l_Lean_nullKind;
lean_inc(x_18);
x_21 = l_Lean_Syntax_isNodeOf(x_18, x_20, x_8);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_22 = lean_box(1);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_7);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_24 = lean_unsigned_to_nat(0u);
x_25 = l_Lean_Syntax_getArg(x_18, x_24);
lean_dec(x_18);
x_26 = l_Lean_Elab_Command_expandElab___lambda__1___closed__10;
lean_inc(x_2);
x_27 = lean_name_mk_string(x_2, x_26);
lean_inc(x_25);
x_28 = l_Lean_Syntax_isOfKind(x_25, x_27);
lean_dec(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_25);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_29 = lean_box(1);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_7);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = l_Lean_Syntax_getArg(x_25, x_8);
lean_dec(x_25);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_box(0);
x_34 = l_Lean_Elab_Command_expandElab___lambda__5(x_1, x_3, x_13, x_11, x_9, x_2, x_5, x_33, x_32, x_6, x_7);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_18);
x_35 = lean_box(0);
x_36 = lean_box(0);
x_37 = l_Lean_Elab_Command_expandElab___lambda__5(x_1, x_3, x_13, x_11, x_9, x_2, x_5, x_36, x_35, x_6, x_7);
return x_37;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_expandElab___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elab");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_expandElab___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabElabRules___lambda__7___closed__1;
x_2 = l_Lean_Elab_Command_expandElab___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandElab(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Elab_Command_expandElab___closed__2;
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = l_Lean_Syntax_isNone(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = l_Lean_nullKind;
x_12 = lean_unsigned_to_nat(1u);
lean_inc(x_9);
x_13 = l_Lean_Syntax_isNodeOf(x_9, x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_box(1);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_3);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = l_Lean_Syntax_getArg(x_9, x_8);
lean_dec(x_9);
x_17 = l_Lean_Elab_Command_elabElabRules___lambda__7___closed__4;
lean_inc(x_16);
x_18 = l_Lean_Syntax_isOfKind(x_16, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_16);
lean_dec(x_2);
lean_dec(x_1);
x_19 = lean_box(1);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_3);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_16);
x_22 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__4;
x_23 = l_Lean_Elab_Command_elabElabRules___lambda__7___closed__1;
x_24 = lean_box(0);
x_25 = l_Lean_Elab_Command_expandElab___lambda__6(x_1, x_22, x_23, x_24, x_21, x_2, x_3);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_9);
x_26 = lean_box(0);
x_27 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__4;
x_28 = l_Lean_Elab_Command_elabElabRules___lambda__7___closed__1;
x_29 = lean_box(0);
x_30 = l_Lean_Elab_Command_expandElab___lambda__6(x_1, x_27, x_28, x_29, x_26, x_2, x_3);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Command_expandElab___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_expandElab___spec__1(x_6, x_7, x_3, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandElab___lambda__1___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
size_t x_18; lean_object* x_19; 
x_18 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_19 = l_Lean_Elab_Command_expandElab___lambda__1(x_1, x_2, x_3, x_4, x_18, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_19;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandElab___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("expandElab");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandElab___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__12;
x_2 = l___regBuiltin_Lean_Elab_Command_expandElab___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandElab___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_macroAttribute;
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandElab___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Command_expandElab), 3, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_expandElab(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Command_expandElab___closed__3;
x_3 = l_Lean_Elab_Command_expandElab___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Command_expandElab___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Command_expandElab___closed__4;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandElab_declRange___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(80u);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandElab_declRange___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(94u);
x_2 = lean_unsigned_to_nat(31u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandElab_declRange___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_expandElab_declRange___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___regBuiltin_Lean_Elab_Command_expandElab_declRange___closed__2;
x_4 = lean_unsigned_to_nat(31u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandElab_declRange___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(80u);
x_2 = lean_unsigned_to_nat(4u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandElab_declRange___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(80u);
x_2 = lean_unsigned_to_nat(14u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandElab_declRange___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Command_expandElab_declRange___closed__4;
x_2 = lean_unsigned_to_nat(4u);
x_3 = l___regBuiltin_Lean_Elab_Command_expandElab_declRange___closed__5;
x_4 = lean_unsigned_to_nat(14u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Command_expandElab_declRange___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Command_expandElab_declRange___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Command_expandElab_declRange___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Command_expandElab_declRange(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Command_expandElab___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Command_expandElab_declRange___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_MacroArgUtil(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_AuxDef(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_ElabRules(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_MacroArgUtil(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_AuxDef(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Command_withExpectedType___closed__1 = _init_l_Lean_Elab_Command_withExpectedType___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_withExpectedType___closed__1);
l_Lean_Elab_Command_withExpectedType___closed__2 = _init_l_Lean_Elab_Command_withExpectedType___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_withExpectedType___closed__2);
l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__1 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__1);
l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__2 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__2();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__2);
l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__3 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__3();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__3);
l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__4 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__4();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__4);
l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__5 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__5();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__5);
l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__6 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__6();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__6);
l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__7 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__7();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__7);
l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__8 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__8();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__8);
l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__9 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__9();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__9);
l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__10 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__10();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__10);
l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__11 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__11();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__11);
l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__12 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__12();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__12);
l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__13 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__13();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__13);
l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__14 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__14();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__14);
l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__1 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__1);
l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__2 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__2();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__2);
l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__3 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__3();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__3);
l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__4 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__4();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__4);
l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__5 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__5();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__5);
l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__6 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__6();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__6);
l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__7 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__7();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__7);
l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__8 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__8();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__8);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__1 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__1);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__2 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__2);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__3 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__3);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__4 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__4);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__5 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__5);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__6 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__6();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__6);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__7 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__7();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__7);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__8 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__8();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__8);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__9 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__9();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__9);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__10 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__10();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__10);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__11 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__11();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__11);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__12 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__12();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__12);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__13 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__13();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__13);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__14 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__14();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__14);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__15 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__15();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__15);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__16 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__16();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__16);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__17 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__17();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__17);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__18 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__18();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__18);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__19 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__19();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__19);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__20 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__20();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__20);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__21 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__21();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__21);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__22 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__22();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__22);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__23 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__23();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__23);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__24 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__24();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__24);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__25 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__25();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__25);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__26 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__26();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__26);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__27 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__27();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__27);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__28 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__28();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__28);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__29 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__29();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__29);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__30 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__30();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__30);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__31 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__31();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__31);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__32 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__32();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__32);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__33 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__33();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__33);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__34 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__34();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__34);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__35 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__35();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__35);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__36 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__36();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__36);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__37 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__37();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__37);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__38 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__38();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__38);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__39 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__39();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__39);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__40 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__40();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__40);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__41 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__41();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__41);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__42 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__42();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__42);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__43 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__43();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__43);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__44 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__44();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__44);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__45 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__45();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__45);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__46 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__46();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__46);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__47 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__47();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__47);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__48 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__48();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__48);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__49 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__49();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__49);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__50 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__50();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__50);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__51 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__51();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__51);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__52 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__52();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__52);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__53 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__53();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__53);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__54 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__54();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__54);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__55 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__55();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__55);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__56 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__56();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__56);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__57 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__57();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__57);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__58 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__58();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__58);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__59 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__59();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__59);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__60 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__60();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__60);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__61 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__61();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__61);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__62 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__62();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__62);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__63 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__63();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__63);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__64 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__64();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__64);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__65 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__65();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__65);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__66 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__66();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__66);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__67 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__67();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__67);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__68 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__68();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__68);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__69 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__69();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__69);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__70 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__70();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__70);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__71 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__71();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__71);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__72 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__72();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__72);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__73 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__73();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__73);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__74 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__74();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__74);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__75 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__75();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__75);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__76 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__76();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__76);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__77 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__77();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__77);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__78 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__78();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__78);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__79 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__79();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__79);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__80 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__80();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__80);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__81 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__81();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__81);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__82 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__82();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__82);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__83 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__83();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__83);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__84 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__84();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__84);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__85 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__85();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__85);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__86 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__86();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__86);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__87 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__87();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__87);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__88 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__88();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__88);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__89 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__89();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__89);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__90 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__90();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__90);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__91 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__91();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__91);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__92 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__92();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__92);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__93 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__93();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__93);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__94 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__94();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__94);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__95 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__95();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__95);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__96 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__96();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__96);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__97 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__97();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__97);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__98 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__98();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__98);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__99 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__99();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__99);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__100 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__100();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__100);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__101 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__101();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__101);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__102 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__102();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__102);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__103 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__103();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__103);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__104 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__104();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__104);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__105 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__105();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__105);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__106 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__106();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__106);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__107 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__107();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__107);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__108 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__108();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__108);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__109 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__109();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__109);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__110 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__110();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__110);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__111 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__111();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__111);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__112 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__112();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__112);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__113 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__113();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__113);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__114 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__114();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__114);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__115 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__115();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__115);
l_Lean_Elab_Command_elabElabRulesAux___closed__1 = _init_l_Lean_Elab_Command_elabElabRulesAux___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___closed__1);
l_Lean_Elab_Command_elabElabRulesAux___closed__2 = _init_l_Lean_Elab_Command_elabElabRulesAux___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___closed__2);
l_Lean_Elab_Command_elabElabRules___lambda__3___closed__1 = _init_l_Lean_Elab_Command_elabElabRules___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRules___lambda__3___closed__1);
l_Lean_Elab_Command_elabElabRules___lambda__3___closed__2 = _init_l_Lean_Elab_Command_elabElabRules___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRules___lambda__3___closed__2);
l_Lean_Elab_Command_elabElabRules___lambda__3___closed__3 = _init_l_Lean_Elab_Command_elabElabRules___lambda__3___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRules___lambda__3___closed__3);
l_Lean_Elab_Command_elabElabRules___lambda__3___closed__4 = _init_l_Lean_Elab_Command_elabElabRules___lambda__3___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRules___lambda__3___closed__4);
l_Lean_Elab_Command_elabElabRules___lambda__3___closed__5 = _init_l_Lean_Elab_Command_elabElabRules___lambda__3___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRules___lambda__3___closed__5);
l_Lean_Elab_Command_elabElabRules___lambda__3___closed__6 = _init_l_Lean_Elab_Command_elabElabRules___lambda__3___closed__6();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRules___lambda__3___closed__6);
l_Lean_Elab_Command_elabElabRules___lambda__3___closed__7 = _init_l_Lean_Elab_Command_elabElabRules___lambda__3___closed__7();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRules___lambda__3___closed__7);
l_Lean_Elab_Command_elabElabRules___lambda__6___closed__1 = _init_l_Lean_Elab_Command_elabElabRules___lambda__6___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRules___lambda__6___closed__1);
l_Lean_Elab_Command_elabElabRules___lambda__7___closed__1 = _init_l_Lean_Elab_Command_elabElabRules___lambda__7___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRules___lambda__7___closed__1);
l_Lean_Elab_Command_elabElabRules___lambda__7___closed__2 = _init_l_Lean_Elab_Command_elabElabRules___lambda__7___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRules___lambda__7___closed__2);
l_Lean_Elab_Command_elabElabRules___lambda__7___closed__3 = _init_l_Lean_Elab_Command_elabElabRules___lambda__7___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRules___lambda__7___closed__3);
l_Lean_Elab_Command_elabElabRules___lambda__7___closed__4 = _init_l_Lean_Elab_Command_elabElabRules___lambda__7___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRules___lambda__7___closed__4);
l_Lean_Elab_Command_elabElabRules___closed__1 = _init_l_Lean_Elab_Command_elabElabRules___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRules___closed__1);
l___regBuiltin_Lean_Elab_Command_elabElabRules___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabElabRules___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabElabRules___closed__1);
l___regBuiltin_Lean_Elab_Command_elabElabRules___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabElabRules___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabElabRules___closed__2);
l___regBuiltin_Lean_Elab_Command_elabElabRules___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabElabRules___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabElabRules___closed__3);
l___regBuiltin_Lean_Elab_Command_elabElabRules___closed__4 = _init_l___regBuiltin_Lean_Elab_Command_elabElabRules___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabElabRules___closed__4);
res = l___regBuiltin_Lean_Elab_Command_elabElabRules(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange___closed__1);
l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange___closed__2);
l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange___closed__3);
l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange___closed__4 = _init_l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange___closed__4);
l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange___closed__5 = _init_l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange___closed__5);
l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange___closed__6 = _init_l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange___closed__6);
l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange___closed__7 = _init_l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange___closed__7);
res = l___regBuiltin_Lean_Elab_Command_elabElabRules_declRange(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Command_expandElab___lambda__1___closed__1 = _init_l_Lean_Elab_Command_expandElab___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_expandElab___lambda__1___closed__1);
l_Lean_Elab_Command_expandElab___lambda__1___closed__2 = _init_l_Lean_Elab_Command_expandElab___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_expandElab___lambda__1___closed__2);
l_Lean_Elab_Command_expandElab___lambda__1___closed__3 = _init_l_Lean_Elab_Command_expandElab___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_expandElab___lambda__1___closed__3);
l_Lean_Elab_Command_expandElab___lambda__1___closed__4 = _init_l_Lean_Elab_Command_expandElab___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_expandElab___lambda__1___closed__4);
l_Lean_Elab_Command_expandElab___lambda__1___closed__5 = _init_l_Lean_Elab_Command_expandElab___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_expandElab___lambda__1___closed__5);
l_Lean_Elab_Command_expandElab___lambda__1___closed__6 = _init_l_Lean_Elab_Command_expandElab___lambda__1___closed__6();
lean_mark_persistent(l_Lean_Elab_Command_expandElab___lambda__1___closed__6);
l_Lean_Elab_Command_expandElab___lambda__1___closed__7 = _init_l_Lean_Elab_Command_expandElab___lambda__1___closed__7();
lean_mark_persistent(l_Lean_Elab_Command_expandElab___lambda__1___closed__7);
l_Lean_Elab_Command_expandElab___lambda__1___closed__8 = _init_l_Lean_Elab_Command_expandElab___lambda__1___closed__8();
lean_mark_persistent(l_Lean_Elab_Command_expandElab___lambda__1___closed__8);
l_Lean_Elab_Command_expandElab___lambda__1___closed__9 = _init_l_Lean_Elab_Command_expandElab___lambda__1___closed__9();
lean_mark_persistent(l_Lean_Elab_Command_expandElab___lambda__1___closed__9);
l_Lean_Elab_Command_expandElab___lambda__1___closed__10 = _init_l_Lean_Elab_Command_expandElab___lambda__1___closed__10();
lean_mark_persistent(l_Lean_Elab_Command_expandElab___lambda__1___closed__10);
l_Lean_Elab_Command_expandElab___lambda__3___closed__1 = _init_l_Lean_Elab_Command_expandElab___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_expandElab___lambda__3___closed__1);
l_Lean_Elab_Command_expandElab___closed__1 = _init_l_Lean_Elab_Command_expandElab___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_expandElab___closed__1);
l_Lean_Elab_Command_expandElab___closed__2 = _init_l_Lean_Elab_Command_expandElab___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_expandElab___closed__2);
l___regBuiltin_Lean_Elab_Command_expandElab___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_expandElab___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandElab___closed__1);
l___regBuiltin_Lean_Elab_Command_expandElab___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_expandElab___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandElab___closed__2);
l___regBuiltin_Lean_Elab_Command_expandElab___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_expandElab___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandElab___closed__3);
l___regBuiltin_Lean_Elab_Command_expandElab___closed__4 = _init_l___regBuiltin_Lean_Elab_Command_expandElab___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandElab___closed__4);
res = l___regBuiltin_Lean_Elab_Command_expandElab(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Command_expandElab_declRange___closed__1 = _init_l___regBuiltin_Lean_Elab_Command_expandElab_declRange___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandElab_declRange___closed__1);
l___regBuiltin_Lean_Elab_Command_expandElab_declRange___closed__2 = _init_l___regBuiltin_Lean_Elab_Command_expandElab_declRange___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandElab_declRange___closed__2);
l___regBuiltin_Lean_Elab_Command_expandElab_declRange___closed__3 = _init_l___regBuiltin_Lean_Elab_Command_expandElab_declRange___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandElab_declRange___closed__3);
l___regBuiltin_Lean_Elab_Command_expandElab_declRange___closed__4 = _init_l___regBuiltin_Lean_Elab_Command_expandElab_declRange___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandElab_declRange___closed__4);
l___regBuiltin_Lean_Elab_Command_expandElab_declRange___closed__5 = _init_l___regBuiltin_Lean_Elab_Command_expandElab_declRange___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandElab_declRange___closed__5);
l___regBuiltin_Lean_Elab_Command_expandElab_declRange___closed__6 = _init_l___regBuiltin_Lean_Elab_Command_expandElab_declRange___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandElab_declRange___closed__6);
l___regBuiltin_Lean_Elab_Command_expandElab_declRange___closed__7 = _init_l___regBuiltin_Lean_Elab_Command_expandElab_declRange___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Command_expandElab_declRange___closed__7);
res = l___regBuiltin_Lean_Elab_Command_expandElab_declRange(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
