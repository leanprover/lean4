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
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__116;
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
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Command_expandElab___closed__4;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__4;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__65;
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__109;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_expandElab___lambda__1___boxed(lean_object**);
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__118;
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
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__119;
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
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__120;
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
static lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__117;
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
x_1 = lean_mk_string("attrKind");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__6;
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__20;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__22() {
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
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__23;
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__22;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__21;
x_3 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__24;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__26() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Attr");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__4;
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__26;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__28() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("simple");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__27;
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__28;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__5;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__30;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__32;
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__25;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__34() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("]");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__35() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__36() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabRules");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__37() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__36;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__38() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__36;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__37;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__39() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__36;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__40() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(":");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__41() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Elab.Tactic.Tactic");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__42() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__41;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__43() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__41;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__42;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__44() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Tactic");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__45() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__10;
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__44;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__46() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__45;
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__44;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__47() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__46;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__48() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__47;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__49() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(":=");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__50() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("fun");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__51() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__6;
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__50;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__52() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("matchAlts");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__53() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__6;
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__52;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__54() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("hole");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__55() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__6;
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__54;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__56() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__57() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("throwUnsupportedSyntax");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__58() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__57;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__59() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__57;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__58;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__60() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__57;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__61() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__10;
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__57;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__62() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__61;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__63() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__62;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__64() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__65() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__4;
x_2 = l_Array_append___rarg(x_1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__66() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__3;
x_3 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__65;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__67() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__64;
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__66;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__68() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("commandElab");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__69() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__68;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__70() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__68;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__69;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__71() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__68;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__72() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Elab.Command.CommandElab");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__73() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__72;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__74() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__72;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__73;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__75() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("CommandElab");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__76() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__12;
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__75;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__77() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__76;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__78() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__77;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__79() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("termElab");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__80() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__79;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__81() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__79;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__80;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__82() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__79;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__83() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Elab.Term.TermElab");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__84() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__83;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__85() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__83;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__84;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__86() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__10;
x_2 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__87() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("TermElab");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__88() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__86;
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__87;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__89() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__88;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__90() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__89;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__91() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("basicFun");
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
lean_object* x_1; 
x_1 = lean_mk_string("stx");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__94() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__93;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__95() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__93;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__94;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__96() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__93;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__97() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("match");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__98() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__6;
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__97;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__99() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("matchDiscr");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__100() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__6;
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__99;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__101() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__32;
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__22;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__102() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("with");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__103() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(6u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__104() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("syntax category '");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__105() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__104;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__106() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' does not support expected type specification");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__107() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__106;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__108() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("expectedType?");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__109() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__108;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__110() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__108;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__109;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__111() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__108;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__112() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("app");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__113() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__6;
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__112;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__114() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Elab.Command.withExpectedType");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__115() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__114;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__116() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__114;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__115;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__117() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("withExpectedType");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__118() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__12;
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__117;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__119() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__118;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__120() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__119;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRulesAux___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__2;
x_10 = lean_name_eq(x_5, x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__4;
x_12 = lean_name_eq(x_5, x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__6;
x_14 = lean_name_eq(x_5, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_15, 0, x_5);
x_16 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__8;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__11;
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_throwError___at_Lean_Elab_Command_elabCommand___spec__12(x_19, x_6, x_7, x_8);
lean_dec(x_7);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
lean_dec(x_5);
lean_inc(x_2);
x_21 = l_Lean_mkIdentFromRef___at_Lean_Elab_Command_elabElabRulesAux___spec__3(x_2, x_6, x_7, x_8);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Command_elabAuxDef___spec__4(x_6, x_7, x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_Elab_Command_getCurrMacroScope(x_6, x_7, x_26);
lean_dec(x_6);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Elab_Command_getMainModule___rarg(x_7, x_29);
lean_dec(x_7);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__17;
lean_inc(x_25);
x_34 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_34, 0, x_25);
lean_ctor_set(x_34, 1, x_33);
lean_inc(x_28);
lean_inc(x_32);
x_35 = l_Lean_addMacroScope(x_32, x_13, x_28);
x_36 = lean_box(0);
x_37 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__31;
lean_inc(x_25);
x_38 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_38, 0, x_25);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set(x_38, 2, x_35);
lean_ctor_set(x_38, 3, x_36);
x_39 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__23;
x_40 = lean_array_push(x_39, x_22);
x_41 = lean_box(2);
x_42 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__3;
x_43 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_43, 2, x_40);
x_44 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__32;
x_45 = lean_array_push(x_44, x_38);
x_46 = lean_array_push(x_45, x_43);
x_47 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__29;
x_48 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_48, 0, x_41);
lean_ctor_set(x_48, 1, x_47);
lean_ctor_set(x_48, 2, x_46);
x_49 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__33;
x_50 = lean_array_push(x_49, x_48);
x_51 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__19;
x_52 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_52, 0, x_41);
lean_ctor_set(x_52, 1, x_51);
lean_ctor_set(x_52, 2, x_50);
x_53 = lean_array_push(x_39, x_52);
x_54 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_54, 0, x_41);
lean_ctor_set(x_54, 1, x_42);
lean_ctor_set(x_54, 2, x_53);
x_55 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__34;
lean_inc(x_25);
x_56 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_56, 0, x_25);
lean_ctor_set(x_56, 1, x_55);
x_57 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__35;
x_58 = lean_array_push(x_57, x_34);
x_59 = lean_array_push(x_58, x_54);
x_60 = lean_array_push(x_59, x_56);
x_61 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__16;
x_62 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_62, 0, x_41);
lean_ctor_set(x_62, 1, x_61);
lean_ctor_set(x_62, 2, x_60);
x_63 = lean_array_push(x_39, x_62);
x_64 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_64, 0, x_41);
lean_ctor_set(x_64, 1, x_42);
lean_ctor_set(x_64, 2, x_63);
x_65 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__13;
lean_inc(x_25);
x_66 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_66, 0, x_25);
lean_ctor_set(x_66, 1, x_65);
x_67 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__39;
lean_inc(x_28);
lean_inc(x_32);
x_68 = l_Lean_addMacroScope(x_32, x_67, x_28);
x_69 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__38;
lean_inc(x_25);
x_70 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_70, 0, x_25);
lean_ctor_set(x_70, 1, x_69);
lean_ctor_set(x_70, 2, x_68);
lean_ctor_set(x_70, 3, x_36);
x_71 = lean_mk_syntax_ident(x_2);
x_72 = lean_array_push(x_44, x_70);
x_73 = lean_array_push(x_72, x_71);
x_74 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_74, 0, x_41);
lean_ctor_set(x_74, 1, x_42);
lean_ctor_set(x_74, 2, x_73);
x_75 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__40;
lean_inc(x_25);
x_76 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_76, 0, x_25);
lean_ctor_set(x_76, 1, x_75);
x_77 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__46;
lean_inc(x_28);
lean_inc(x_32);
x_78 = l_Lean_addMacroScope(x_32, x_77, x_28);
x_79 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__43;
x_80 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__48;
lean_inc(x_25);
x_81 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_81, 0, x_25);
lean_ctor_set(x_81, 1, x_79);
lean_ctor_set(x_81, 2, x_78);
lean_ctor_set(x_81, 3, x_80);
x_82 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__49;
lean_inc(x_25);
x_83 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_83, 0, x_25);
lean_ctor_set(x_83, 1, x_82);
x_84 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__50;
lean_inc(x_25);
x_85 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_85, 0, x_25);
lean_ctor_set(x_85, 1, x_84);
x_86 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__4;
x_87 = l_Array_append___rarg(x_86, x_3);
x_88 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__1;
lean_inc(x_25);
x_89 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_89, 0, x_25);
lean_ctor_set(x_89, 1, x_88);
x_90 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__56;
lean_inc(x_25);
x_91 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_91, 0, x_25);
lean_ctor_set(x_91, 1, x_90);
x_92 = lean_array_push(x_39, x_91);
x_93 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__55;
x_94 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_94, 0, x_41);
lean_ctor_set(x_94, 1, x_93);
lean_ctor_set(x_94, 2, x_92);
x_95 = lean_array_push(x_39, x_94);
x_96 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_96, 0, x_41);
lean_ctor_set(x_96, 1, x_42);
lean_ctor_set(x_96, 2, x_95);
x_97 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__6;
lean_inc(x_25);
x_98 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_98, 0, x_25);
lean_ctor_set(x_98, 1, x_97);
x_99 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__60;
x_100 = l_Lean_addMacroScope(x_32, x_99, x_28);
x_101 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__59;
x_102 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__63;
x_103 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_103, 0, x_25);
lean_ctor_set(x_103, 1, x_101);
lean_ctor_set(x_103, 2, x_100);
lean_ctor_set(x_103, 3, x_102);
x_104 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__7;
x_105 = lean_array_push(x_104, x_89);
x_106 = lean_array_push(x_105, x_96);
x_107 = lean_array_push(x_106, x_98);
x_108 = lean_array_push(x_107, x_103);
x_109 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__8;
x_110 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_110, 0, x_41);
lean_ctor_set(x_110, 1, x_109);
lean_ctor_set(x_110, 2, x_108);
x_111 = lean_array_push(x_87, x_110);
x_112 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_112, 0, x_41);
lean_ctor_set(x_112, 1, x_42);
lean_ctor_set(x_112, 2, x_111);
x_113 = lean_array_push(x_39, x_112);
x_114 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__53;
x_115 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_115, 0, x_41);
lean_ctor_set(x_115, 1, x_114);
lean_ctor_set(x_115, 2, x_113);
x_116 = lean_array_push(x_44, x_85);
x_117 = lean_array_push(x_116, x_115);
x_118 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__51;
x_119 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_119, 0, x_41);
lean_ctor_set(x_119, 1, x_118);
lean_ctor_set(x_119, 2, x_117);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_120 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__67;
x_121 = lean_array_push(x_120, x_64);
x_122 = lean_array_push(x_121, x_66);
x_123 = lean_array_push(x_122, x_74);
x_124 = lean_array_push(x_123, x_76);
x_125 = lean_array_push(x_124, x_81);
x_126 = lean_array_push(x_125, x_83);
x_127 = lean_array_push(x_126, x_119);
x_128 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__14;
x_129 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_129, 0, x_41);
lean_ctor_set(x_129, 1, x_128);
lean_ctor_set(x_129, 2, x_127);
lean_ctor_set(x_30, 0, x_129);
return x_30;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_130 = lean_ctor_get(x_4, 0);
lean_inc(x_130);
lean_dec(x_4);
x_131 = lean_array_push(x_39, x_130);
x_132 = l_Array_append___rarg(x_86, x_131);
x_133 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_133, 0, x_41);
lean_ctor_set(x_133, 1, x_42);
lean_ctor_set(x_133, 2, x_132);
x_134 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__64;
x_135 = lean_array_push(x_134, x_133);
x_136 = lean_array_push(x_135, x_64);
x_137 = lean_array_push(x_136, x_66);
x_138 = lean_array_push(x_137, x_74);
x_139 = lean_array_push(x_138, x_76);
x_140 = lean_array_push(x_139, x_81);
x_141 = lean_array_push(x_140, x_83);
x_142 = lean_array_push(x_141, x_119);
x_143 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__14;
x_144 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_144, 0, x_41);
lean_ctor_set(x_144, 1, x_143);
lean_ctor_set(x_144, 2, x_142);
lean_ctor_set(x_30, 0, x_144);
return x_30;
}
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_145 = lean_ctor_get(x_30, 0);
x_146 = lean_ctor_get(x_30, 1);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_30);
x_147 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__17;
lean_inc(x_25);
x_148 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_148, 0, x_25);
lean_ctor_set(x_148, 1, x_147);
lean_inc(x_28);
lean_inc(x_145);
x_149 = l_Lean_addMacroScope(x_145, x_13, x_28);
x_150 = lean_box(0);
x_151 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__31;
lean_inc(x_25);
x_152 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_152, 0, x_25);
lean_ctor_set(x_152, 1, x_151);
lean_ctor_set(x_152, 2, x_149);
lean_ctor_set(x_152, 3, x_150);
x_153 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__23;
x_154 = lean_array_push(x_153, x_22);
x_155 = lean_box(2);
x_156 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__3;
x_157 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set(x_157, 1, x_156);
lean_ctor_set(x_157, 2, x_154);
x_158 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__32;
x_159 = lean_array_push(x_158, x_152);
x_160 = lean_array_push(x_159, x_157);
x_161 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__29;
x_162 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_162, 0, x_155);
lean_ctor_set(x_162, 1, x_161);
lean_ctor_set(x_162, 2, x_160);
x_163 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__33;
x_164 = lean_array_push(x_163, x_162);
x_165 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__19;
x_166 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_166, 0, x_155);
lean_ctor_set(x_166, 1, x_165);
lean_ctor_set(x_166, 2, x_164);
x_167 = lean_array_push(x_153, x_166);
x_168 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_168, 0, x_155);
lean_ctor_set(x_168, 1, x_156);
lean_ctor_set(x_168, 2, x_167);
x_169 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__34;
lean_inc(x_25);
x_170 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_170, 0, x_25);
lean_ctor_set(x_170, 1, x_169);
x_171 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__35;
x_172 = lean_array_push(x_171, x_148);
x_173 = lean_array_push(x_172, x_168);
x_174 = lean_array_push(x_173, x_170);
x_175 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__16;
x_176 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_176, 0, x_155);
lean_ctor_set(x_176, 1, x_175);
lean_ctor_set(x_176, 2, x_174);
x_177 = lean_array_push(x_153, x_176);
x_178 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_178, 0, x_155);
lean_ctor_set(x_178, 1, x_156);
lean_ctor_set(x_178, 2, x_177);
x_179 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__13;
lean_inc(x_25);
x_180 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_180, 0, x_25);
lean_ctor_set(x_180, 1, x_179);
x_181 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__39;
lean_inc(x_28);
lean_inc(x_145);
x_182 = l_Lean_addMacroScope(x_145, x_181, x_28);
x_183 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__38;
lean_inc(x_25);
x_184 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_184, 0, x_25);
lean_ctor_set(x_184, 1, x_183);
lean_ctor_set(x_184, 2, x_182);
lean_ctor_set(x_184, 3, x_150);
x_185 = lean_mk_syntax_ident(x_2);
x_186 = lean_array_push(x_158, x_184);
x_187 = lean_array_push(x_186, x_185);
x_188 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_188, 0, x_155);
lean_ctor_set(x_188, 1, x_156);
lean_ctor_set(x_188, 2, x_187);
x_189 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__40;
lean_inc(x_25);
x_190 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_190, 0, x_25);
lean_ctor_set(x_190, 1, x_189);
x_191 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__46;
lean_inc(x_28);
lean_inc(x_145);
x_192 = l_Lean_addMacroScope(x_145, x_191, x_28);
x_193 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__43;
x_194 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__48;
lean_inc(x_25);
x_195 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_195, 0, x_25);
lean_ctor_set(x_195, 1, x_193);
lean_ctor_set(x_195, 2, x_192);
lean_ctor_set(x_195, 3, x_194);
x_196 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__49;
lean_inc(x_25);
x_197 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_197, 0, x_25);
lean_ctor_set(x_197, 1, x_196);
x_198 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__50;
lean_inc(x_25);
x_199 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_199, 0, x_25);
lean_ctor_set(x_199, 1, x_198);
x_200 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__4;
x_201 = l_Array_append___rarg(x_200, x_3);
x_202 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__1;
lean_inc(x_25);
x_203 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_203, 0, x_25);
lean_ctor_set(x_203, 1, x_202);
x_204 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__56;
lean_inc(x_25);
x_205 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_205, 0, x_25);
lean_ctor_set(x_205, 1, x_204);
x_206 = lean_array_push(x_153, x_205);
x_207 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__55;
x_208 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_208, 0, x_155);
lean_ctor_set(x_208, 1, x_207);
lean_ctor_set(x_208, 2, x_206);
x_209 = lean_array_push(x_153, x_208);
x_210 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_210, 0, x_155);
lean_ctor_set(x_210, 1, x_156);
lean_ctor_set(x_210, 2, x_209);
x_211 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__6;
lean_inc(x_25);
x_212 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_212, 0, x_25);
lean_ctor_set(x_212, 1, x_211);
x_213 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__60;
x_214 = l_Lean_addMacroScope(x_145, x_213, x_28);
x_215 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__59;
x_216 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__63;
x_217 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_217, 0, x_25);
lean_ctor_set(x_217, 1, x_215);
lean_ctor_set(x_217, 2, x_214);
lean_ctor_set(x_217, 3, x_216);
x_218 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__7;
x_219 = lean_array_push(x_218, x_203);
x_220 = lean_array_push(x_219, x_210);
x_221 = lean_array_push(x_220, x_212);
x_222 = lean_array_push(x_221, x_217);
x_223 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__8;
x_224 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_224, 0, x_155);
lean_ctor_set(x_224, 1, x_223);
lean_ctor_set(x_224, 2, x_222);
x_225 = lean_array_push(x_201, x_224);
x_226 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_226, 0, x_155);
lean_ctor_set(x_226, 1, x_156);
lean_ctor_set(x_226, 2, x_225);
x_227 = lean_array_push(x_153, x_226);
x_228 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__53;
x_229 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_229, 0, x_155);
lean_ctor_set(x_229, 1, x_228);
lean_ctor_set(x_229, 2, x_227);
x_230 = lean_array_push(x_158, x_199);
x_231 = lean_array_push(x_230, x_229);
x_232 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__51;
x_233 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_233, 0, x_155);
lean_ctor_set(x_233, 1, x_232);
lean_ctor_set(x_233, 2, x_231);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_234 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__67;
x_235 = lean_array_push(x_234, x_178);
x_236 = lean_array_push(x_235, x_180);
x_237 = lean_array_push(x_236, x_188);
x_238 = lean_array_push(x_237, x_190);
x_239 = lean_array_push(x_238, x_195);
x_240 = lean_array_push(x_239, x_197);
x_241 = lean_array_push(x_240, x_233);
x_242 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__14;
x_243 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_243, 0, x_155);
lean_ctor_set(x_243, 1, x_242);
lean_ctor_set(x_243, 2, x_241);
x_244 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_244, 0, x_243);
lean_ctor_set(x_244, 1, x_146);
return x_244;
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_245 = lean_ctor_get(x_4, 0);
lean_inc(x_245);
lean_dec(x_4);
x_246 = lean_array_push(x_153, x_245);
x_247 = l_Array_append___rarg(x_200, x_246);
x_248 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_248, 0, x_155);
lean_ctor_set(x_248, 1, x_156);
lean_ctor_set(x_248, 2, x_247);
x_249 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__64;
x_250 = lean_array_push(x_249, x_248);
x_251 = lean_array_push(x_250, x_178);
x_252 = lean_array_push(x_251, x_180);
x_253 = lean_array_push(x_252, x_188);
x_254 = lean_array_push(x_253, x_190);
x_255 = lean_array_push(x_254, x_195);
x_256 = lean_array_push(x_255, x_197);
x_257 = lean_array_push(x_256, x_233);
x_258 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__14;
x_259 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_259, 0, x_155);
lean_ctor_set(x_259, 1, x_258);
lean_ctor_set(x_259, 2, x_257);
x_260 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_260, 0, x_259);
lean_ctor_set(x_260, 1, x_146);
return x_260;
}
}
}
}
else
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; uint8_t x_271; 
lean_dec(x_5);
lean_inc(x_2);
x_261 = l_Lean_mkIdentFromRef___at_Lean_Elab_Command_elabElabRulesAux___spec__3(x_2, x_6, x_7, x_8);
x_262 = lean_ctor_get(x_261, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_261, 1);
lean_inc(x_263);
lean_dec(x_261);
x_264 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Command_elabAuxDef___spec__4(x_6, x_7, x_263);
x_265 = lean_ctor_get(x_264, 0);
lean_inc(x_265);
x_266 = lean_ctor_get(x_264, 1);
lean_inc(x_266);
lean_dec(x_264);
x_267 = l_Lean_Elab_Command_getCurrMacroScope(x_6, x_7, x_266);
lean_dec(x_6);
x_268 = lean_ctor_get(x_267, 0);
lean_inc(x_268);
x_269 = lean_ctor_get(x_267, 1);
lean_inc(x_269);
lean_dec(x_267);
x_270 = l_Lean_Elab_Command_getMainModule___rarg(x_7, x_269);
lean_dec(x_7);
x_271 = !lean_is_exclusive(x_270);
if (x_271 == 0)
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; 
x_272 = lean_ctor_get(x_270, 0);
x_273 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__17;
lean_inc(x_265);
x_274 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_274, 0, x_265);
lean_ctor_set(x_274, 1, x_273);
x_275 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__71;
lean_inc(x_268);
lean_inc(x_272);
x_276 = l_Lean_addMacroScope(x_272, x_275, x_268);
x_277 = lean_box(0);
x_278 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__70;
lean_inc(x_265);
x_279 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_279, 0, x_265);
lean_ctor_set(x_279, 1, x_278);
lean_ctor_set(x_279, 2, x_276);
lean_ctor_set(x_279, 3, x_277);
x_280 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__23;
x_281 = lean_array_push(x_280, x_262);
x_282 = lean_box(2);
x_283 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__3;
x_284 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_284, 0, x_282);
lean_ctor_set(x_284, 1, x_283);
lean_ctor_set(x_284, 2, x_281);
x_285 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__32;
x_286 = lean_array_push(x_285, x_279);
x_287 = lean_array_push(x_286, x_284);
x_288 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__29;
x_289 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_289, 0, x_282);
lean_ctor_set(x_289, 1, x_288);
lean_ctor_set(x_289, 2, x_287);
x_290 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__33;
x_291 = lean_array_push(x_290, x_289);
x_292 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__19;
x_293 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_293, 0, x_282);
lean_ctor_set(x_293, 1, x_292);
lean_ctor_set(x_293, 2, x_291);
x_294 = lean_array_push(x_280, x_293);
x_295 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_295, 0, x_282);
lean_ctor_set(x_295, 1, x_283);
lean_ctor_set(x_295, 2, x_294);
x_296 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__34;
lean_inc(x_265);
x_297 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_297, 0, x_265);
lean_ctor_set(x_297, 1, x_296);
x_298 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__35;
x_299 = lean_array_push(x_298, x_274);
x_300 = lean_array_push(x_299, x_295);
x_301 = lean_array_push(x_300, x_297);
x_302 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__16;
x_303 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_303, 0, x_282);
lean_ctor_set(x_303, 1, x_302);
lean_ctor_set(x_303, 2, x_301);
x_304 = lean_array_push(x_280, x_303);
x_305 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_305, 0, x_282);
lean_ctor_set(x_305, 1, x_283);
lean_ctor_set(x_305, 2, x_304);
x_306 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__13;
lean_inc(x_265);
x_307 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_307, 0, x_265);
lean_ctor_set(x_307, 1, x_306);
x_308 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__39;
lean_inc(x_268);
lean_inc(x_272);
x_309 = l_Lean_addMacroScope(x_272, x_308, x_268);
x_310 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__38;
lean_inc(x_265);
x_311 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_311, 0, x_265);
lean_ctor_set(x_311, 1, x_310);
lean_ctor_set(x_311, 2, x_309);
lean_ctor_set(x_311, 3, x_277);
x_312 = lean_mk_syntax_ident(x_2);
x_313 = lean_array_push(x_285, x_311);
x_314 = lean_array_push(x_313, x_312);
x_315 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_315, 0, x_282);
lean_ctor_set(x_315, 1, x_283);
lean_ctor_set(x_315, 2, x_314);
x_316 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__40;
lean_inc(x_265);
x_317 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_317, 0, x_265);
lean_ctor_set(x_317, 1, x_316);
x_318 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__76;
lean_inc(x_268);
lean_inc(x_272);
x_319 = l_Lean_addMacroScope(x_272, x_318, x_268);
x_320 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__74;
x_321 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__78;
lean_inc(x_265);
x_322 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_322, 0, x_265);
lean_ctor_set(x_322, 1, x_320);
lean_ctor_set(x_322, 2, x_319);
lean_ctor_set(x_322, 3, x_321);
x_323 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__49;
lean_inc(x_265);
x_324 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_324, 0, x_265);
lean_ctor_set(x_324, 1, x_323);
x_325 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__50;
lean_inc(x_265);
x_326 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_326, 0, x_265);
lean_ctor_set(x_326, 1, x_325);
x_327 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__4;
x_328 = l_Array_append___rarg(x_327, x_3);
x_329 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__1;
lean_inc(x_265);
x_330 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_330, 0, x_265);
lean_ctor_set(x_330, 1, x_329);
x_331 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__56;
lean_inc(x_265);
x_332 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_332, 0, x_265);
lean_ctor_set(x_332, 1, x_331);
x_333 = lean_array_push(x_280, x_332);
x_334 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__55;
x_335 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_335, 0, x_282);
lean_ctor_set(x_335, 1, x_334);
lean_ctor_set(x_335, 2, x_333);
x_336 = lean_array_push(x_280, x_335);
x_337 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_337, 0, x_282);
lean_ctor_set(x_337, 1, x_283);
lean_ctor_set(x_337, 2, x_336);
x_338 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__6;
lean_inc(x_265);
x_339 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_339, 0, x_265);
lean_ctor_set(x_339, 1, x_338);
x_340 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__60;
x_341 = l_Lean_addMacroScope(x_272, x_340, x_268);
x_342 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__59;
x_343 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__63;
x_344 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_344, 0, x_265);
lean_ctor_set(x_344, 1, x_342);
lean_ctor_set(x_344, 2, x_341);
lean_ctor_set(x_344, 3, x_343);
x_345 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__7;
x_346 = lean_array_push(x_345, x_330);
x_347 = lean_array_push(x_346, x_337);
x_348 = lean_array_push(x_347, x_339);
x_349 = lean_array_push(x_348, x_344);
x_350 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__8;
x_351 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_351, 0, x_282);
lean_ctor_set(x_351, 1, x_350);
lean_ctor_set(x_351, 2, x_349);
x_352 = lean_array_push(x_328, x_351);
x_353 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_353, 0, x_282);
lean_ctor_set(x_353, 1, x_283);
lean_ctor_set(x_353, 2, x_352);
x_354 = lean_array_push(x_280, x_353);
x_355 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__53;
x_356 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_356, 0, x_282);
lean_ctor_set(x_356, 1, x_355);
lean_ctor_set(x_356, 2, x_354);
x_357 = lean_array_push(x_285, x_326);
x_358 = lean_array_push(x_357, x_356);
x_359 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__51;
x_360 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_360, 0, x_282);
lean_ctor_set(x_360, 1, x_359);
lean_ctor_set(x_360, 2, x_358);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; 
x_361 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__67;
x_362 = lean_array_push(x_361, x_305);
x_363 = lean_array_push(x_362, x_307);
x_364 = lean_array_push(x_363, x_315);
x_365 = lean_array_push(x_364, x_317);
x_366 = lean_array_push(x_365, x_322);
x_367 = lean_array_push(x_366, x_324);
x_368 = lean_array_push(x_367, x_360);
x_369 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__14;
x_370 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_370, 0, x_282);
lean_ctor_set(x_370, 1, x_369);
lean_ctor_set(x_370, 2, x_368);
lean_ctor_set(x_270, 0, x_370);
return x_270;
}
else
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; 
x_371 = lean_ctor_get(x_4, 0);
lean_inc(x_371);
lean_dec(x_4);
x_372 = lean_array_push(x_280, x_371);
x_373 = l_Array_append___rarg(x_327, x_372);
x_374 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_374, 0, x_282);
lean_ctor_set(x_374, 1, x_283);
lean_ctor_set(x_374, 2, x_373);
x_375 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__64;
x_376 = lean_array_push(x_375, x_374);
x_377 = lean_array_push(x_376, x_305);
x_378 = lean_array_push(x_377, x_307);
x_379 = lean_array_push(x_378, x_315);
x_380 = lean_array_push(x_379, x_317);
x_381 = lean_array_push(x_380, x_322);
x_382 = lean_array_push(x_381, x_324);
x_383 = lean_array_push(x_382, x_360);
x_384 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__14;
x_385 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_385, 0, x_282);
lean_ctor_set(x_385, 1, x_384);
lean_ctor_set(x_385, 2, x_383);
lean_ctor_set(x_270, 0, x_385);
return x_270;
}
}
else
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; 
x_386 = lean_ctor_get(x_270, 0);
x_387 = lean_ctor_get(x_270, 1);
lean_inc(x_387);
lean_inc(x_386);
lean_dec(x_270);
x_388 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__17;
lean_inc(x_265);
x_389 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_389, 0, x_265);
lean_ctor_set(x_389, 1, x_388);
x_390 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__71;
lean_inc(x_268);
lean_inc(x_386);
x_391 = l_Lean_addMacroScope(x_386, x_390, x_268);
x_392 = lean_box(0);
x_393 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__70;
lean_inc(x_265);
x_394 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_394, 0, x_265);
lean_ctor_set(x_394, 1, x_393);
lean_ctor_set(x_394, 2, x_391);
lean_ctor_set(x_394, 3, x_392);
x_395 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__23;
x_396 = lean_array_push(x_395, x_262);
x_397 = lean_box(2);
x_398 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__3;
x_399 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_399, 0, x_397);
lean_ctor_set(x_399, 1, x_398);
lean_ctor_set(x_399, 2, x_396);
x_400 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__32;
x_401 = lean_array_push(x_400, x_394);
x_402 = lean_array_push(x_401, x_399);
x_403 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__29;
x_404 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_404, 0, x_397);
lean_ctor_set(x_404, 1, x_403);
lean_ctor_set(x_404, 2, x_402);
x_405 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__33;
x_406 = lean_array_push(x_405, x_404);
x_407 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__19;
x_408 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_408, 0, x_397);
lean_ctor_set(x_408, 1, x_407);
lean_ctor_set(x_408, 2, x_406);
x_409 = lean_array_push(x_395, x_408);
x_410 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_410, 0, x_397);
lean_ctor_set(x_410, 1, x_398);
lean_ctor_set(x_410, 2, x_409);
x_411 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__34;
lean_inc(x_265);
x_412 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_412, 0, x_265);
lean_ctor_set(x_412, 1, x_411);
x_413 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__35;
x_414 = lean_array_push(x_413, x_389);
x_415 = lean_array_push(x_414, x_410);
x_416 = lean_array_push(x_415, x_412);
x_417 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__16;
x_418 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_418, 0, x_397);
lean_ctor_set(x_418, 1, x_417);
lean_ctor_set(x_418, 2, x_416);
x_419 = lean_array_push(x_395, x_418);
x_420 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_420, 0, x_397);
lean_ctor_set(x_420, 1, x_398);
lean_ctor_set(x_420, 2, x_419);
x_421 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__13;
lean_inc(x_265);
x_422 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_422, 0, x_265);
lean_ctor_set(x_422, 1, x_421);
x_423 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__39;
lean_inc(x_268);
lean_inc(x_386);
x_424 = l_Lean_addMacroScope(x_386, x_423, x_268);
x_425 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__38;
lean_inc(x_265);
x_426 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_426, 0, x_265);
lean_ctor_set(x_426, 1, x_425);
lean_ctor_set(x_426, 2, x_424);
lean_ctor_set(x_426, 3, x_392);
x_427 = lean_mk_syntax_ident(x_2);
x_428 = lean_array_push(x_400, x_426);
x_429 = lean_array_push(x_428, x_427);
x_430 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_430, 0, x_397);
lean_ctor_set(x_430, 1, x_398);
lean_ctor_set(x_430, 2, x_429);
x_431 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__40;
lean_inc(x_265);
x_432 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_432, 0, x_265);
lean_ctor_set(x_432, 1, x_431);
x_433 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__76;
lean_inc(x_268);
lean_inc(x_386);
x_434 = l_Lean_addMacroScope(x_386, x_433, x_268);
x_435 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__74;
x_436 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__78;
lean_inc(x_265);
x_437 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_437, 0, x_265);
lean_ctor_set(x_437, 1, x_435);
lean_ctor_set(x_437, 2, x_434);
lean_ctor_set(x_437, 3, x_436);
x_438 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__49;
lean_inc(x_265);
x_439 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_439, 0, x_265);
lean_ctor_set(x_439, 1, x_438);
x_440 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__50;
lean_inc(x_265);
x_441 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_441, 0, x_265);
lean_ctor_set(x_441, 1, x_440);
x_442 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__4;
x_443 = l_Array_append___rarg(x_442, x_3);
x_444 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__1;
lean_inc(x_265);
x_445 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_445, 0, x_265);
lean_ctor_set(x_445, 1, x_444);
x_446 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__56;
lean_inc(x_265);
x_447 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_447, 0, x_265);
lean_ctor_set(x_447, 1, x_446);
x_448 = lean_array_push(x_395, x_447);
x_449 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__55;
x_450 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_450, 0, x_397);
lean_ctor_set(x_450, 1, x_449);
lean_ctor_set(x_450, 2, x_448);
x_451 = lean_array_push(x_395, x_450);
x_452 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_452, 0, x_397);
lean_ctor_set(x_452, 1, x_398);
lean_ctor_set(x_452, 2, x_451);
x_453 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__6;
lean_inc(x_265);
x_454 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_454, 0, x_265);
lean_ctor_set(x_454, 1, x_453);
x_455 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__60;
x_456 = l_Lean_addMacroScope(x_386, x_455, x_268);
x_457 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__59;
x_458 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__63;
x_459 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_459, 0, x_265);
lean_ctor_set(x_459, 1, x_457);
lean_ctor_set(x_459, 2, x_456);
lean_ctor_set(x_459, 3, x_458);
x_460 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__7;
x_461 = lean_array_push(x_460, x_445);
x_462 = lean_array_push(x_461, x_452);
x_463 = lean_array_push(x_462, x_454);
x_464 = lean_array_push(x_463, x_459);
x_465 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__8;
x_466 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_466, 0, x_397);
lean_ctor_set(x_466, 1, x_465);
lean_ctor_set(x_466, 2, x_464);
x_467 = lean_array_push(x_443, x_466);
x_468 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_468, 0, x_397);
lean_ctor_set(x_468, 1, x_398);
lean_ctor_set(x_468, 2, x_467);
x_469 = lean_array_push(x_395, x_468);
x_470 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__53;
x_471 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_471, 0, x_397);
lean_ctor_set(x_471, 1, x_470);
lean_ctor_set(x_471, 2, x_469);
x_472 = lean_array_push(x_400, x_441);
x_473 = lean_array_push(x_472, x_471);
x_474 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__51;
x_475 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_475, 0, x_397);
lean_ctor_set(x_475, 1, x_474);
lean_ctor_set(x_475, 2, x_473);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; 
x_476 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__67;
x_477 = lean_array_push(x_476, x_420);
x_478 = lean_array_push(x_477, x_422);
x_479 = lean_array_push(x_478, x_430);
x_480 = lean_array_push(x_479, x_432);
x_481 = lean_array_push(x_480, x_437);
x_482 = lean_array_push(x_481, x_439);
x_483 = lean_array_push(x_482, x_475);
x_484 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__14;
x_485 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_485, 0, x_397);
lean_ctor_set(x_485, 1, x_484);
lean_ctor_set(x_485, 2, x_483);
x_486 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_486, 0, x_485);
lean_ctor_set(x_486, 1, x_387);
return x_486;
}
else
{
lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; 
x_487 = lean_ctor_get(x_4, 0);
lean_inc(x_487);
lean_dec(x_4);
x_488 = lean_array_push(x_395, x_487);
x_489 = l_Array_append___rarg(x_442, x_488);
x_490 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_490, 0, x_397);
lean_ctor_set(x_490, 1, x_398);
lean_ctor_set(x_490, 2, x_489);
x_491 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__64;
x_492 = lean_array_push(x_491, x_490);
x_493 = lean_array_push(x_492, x_420);
x_494 = lean_array_push(x_493, x_422);
x_495 = lean_array_push(x_494, x_430);
x_496 = lean_array_push(x_495, x_432);
x_497 = lean_array_push(x_496, x_437);
x_498 = lean_array_push(x_497, x_439);
x_499 = lean_array_push(x_498, x_475);
x_500 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__14;
x_501 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_501, 0, x_397);
lean_ctor_set(x_501, 1, x_500);
lean_ctor_set(x_501, 2, x_499);
x_502 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_502, 0, x_501);
lean_ctor_set(x_502, 1, x_387);
return x_502;
}
}
}
}
else
{
lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; uint8_t x_513; 
lean_dec(x_5);
lean_inc(x_2);
x_503 = l_Lean_mkIdentFromRef___at_Lean_Elab_Command_elabElabRulesAux___spec__3(x_2, x_6, x_7, x_8);
x_504 = lean_ctor_get(x_503, 0);
lean_inc(x_504);
x_505 = lean_ctor_get(x_503, 1);
lean_inc(x_505);
lean_dec(x_503);
x_506 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Command_elabAuxDef___spec__4(x_6, x_7, x_505);
x_507 = lean_ctor_get(x_506, 0);
lean_inc(x_507);
x_508 = lean_ctor_get(x_506, 1);
lean_inc(x_508);
lean_dec(x_506);
x_509 = l_Lean_Elab_Command_getCurrMacroScope(x_6, x_7, x_508);
lean_dec(x_6);
x_510 = lean_ctor_get(x_509, 0);
lean_inc(x_510);
x_511 = lean_ctor_get(x_509, 1);
lean_inc(x_511);
lean_dec(x_509);
x_512 = l_Lean_Elab_Command_getMainModule___rarg(x_7, x_511);
lean_dec(x_7);
x_513 = !lean_is_exclusive(x_512);
if (x_513 == 0)
{
lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; 
x_514 = lean_ctor_get(x_512, 0);
x_515 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__17;
lean_inc(x_507);
x_516 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_516, 0, x_507);
lean_ctor_set(x_516, 1, x_515);
x_517 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__82;
lean_inc(x_510);
lean_inc(x_514);
x_518 = l_Lean_addMacroScope(x_514, x_517, x_510);
x_519 = lean_box(0);
x_520 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__81;
lean_inc(x_507);
x_521 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_521, 0, x_507);
lean_ctor_set(x_521, 1, x_520);
lean_ctor_set(x_521, 2, x_518);
lean_ctor_set(x_521, 3, x_519);
x_522 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__23;
x_523 = lean_array_push(x_522, x_504);
x_524 = lean_box(2);
x_525 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__3;
x_526 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_526, 0, x_524);
lean_ctor_set(x_526, 1, x_525);
lean_ctor_set(x_526, 2, x_523);
x_527 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__32;
x_528 = lean_array_push(x_527, x_521);
x_529 = lean_array_push(x_528, x_526);
x_530 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__29;
x_531 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_531, 0, x_524);
lean_ctor_set(x_531, 1, x_530);
lean_ctor_set(x_531, 2, x_529);
x_532 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__33;
x_533 = lean_array_push(x_532, x_531);
x_534 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__19;
x_535 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_535, 0, x_524);
lean_ctor_set(x_535, 1, x_534);
lean_ctor_set(x_535, 2, x_533);
x_536 = lean_array_push(x_522, x_535);
x_537 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_537, 0, x_524);
lean_ctor_set(x_537, 1, x_525);
lean_ctor_set(x_537, 2, x_536);
x_538 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__34;
lean_inc(x_507);
x_539 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_539, 0, x_507);
lean_ctor_set(x_539, 1, x_538);
x_540 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__35;
x_541 = lean_array_push(x_540, x_516);
x_542 = lean_array_push(x_541, x_537);
x_543 = lean_array_push(x_542, x_539);
x_544 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__16;
x_545 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_545, 0, x_524);
lean_ctor_set(x_545, 1, x_544);
lean_ctor_set(x_545, 2, x_543);
x_546 = lean_array_push(x_522, x_545);
x_547 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_547, 0, x_524);
lean_ctor_set(x_547, 1, x_525);
lean_ctor_set(x_547, 2, x_546);
x_548 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__13;
lean_inc(x_507);
x_549 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_549, 0, x_507);
lean_ctor_set(x_549, 1, x_548);
x_550 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__39;
lean_inc(x_510);
lean_inc(x_514);
x_551 = l_Lean_addMacroScope(x_514, x_550, x_510);
x_552 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__38;
lean_inc(x_507);
x_553 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_553, 0, x_507);
lean_ctor_set(x_553, 1, x_552);
lean_ctor_set(x_553, 2, x_551);
lean_ctor_set(x_553, 3, x_519);
x_554 = lean_mk_syntax_ident(x_2);
x_555 = lean_array_push(x_527, x_553);
x_556 = lean_array_push(x_555, x_554);
x_557 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_557, 0, x_524);
lean_ctor_set(x_557, 1, x_525);
lean_ctor_set(x_557, 2, x_556);
x_558 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__40;
lean_inc(x_507);
x_559 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_559, 0, x_507);
lean_ctor_set(x_559, 1, x_558);
x_560 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__88;
lean_inc(x_510);
lean_inc(x_514);
x_561 = l_Lean_addMacroScope(x_514, x_560, x_510);
x_562 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__85;
x_563 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__90;
lean_inc(x_507);
x_564 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_564, 0, x_507);
lean_ctor_set(x_564, 1, x_562);
lean_ctor_set(x_564, 2, x_561);
lean_ctor_set(x_564, 3, x_563);
x_565 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__49;
lean_inc(x_507);
x_566 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_566, 0, x_507);
lean_ctor_set(x_566, 1, x_565);
x_567 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__50;
lean_inc(x_507);
x_568 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_568, 0, x_507);
lean_ctor_set(x_568, 1, x_567);
x_569 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__96;
lean_inc(x_510);
lean_inc(x_514);
x_570 = l_Lean_addMacroScope(x_514, x_569, x_510);
x_571 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__95;
lean_inc(x_507);
x_572 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_572, 0, x_507);
lean_ctor_set(x_572, 1, x_571);
lean_ctor_set(x_572, 2, x_570);
lean_ctor_set(x_572, 3, x_519);
x_573 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__56;
lean_inc(x_507);
x_574 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_574, 0, x_507);
lean_ctor_set(x_574, 1, x_573);
x_575 = lean_array_push(x_522, x_574);
x_576 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__55;
x_577 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_577, 0, x_524);
lean_ctor_set(x_577, 1, x_576);
lean_ctor_set(x_577, 2, x_575);
lean_inc(x_572);
x_578 = lean_array_push(x_527, x_572);
lean_inc(x_577);
x_579 = lean_array_push(x_578, x_577);
x_580 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_580, 0, x_524);
lean_ctor_set(x_580, 1, x_525);
lean_ctor_set(x_580, 2, x_579);
x_581 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__6;
lean_inc(x_507);
x_582 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_582, 0, x_507);
lean_ctor_set(x_582, 1, x_581);
x_583 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__97;
lean_inc(x_507);
x_584 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_584, 0, x_507);
lean_ctor_set(x_584, 1, x_583);
x_585 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__101;
x_586 = lean_array_push(x_585, x_572);
x_587 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__100;
x_588 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_588, 0, x_524);
lean_ctor_set(x_588, 1, x_587);
lean_ctor_set(x_588, 2, x_586);
x_589 = lean_array_push(x_522, x_588);
x_590 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_590, 0, x_524);
lean_ctor_set(x_590, 1, x_525);
lean_ctor_set(x_590, 2, x_589);
x_591 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__102;
lean_inc(x_507);
x_592 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_592, 0, x_507);
lean_ctor_set(x_592, 1, x_591);
x_593 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__4;
x_594 = l_Array_append___rarg(x_593, x_3);
x_595 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__1;
lean_inc(x_507);
x_596 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_596, 0, x_507);
lean_ctor_set(x_596, 1, x_595);
x_597 = lean_array_push(x_522, x_577);
x_598 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_598, 0, x_524);
lean_ctor_set(x_598, 1, x_525);
lean_ctor_set(x_598, 2, x_597);
x_599 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__60;
x_600 = l_Lean_addMacroScope(x_514, x_599, x_510);
x_601 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__59;
x_602 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__63;
x_603 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_603, 0, x_507);
lean_ctor_set(x_603, 1, x_601);
lean_ctor_set(x_603, 2, x_600);
lean_ctor_set(x_603, 3, x_602);
x_604 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__7;
x_605 = lean_array_push(x_604, x_596);
x_606 = lean_array_push(x_605, x_598);
lean_inc(x_582);
x_607 = lean_array_push(x_606, x_582);
x_608 = lean_array_push(x_607, x_603);
x_609 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__8;
x_610 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_610, 0, x_524);
lean_ctor_set(x_610, 1, x_609);
lean_ctor_set(x_610, 2, x_608);
x_611 = lean_array_push(x_594, x_610);
x_612 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_612, 0, x_524);
lean_ctor_set(x_612, 1, x_525);
lean_ctor_set(x_612, 2, x_611);
x_613 = lean_array_push(x_522, x_612);
x_614 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__53;
x_615 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_615, 0, x_524);
lean_ctor_set(x_615, 1, x_614);
lean_ctor_set(x_615, 2, x_613);
x_616 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__103;
x_617 = lean_array_push(x_616, x_584);
x_618 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__22;
x_619 = lean_array_push(x_617, x_618);
x_620 = lean_array_push(x_619, x_590);
x_621 = lean_array_push(x_620, x_618);
x_622 = lean_array_push(x_621, x_592);
x_623 = lean_array_push(x_622, x_615);
x_624 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__98;
x_625 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_625, 0, x_524);
lean_ctor_set(x_625, 1, x_624);
lean_ctor_set(x_625, 2, x_623);
x_626 = lean_array_push(x_540, x_580);
x_627 = lean_array_push(x_626, x_582);
x_628 = lean_array_push(x_627, x_625);
x_629 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__92;
x_630 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_630, 0, x_524);
lean_ctor_set(x_630, 1, x_629);
lean_ctor_set(x_630, 2, x_628);
x_631 = lean_array_push(x_527, x_568);
x_632 = lean_array_push(x_631, x_630);
x_633 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__51;
x_634 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_634, 0, x_524);
lean_ctor_set(x_634, 1, x_633);
lean_ctor_set(x_634, 2, x_632);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; 
x_635 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__67;
x_636 = lean_array_push(x_635, x_547);
x_637 = lean_array_push(x_636, x_549);
x_638 = lean_array_push(x_637, x_557);
x_639 = lean_array_push(x_638, x_559);
x_640 = lean_array_push(x_639, x_564);
x_641 = lean_array_push(x_640, x_566);
x_642 = lean_array_push(x_641, x_634);
x_643 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__14;
x_644 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_644, 0, x_524);
lean_ctor_set(x_644, 1, x_643);
lean_ctor_set(x_644, 2, x_642);
lean_ctor_set(x_512, 0, x_644);
return x_512;
}
else
{
lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; 
x_645 = lean_ctor_get(x_4, 0);
lean_inc(x_645);
lean_dec(x_4);
x_646 = lean_array_push(x_522, x_645);
x_647 = l_Array_append___rarg(x_593, x_646);
x_648 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_648, 0, x_524);
lean_ctor_set(x_648, 1, x_525);
lean_ctor_set(x_648, 2, x_647);
x_649 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__64;
x_650 = lean_array_push(x_649, x_648);
x_651 = lean_array_push(x_650, x_547);
x_652 = lean_array_push(x_651, x_549);
x_653 = lean_array_push(x_652, x_557);
x_654 = lean_array_push(x_653, x_559);
x_655 = lean_array_push(x_654, x_564);
x_656 = lean_array_push(x_655, x_566);
x_657 = lean_array_push(x_656, x_634);
x_658 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__14;
x_659 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_659, 0, x_524);
lean_ctor_set(x_659, 1, x_658);
lean_ctor_set(x_659, 2, x_657);
lean_ctor_set(x_512, 0, x_659);
return x_512;
}
}
else
{
lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; 
x_660 = lean_ctor_get(x_512, 0);
x_661 = lean_ctor_get(x_512, 1);
lean_inc(x_661);
lean_inc(x_660);
lean_dec(x_512);
x_662 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__17;
lean_inc(x_507);
x_663 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_663, 0, x_507);
lean_ctor_set(x_663, 1, x_662);
x_664 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__82;
lean_inc(x_510);
lean_inc(x_660);
x_665 = l_Lean_addMacroScope(x_660, x_664, x_510);
x_666 = lean_box(0);
x_667 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__81;
lean_inc(x_507);
x_668 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_668, 0, x_507);
lean_ctor_set(x_668, 1, x_667);
lean_ctor_set(x_668, 2, x_665);
lean_ctor_set(x_668, 3, x_666);
x_669 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__23;
x_670 = lean_array_push(x_669, x_504);
x_671 = lean_box(2);
x_672 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__3;
x_673 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_673, 0, x_671);
lean_ctor_set(x_673, 1, x_672);
lean_ctor_set(x_673, 2, x_670);
x_674 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__32;
x_675 = lean_array_push(x_674, x_668);
x_676 = lean_array_push(x_675, x_673);
x_677 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__29;
x_678 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_678, 0, x_671);
lean_ctor_set(x_678, 1, x_677);
lean_ctor_set(x_678, 2, x_676);
x_679 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__33;
x_680 = lean_array_push(x_679, x_678);
x_681 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__19;
x_682 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_682, 0, x_671);
lean_ctor_set(x_682, 1, x_681);
lean_ctor_set(x_682, 2, x_680);
x_683 = lean_array_push(x_669, x_682);
x_684 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_684, 0, x_671);
lean_ctor_set(x_684, 1, x_672);
lean_ctor_set(x_684, 2, x_683);
x_685 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__34;
lean_inc(x_507);
x_686 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_686, 0, x_507);
lean_ctor_set(x_686, 1, x_685);
x_687 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__35;
x_688 = lean_array_push(x_687, x_663);
x_689 = lean_array_push(x_688, x_684);
x_690 = lean_array_push(x_689, x_686);
x_691 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__16;
x_692 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_692, 0, x_671);
lean_ctor_set(x_692, 1, x_691);
lean_ctor_set(x_692, 2, x_690);
x_693 = lean_array_push(x_669, x_692);
x_694 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_694, 0, x_671);
lean_ctor_set(x_694, 1, x_672);
lean_ctor_set(x_694, 2, x_693);
x_695 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__13;
lean_inc(x_507);
x_696 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_696, 0, x_507);
lean_ctor_set(x_696, 1, x_695);
x_697 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__39;
lean_inc(x_510);
lean_inc(x_660);
x_698 = l_Lean_addMacroScope(x_660, x_697, x_510);
x_699 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__38;
lean_inc(x_507);
x_700 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_700, 0, x_507);
lean_ctor_set(x_700, 1, x_699);
lean_ctor_set(x_700, 2, x_698);
lean_ctor_set(x_700, 3, x_666);
x_701 = lean_mk_syntax_ident(x_2);
x_702 = lean_array_push(x_674, x_700);
x_703 = lean_array_push(x_702, x_701);
x_704 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_704, 0, x_671);
lean_ctor_set(x_704, 1, x_672);
lean_ctor_set(x_704, 2, x_703);
x_705 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__40;
lean_inc(x_507);
x_706 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_706, 0, x_507);
lean_ctor_set(x_706, 1, x_705);
x_707 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__88;
lean_inc(x_510);
lean_inc(x_660);
x_708 = l_Lean_addMacroScope(x_660, x_707, x_510);
x_709 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__85;
x_710 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__90;
lean_inc(x_507);
x_711 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_711, 0, x_507);
lean_ctor_set(x_711, 1, x_709);
lean_ctor_set(x_711, 2, x_708);
lean_ctor_set(x_711, 3, x_710);
x_712 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__49;
lean_inc(x_507);
x_713 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_713, 0, x_507);
lean_ctor_set(x_713, 1, x_712);
x_714 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__50;
lean_inc(x_507);
x_715 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_715, 0, x_507);
lean_ctor_set(x_715, 1, x_714);
x_716 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__96;
lean_inc(x_510);
lean_inc(x_660);
x_717 = l_Lean_addMacroScope(x_660, x_716, x_510);
x_718 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__95;
lean_inc(x_507);
x_719 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_719, 0, x_507);
lean_ctor_set(x_719, 1, x_718);
lean_ctor_set(x_719, 2, x_717);
lean_ctor_set(x_719, 3, x_666);
x_720 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__56;
lean_inc(x_507);
x_721 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_721, 0, x_507);
lean_ctor_set(x_721, 1, x_720);
x_722 = lean_array_push(x_669, x_721);
x_723 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__55;
x_724 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_724, 0, x_671);
lean_ctor_set(x_724, 1, x_723);
lean_ctor_set(x_724, 2, x_722);
lean_inc(x_719);
x_725 = lean_array_push(x_674, x_719);
lean_inc(x_724);
x_726 = lean_array_push(x_725, x_724);
x_727 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_727, 0, x_671);
lean_ctor_set(x_727, 1, x_672);
lean_ctor_set(x_727, 2, x_726);
x_728 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__6;
lean_inc(x_507);
x_729 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_729, 0, x_507);
lean_ctor_set(x_729, 1, x_728);
x_730 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__97;
lean_inc(x_507);
x_731 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_731, 0, x_507);
lean_ctor_set(x_731, 1, x_730);
x_732 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__101;
x_733 = lean_array_push(x_732, x_719);
x_734 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__100;
x_735 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_735, 0, x_671);
lean_ctor_set(x_735, 1, x_734);
lean_ctor_set(x_735, 2, x_733);
x_736 = lean_array_push(x_669, x_735);
x_737 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_737, 0, x_671);
lean_ctor_set(x_737, 1, x_672);
lean_ctor_set(x_737, 2, x_736);
x_738 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__102;
lean_inc(x_507);
x_739 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_739, 0, x_507);
lean_ctor_set(x_739, 1, x_738);
x_740 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__4;
x_741 = l_Array_append___rarg(x_740, x_3);
x_742 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__1;
lean_inc(x_507);
x_743 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_743, 0, x_507);
lean_ctor_set(x_743, 1, x_742);
x_744 = lean_array_push(x_669, x_724);
x_745 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_745, 0, x_671);
lean_ctor_set(x_745, 1, x_672);
lean_ctor_set(x_745, 2, x_744);
x_746 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__60;
x_747 = l_Lean_addMacroScope(x_660, x_746, x_510);
x_748 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__59;
x_749 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__63;
x_750 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_750, 0, x_507);
lean_ctor_set(x_750, 1, x_748);
lean_ctor_set(x_750, 2, x_747);
lean_ctor_set(x_750, 3, x_749);
x_751 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__7;
x_752 = lean_array_push(x_751, x_743);
x_753 = lean_array_push(x_752, x_745);
lean_inc(x_729);
x_754 = lean_array_push(x_753, x_729);
x_755 = lean_array_push(x_754, x_750);
x_756 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__8;
x_757 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_757, 0, x_671);
lean_ctor_set(x_757, 1, x_756);
lean_ctor_set(x_757, 2, x_755);
x_758 = lean_array_push(x_741, x_757);
x_759 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_759, 0, x_671);
lean_ctor_set(x_759, 1, x_672);
lean_ctor_set(x_759, 2, x_758);
x_760 = lean_array_push(x_669, x_759);
x_761 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__53;
x_762 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_762, 0, x_671);
lean_ctor_set(x_762, 1, x_761);
lean_ctor_set(x_762, 2, x_760);
x_763 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__103;
x_764 = lean_array_push(x_763, x_731);
x_765 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__22;
x_766 = lean_array_push(x_764, x_765);
x_767 = lean_array_push(x_766, x_737);
x_768 = lean_array_push(x_767, x_765);
x_769 = lean_array_push(x_768, x_739);
x_770 = lean_array_push(x_769, x_762);
x_771 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__98;
x_772 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_772, 0, x_671);
lean_ctor_set(x_772, 1, x_771);
lean_ctor_set(x_772, 2, x_770);
x_773 = lean_array_push(x_687, x_727);
x_774 = lean_array_push(x_773, x_729);
x_775 = lean_array_push(x_774, x_772);
x_776 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__92;
x_777 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_777, 0, x_671);
lean_ctor_set(x_777, 1, x_776);
lean_ctor_set(x_777, 2, x_775);
x_778 = lean_array_push(x_674, x_715);
x_779 = lean_array_push(x_778, x_777);
x_780 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__51;
x_781 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_781, 0, x_671);
lean_ctor_set(x_781, 1, x_780);
lean_ctor_set(x_781, 2, x_779);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; 
x_782 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__67;
x_783 = lean_array_push(x_782, x_694);
x_784 = lean_array_push(x_783, x_696);
x_785 = lean_array_push(x_784, x_704);
x_786 = lean_array_push(x_785, x_706);
x_787 = lean_array_push(x_786, x_711);
x_788 = lean_array_push(x_787, x_713);
x_789 = lean_array_push(x_788, x_781);
x_790 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__14;
x_791 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_791, 0, x_671);
lean_ctor_set(x_791, 1, x_790);
lean_ctor_set(x_791, 2, x_789);
x_792 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_792, 0, x_791);
lean_ctor_set(x_792, 1, x_661);
return x_792;
}
else
{
lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; 
x_793 = lean_ctor_get(x_4, 0);
lean_inc(x_793);
lean_dec(x_4);
x_794 = lean_array_push(x_669, x_793);
x_795 = l_Array_append___rarg(x_740, x_794);
x_796 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_796, 0, x_671);
lean_ctor_set(x_796, 1, x_672);
lean_ctor_set(x_796, 2, x_795);
x_797 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__64;
x_798 = lean_array_push(x_797, x_796);
x_799 = lean_array_push(x_798, x_694);
x_800 = lean_array_push(x_799, x_696);
x_801 = lean_array_push(x_800, x_704);
x_802 = lean_array_push(x_801, x_706);
x_803 = lean_array_push(x_802, x_711);
x_804 = lean_array_push(x_803, x_713);
x_805 = lean_array_push(x_804, x_781);
x_806 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__14;
x_807 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_807, 0, x_671);
lean_ctor_set(x_807, 1, x_806);
lean_ctor_set(x_807, 2, x_805);
x_808 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_808, 0, x_807);
lean_ctor_set(x_808, 1, x_661);
return x_808;
}
}
}
}
else
{
lean_object* x_809; lean_object* x_810; uint8_t x_811; 
x_809 = lean_ctor_get(x_1, 0);
lean_inc(x_809);
lean_dec(x_1);
x_810 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__2;
x_811 = lean_name_eq(x_5, x_810);
if (x_811 == 0)
{
lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_812 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_812, 0, x_5);
x_813 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__105;
x_814 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_814, 0, x_813);
lean_ctor_set(x_814, 1, x_812);
x_815 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__107;
x_816 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_816, 0, x_814);
lean_ctor_set(x_816, 1, x_815);
x_817 = l_Lean_throwErrorAt___at_Lean_Elab_Command_elabCommand___spec__11(x_809, x_816, x_6, x_7, x_8);
return x_817;
}
else
{
lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; uint8_t x_828; 
lean_dec(x_5);
lean_inc(x_2);
x_818 = l_Lean_mkIdentFromRef___at_Lean_Elab_Command_elabElabRulesAux___spec__3(x_2, x_6, x_7, x_8);
x_819 = lean_ctor_get(x_818, 0);
lean_inc(x_819);
x_820 = lean_ctor_get(x_818, 1);
lean_inc(x_820);
lean_dec(x_818);
x_821 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Command_elabAuxDef___spec__4(x_6, x_7, x_820);
x_822 = lean_ctor_get(x_821, 0);
lean_inc(x_822);
x_823 = lean_ctor_get(x_821, 1);
lean_inc(x_823);
lean_dec(x_821);
x_824 = l_Lean_Elab_Command_getCurrMacroScope(x_6, x_7, x_823);
lean_dec(x_6);
x_825 = lean_ctor_get(x_824, 0);
lean_inc(x_825);
x_826 = lean_ctor_get(x_824, 1);
lean_inc(x_826);
lean_dec(x_824);
x_827 = l_Lean_Elab_Command_getMainModule___rarg(x_7, x_826);
lean_dec(x_7);
x_828 = !lean_is_exclusive(x_827);
if (x_828 == 0)
{
lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; lean_object* x_874; lean_object* x_875; lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; lean_object* x_895; lean_object* x_896; lean_object* x_897; lean_object* x_898; lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; lean_object* x_903; lean_object* x_904; lean_object* x_905; lean_object* x_906; lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; lean_object* x_911; lean_object* x_912; lean_object* x_913; lean_object* x_914; lean_object* x_915; lean_object* x_916; lean_object* x_917; lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; lean_object* x_925; lean_object* x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; lean_object* x_932; lean_object* x_933; lean_object* x_934; lean_object* x_935; lean_object* x_936; lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; lean_object* x_941; lean_object* x_942; lean_object* x_943; lean_object* x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; lean_object* x_949; lean_object* x_950; lean_object* x_951; lean_object* x_952; lean_object* x_953; lean_object* x_954; lean_object* x_955; lean_object* x_956; lean_object* x_957; lean_object* x_958; lean_object* x_959; lean_object* x_960; lean_object* x_961; lean_object* x_962; lean_object* x_963; lean_object* x_964; lean_object* x_965; lean_object* x_966; lean_object* x_967; lean_object* x_968; lean_object* x_969; lean_object* x_970; lean_object* x_971; lean_object* x_972; lean_object* x_973; 
x_829 = lean_ctor_get(x_827, 0);
x_830 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__17;
lean_inc(x_822);
x_831 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_831, 0, x_822);
lean_ctor_set(x_831, 1, x_830);
x_832 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__82;
lean_inc(x_825);
lean_inc(x_829);
x_833 = l_Lean_addMacroScope(x_829, x_832, x_825);
x_834 = lean_box(0);
x_835 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__81;
lean_inc(x_822);
x_836 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_836, 0, x_822);
lean_ctor_set(x_836, 1, x_835);
lean_ctor_set(x_836, 2, x_833);
lean_ctor_set(x_836, 3, x_834);
x_837 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__23;
x_838 = lean_array_push(x_837, x_819);
x_839 = lean_box(2);
x_840 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__3;
x_841 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_841, 0, x_839);
lean_ctor_set(x_841, 1, x_840);
lean_ctor_set(x_841, 2, x_838);
x_842 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__32;
x_843 = lean_array_push(x_842, x_836);
x_844 = lean_array_push(x_843, x_841);
x_845 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__29;
x_846 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_846, 0, x_839);
lean_ctor_set(x_846, 1, x_845);
lean_ctor_set(x_846, 2, x_844);
x_847 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__33;
x_848 = lean_array_push(x_847, x_846);
x_849 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__19;
x_850 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_850, 0, x_839);
lean_ctor_set(x_850, 1, x_849);
lean_ctor_set(x_850, 2, x_848);
x_851 = lean_array_push(x_837, x_850);
x_852 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_852, 0, x_839);
lean_ctor_set(x_852, 1, x_840);
lean_ctor_set(x_852, 2, x_851);
x_853 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__34;
lean_inc(x_822);
x_854 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_854, 0, x_822);
lean_ctor_set(x_854, 1, x_853);
x_855 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__35;
x_856 = lean_array_push(x_855, x_831);
x_857 = lean_array_push(x_856, x_852);
x_858 = lean_array_push(x_857, x_854);
x_859 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__16;
x_860 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_860, 0, x_839);
lean_ctor_set(x_860, 1, x_859);
lean_ctor_set(x_860, 2, x_858);
x_861 = lean_array_push(x_837, x_860);
x_862 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_862, 0, x_839);
lean_ctor_set(x_862, 1, x_840);
lean_ctor_set(x_862, 2, x_861);
x_863 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__13;
lean_inc(x_822);
x_864 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_864, 0, x_822);
lean_ctor_set(x_864, 1, x_863);
x_865 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__39;
lean_inc(x_825);
lean_inc(x_829);
x_866 = l_Lean_addMacroScope(x_829, x_865, x_825);
x_867 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__38;
lean_inc(x_822);
x_868 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_868, 0, x_822);
lean_ctor_set(x_868, 1, x_867);
lean_ctor_set(x_868, 2, x_866);
lean_ctor_set(x_868, 3, x_834);
x_869 = lean_mk_syntax_ident(x_2);
x_870 = lean_array_push(x_842, x_868);
x_871 = lean_array_push(x_870, x_869);
x_872 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_872, 0, x_839);
lean_ctor_set(x_872, 1, x_840);
lean_ctor_set(x_872, 2, x_871);
x_873 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__40;
lean_inc(x_822);
x_874 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_874, 0, x_822);
lean_ctor_set(x_874, 1, x_873);
x_875 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__88;
lean_inc(x_825);
lean_inc(x_829);
x_876 = l_Lean_addMacroScope(x_829, x_875, x_825);
x_877 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__85;
x_878 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__90;
lean_inc(x_822);
x_879 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_879, 0, x_822);
lean_ctor_set(x_879, 1, x_877);
lean_ctor_set(x_879, 2, x_876);
lean_ctor_set(x_879, 3, x_878);
x_880 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__49;
lean_inc(x_822);
x_881 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_881, 0, x_822);
lean_ctor_set(x_881, 1, x_880);
x_882 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__50;
lean_inc(x_822);
x_883 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_883, 0, x_822);
lean_ctor_set(x_883, 1, x_882);
x_884 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__96;
lean_inc(x_825);
lean_inc(x_829);
x_885 = l_Lean_addMacroScope(x_829, x_884, x_825);
x_886 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__95;
lean_inc(x_822);
x_887 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_887, 0, x_822);
lean_ctor_set(x_887, 1, x_886);
lean_ctor_set(x_887, 2, x_885);
lean_ctor_set(x_887, 3, x_834);
x_888 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__111;
lean_inc(x_825);
lean_inc(x_829);
x_889 = l_Lean_addMacroScope(x_829, x_888, x_825);
x_890 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__110;
lean_inc(x_822);
x_891 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_891, 0, x_822);
lean_ctor_set(x_891, 1, x_890);
lean_ctor_set(x_891, 2, x_889);
lean_ctor_set(x_891, 3, x_834);
lean_inc(x_887);
x_892 = lean_array_push(x_842, x_887);
lean_inc(x_891);
x_893 = lean_array_push(x_892, x_891);
x_894 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_894, 0, x_839);
lean_ctor_set(x_894, 1, x_840);
lean_ctor_set(x_894, 2, x_893);
x_895 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__6;
lean_inc(x_822);
x_896 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_896, 0, x_822);
lean_ctor_set(x_896, 1, x_895);
x_897 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__118;
lean_inc(x_825);
lean_inc(x_829);
x_898 = l_Lean_addMacroScope(x_829, x_897, x_825);
x_899 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__116;
x_900 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__120;
lean_inc(x_822);
x_901 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_901, 0, x_822);
lean_ctor_set(x_901, 1, x_899);
lean_ctor_set(x_901, 2, x_898);
lean_ctor_set(x_901, 3, x_900);
x_902 = lean_array_push(x_837, x_809);
x_903 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_903, 0, x_839);
lean_ctor_set(x_903, 1, x_840);
lean_ctor_set(x_903, 2, x_902);
x_904 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__97;
lean_inc(x_822);
x_905 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_905, 0, x_822);
lean_ctor_set(x_905, 1, x_904);
x_906 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__101;
x_907 = lean_array_push(x_906, x_887);
x_908 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__100;
x_909 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_909, 0, x_839);
lean_ctor_set(x_909, 1, x_908);
lean_ctor_set(x_909, 2, x_907);
x_910 = lean_array_push(x_837, x_909);
x_911 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_911, 0, x_839);
lean_ctor_set(x_911, 1, x_840);
lean_ctor_set(x_911, 2, x_910);
x_912 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__102;
lean_inc(x_822);
x_913 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_913, 0, x_822);
lean_ctor_set(x_913, 1, x_912);
x_914 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__4;
x_915 = l_Array_append___rarg(x_914, x_3);
x_916 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__1;
lean_inc(x_822);
x_917 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_917, 0, x_822);
lean_ctor_set(x_917, 1, x_916);
x_918 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__56;
lean_inc(x_822);
x_919 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_919, 0, x_822);
lean_ctor_set(x_919, 1, x_918);
x_920 = lean_array_push(x_837, x_919);
x_921 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__55;
x_922 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_922, 0, x_839);
lean_ctor_set(x_922, 1, x_921);
lean_ctor_set(x_922, 2, x_920);
x_923 = lean_array_push(x_837, x_922);
x_924 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_924, 0, x_839);
lean_ctor_set(x_924, 1, x_840);
lean_ctor_set(x_924, 2, x_923);
x_925 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__60;
x_926 = l_Lean_addMacroScope(x_829, x_925, x_825);
x_927 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__59;
x_928 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__63;
x_929 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_929, 0, x_822);
lean_ctor_set(x_929, 1, x_927);
lean_ctor_set(x_929, 2, x_926);
lean_ctor_set(x_929, 3, x_928);
x_930 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__7;
x_931 = lean_array_push(x_930, x_917);
x_932 = lean_array_push(x_931, x_924);
lean_inc(x_896);
x_933 = lean_array_push(x_932, x_896);
x_934 = lean_array_push(x_933, x_929);
x_935 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__8;
x_936 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_936, 0, x_839);
lean_ctor_set(x_936, 1, x_935);
lean_ctor_set(x_936, 2, x_934);
x_937 = lean_array_push(x_915, x_936);
x_938 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_938, 0, x_839);
lean_ctor_set(x_938, 1, x_840);
lean_ctor_set(x_938, 2, x_937);
x_939 = lean_array_push(x_837, x_938);
x_940 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__53;
x_941 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_941, 0, x_839);
lean_ctor_set(x_941, 1, x_940);
lean_ctor_set(x_941, 2, x_939);
x_942 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__103;
x_943 = lean_array_push(x_942, x_905);
x_944 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__22;
x_945 = lean_array_push(x_943, x_944);
x_946 = lean_array_push(x_945, x_911);
x_947 = lean_array_push(x_946, x_944);
x_948 = lean_array_push(x_947, x_913);
x_949 = lean_array_push(x_948, x_941);
x_950 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__98;
x_951 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_951, 0, x_839);
lean_ctor_set(x_951, 1, x_950);
lean_ctor_set(x_951, 2, x_949);
x_952 = lean_array_push(x_855, x_903);
lean_inc(x_896);
x_953 = lean_array_push(x_952, x_896);
x_954 = lean_array_push(x_953, x_951);
x_955 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__92;
x_956 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_956, 0, x_839);
lean_ctor_set(x_956, 1, x_955);
lean_ctor_set(x_956, 2, x_954);
x_957 = lean_array_push(x_842, x_883);
lean_inc(x_957);
x_958 = lean_array_push(x_957, x_956);
x_959 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__51;
x_960 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_960, 0, x_839);
lean_ctor_set(x_960, 1, x_959);
lean_ctor_set(x_960, 2, x_958);
x_961 = lean_array_push(x_842, x_891);
x_962 = lean_array_push(x_961, x_960);
x_963 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_963, 0, x_839);
lean_ctor_set(x_963, 1, x_840);
lean_ctor_set(x_963, 2, x_962);
x_964 = lean_array_push(x_842, x_901);
x_965 = lean_array_push(x_964, x_963);
x_966 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__113;
x_967 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_967, 0, x_839);
lean_ctor_set(x_967, 1, x_966);
lean_ctor_set(x_967, 2, x_965);
x_968 = lean_array_push(x_855, x_894);
x_969 = lean_array_push(x_968, x_896);
x_970 = lean_array_push(x_969, x_967);
x_971 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_971, 0, x_839);
lean_ctor_set(x_971, 1, x_955);
lean_ctor_set(x_971, 2, x_970);
x_972 = lean_array_push(x_957, x_971);
x_973 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_973, 0, x_839);
lean_ctor_set(x_973, 1, x_959);
lean_ctor_set(x_973, 2, x_972);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_974; lean_object* x_975; lean_object* x_976; lean_object* x_977; lean_object* x_978; lean_object* x_979; lean_object* x_980; lean_object* x_981; lean_object* x_982; lean_object* x_983; 
x_974 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__67;
x_975 = lean_array_push(x_974, x_862);
x_976 = lean_array_push(x_975, x_864);
x_977 = lean_array_push(x_976, x_872);
x_978 = lean_array_push(x_977, x_874);
x_979 = lean_array_push(x_978, x_879);
x_980 = lean_array_push(x_979, x_881);
x_981 = lean_array_push(x_980, x_973);
x_982 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__14;
x_983 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_983, 0, x_839);
lean_ctor_set(x_983, 1, x_982);
lean_ctor_set(x_983, 2, x_981);
lean_ctor_set(x_827, 0, x_983);
return x_827;
}
else
{
lean_object* x_984; lean_object* x_985; lean_object* x_986; lean_object* x_987; lean_object* x_988; lean_object* x_989; lean_object* x_990; lean_object* x_991; lean_object* x_992; lean_object* x_993; lean_object* x_994; lean_object* x_995; lean_object* x_996; lean_object* x_997; lean_object* x_998; 
x_984 = lean_ctor_get(x_4, 0);
lean_inc(x_984);
lean_dec(x_4);
x_985 = lean_array_push(x_837, x_984);
x_986 = l_Array_append___rarg(x_914, x_985);
x_987 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_987, 0, x_839);
lean_ctor_set(x_987, 1, x_840);
lean_ctor_set(x_987, 2, x_986);
x_988 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__64;
x_989 = lean_array_push(x_988, x_987);
x_990 = lean_array_push(x_989, x_862);
x_991 = lean_array_push(x_990, x_864);
x_992 = lean_array_push(x_991, x_872);
x_993 = lean_array_push(x_992, x_874);
x_994 = lean_array_push(x_993, x_879);
x_995 = lean_array_push(x_994, x_881);
x_996 = lean_array_push(x_995, x_973);
x_997 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__14;
x_998 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_998, 0, x_839);
lean_ctor_set(x_998, 1, x_997);
lean_ctor_set(x_998, 2, x_996);
lean_ctor_set(x_827, 0, x_998);
return x_827;
}
}
else
{
lean_object* x_999; lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; lean_object* x_1010; lean_object* x_1011; lean_object* x_1012; lean_object* x_1013; lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; lean_object* x_1020; lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; lean_object* x_1024; lean_object* x_1025; lean_object* x_1026; lean_object* x_1027; lean_object* x_1028; lean_object* x_1029; lean_object* x_1030; lean_object* x_1031; lean_object* x_1032; lean_object* x_1033; lean_object* x_1034; lean_object* x_1035; lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; lean_object* x_1039; lean_object* x_1040; lean_object* x_1041; lean_object* x_1042; lean_object* x_1043; lean_object* x_1044; lean_object* x_1045; lean_object* x_1046; lean_object* x_1047; lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; lean_object* x_1052; lean_object* x_1053; lean_object* x_1054; lean_object* x_1055; lean_object* x_1056; lean_object* x_1057; lean_object* x_1058; lean_object* x_1059; lean_object* x_1060; lean_object* x_1061; lean_object* x_1062; lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; lean_object* x_1066; lean_object* x_1067; lean_object* x_1068; lean_object* x_1069; lean_object* x_1070; lean_object* x_1071; lean_object* x_1072; lean_object* x_1073; lean_object* x_1074; lean_object* x_1075; lean_object* x_1076; lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; lean_object* x_1080; lean_object* x_1081; lean_object* x_1082; lean_object* x_1083; lean_object* x_1084; lean_object* x_1085; lean_object* x_1086; lean_object* x_1087; lean_object* x_1088; lean_object* x_1089; lean_object* x_1090; lean_object* x_1091; lean_object* x_1092; lean_object* x_1093; lean_object* x_1094; lean_object* x_1095; lean_object* x_1096; lean_object* x_1097; lean_object* x_1098; lean_object* x_1099; lean_object* x_1100; lean_object* x_1101; lean_object* x_1102; lean_object* x_1103; lean_object* x_1104; lean_object* x_1105; lean_object* x_1106; lean_object* x_1107; lean_object* x_1108; lean_object* x_1109; lean_object* x_1110; lean_object* x_1111; lean_object* x_1112; lean_object* x_1113; lean_object* x_1114; lean_object* x_1115; lean_object* x_1116; lean_object* x_1117; lean_object* x_1118; lean_object* x_1119; lean_object* x_1120; lean_object* x_1121; lean_object* x_1122; lean_object* x_1123; lean_object* x_1124; lean_object* x_1125; lean_object* x_1126; lean_object* x_1127; lean_object* x_1128; lean_object* x_1129; lean_object* x_1130; lean_object* x_1131; lean_object* x_1132; lean_object* x_1133; lean_object* x_1134; lean_object* x_1135; lean_object* x_1136; lean_object* x_1137; lean_object* x_1138; lean_object* x_1139; lean_object* x_1140; lean_object* x_1141; lean_object* x_1142; lean_object* x_1143; lean_object* x_1144; 
x_999 = lean_ctor_get(x_827, 0);
x_1000 = lean_ctor_get(x_827, 1);
lean_inc(x_1000);
lean_inc(x_999);
lean_dec(x_827);
x_1001 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__17;
lean_inc(x_822);
x_1002 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1002, 0, x_822);
lean_ctor_set(x_1002, 1, x_1001);
x_1003 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__82;
lean_inc(x_825);
lean_inc(x_999);
x_1004 = l_Lean_addMacroScope(x_999, x_1003, x_825);
x_1005 = lean_box(0);
x_1006 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__81;
lean_inc(x_822);
x_1007 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_1007, 0, x_822);
lean_ctor_set(x_1007, 1, x_1006);
lean_ctor_set(x_1007, 2, x_1004);
lean_ctor_set(x_1007, 3, x_1005);
x_1008 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__23;
x_1009 = lean_array_push(x_1008, x_819);
x_1010 = lean_box(2);
x_1011 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__3;
x_1012 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1012, 0, x_1010);
lean_ctor_set(x_1012, 1, x_1011);
lean_ctor_set(x_1012, 2, x_1009);
x_1013 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__32;
x_1014 = lean_array_push(x_1013, x_1007);
x_1015 = lean_array_push(x_1014, x_1012);
x_1016 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__29;
x_1017 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1017, 0, x_1010);
lean_ctor_set(x_1017, 1, x_1016);
lean_ctor_set(x_1017, 2, x_1015);
x_1018 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__33;
x_1019 = lean_array_push(x_1018, x_1017);
x_1020 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__19;
x_1021 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1021, 0, x_1010);
lean_ctor_set(x_1021, 1, x_1020);
lean_ctor_set(x_1021, 2, x_1019);
x_1022 = lean_array_push(x_1008, x_1021);
x_1023 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1023, 0, x_1010);
lean_ctor_set(x_1023, 1, x_1011);
lean_ctor_set(x_1023, 2, x_1022);
x_1024 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__34;
lean_inc(x_822);
x_1025 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1025, 0, x_822);
lean_ctor_set(x_1025, 1, x_1024);
x_1026 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__35;
x_1027 = lean_array_push(x_1026, x_1002);
x_1028 = lean_array_push(x_1027, x_1023);
x_1029 = lean_array_push(x_1028, x_1025);
x_1030 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__16;
x_1031 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1031, 0, x_1010);
lean_ctor_set(x_1031, 1, x_1030);
lean_ctor_set(x_1031, 2, x_1029);
x_1032 = lean_array_push(x_1008, x_1031);
x_1033 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1033, 0, x_1010);
lean_ctor_set(x_1033, 1, x_1011);
lean_ctor_set(x_1033, 2, x_1032);
x_1034 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__13;
lean_inc(x_822);
x_1035 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1035, 0, x_822);
lean_ctor_set(x_1035, 1, x_1034);
x_1036 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__39;
lean_inc(x_825);
lean_inc(x_999);
x_1037 = l_Lean_addMacroScope(x_999, x_1036, x_825);
x_1038 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__38;
lean_inc(x_822);
x_1039 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_1039, 0, x_822);
lean_ctor_set(x_1039, 1, x_1038);
lean_ctor_set(x_1039, 2, x_1037);
lean_ctor_set(x_1039, 3, x_1005);
x_1040 = lean_mk_syntax_ident(x_2);
x_1041 = lean_array_push(x_1013, x_1039);
x_1042 = lean_array_push(x_1041, x_1040);
x_1043 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1043, 0, x_1010);
lean_ctor_set(x_1043, 1, x_1011);
lean_ctor_set(x_1043, 2, x_1042);
x_1044 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__40;
lean_inc(x_822);
x_1045 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1045, 0, x_822);
lean_ctor_set(x_1045, 1, x_1044);
x_1046 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__88;
lean_inc(x_825);
lean_inc(x_999);
x_1047 = l_Lean_addMacroScope(x_999, x_1046, x_825);
x_1048 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__85;
x_1049 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__90;
lean_inc(x_822);
x_1050 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_1050, 0, x_822);
lean_ctor_set(x_1050, 1, x_1048);
lean_ctor_set(x_1050, 2, x_1047);
lean_ctor_set(x_1050, 3, x_1049);
x_1051 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__49;
lean_inc(x_822);
x_1052 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1052, 0, x_822);
lean_ctor_set(x_1052, 1, x_1051);
x_1053 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__50;
lean_inc(x_822);
x_1054 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1054, 0, x_822);
lean_ctor_set(x_1054, 1, x_1053);
x_1055 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__96;
lean_inc(x_825);
lean_inc(x_999);
x_1056 = l_Lean_addMacroScope(x_999, x_1055, x_825);
x_1057 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__95;
lean_inc(x_822);
x_1058 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_1058, 0, x_822);
lean_ctor_set(x_1058, 1, x_1057);
lean_ctor_set(x_1058, 2, x_1056);
lean_ctor_set(x_1058, 3, x_1005);
x_1059 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__111;
lean_inc(x_825);
lean_inc(x_999);
x_1060 = l_Lean_addMacroScope(x_999, x_1059, x_825);
x_1061 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__110;
lean_inc(x_822);
x_1062 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_1062, 0, x_822);
lean_ctor_set(x_1062, 1, x_1061);
lean_ctor_set(x_1062, 2, x_1060);
lean_ctor_set(x_1062, 3, x_1005);
lean_inc(x_1058);
x_1063 = lean_array_push(x_1013, x_1058);
lean_inc(x_1062);
x_1064 = lean_array_push(x_1063, x_1062);
x_1065 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1065, 0, x_1010);
lean_ctor_set(x_1065, 1, x_1011);
lean_ctor_set(x_1065, 2, x_1064);
x_1066 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__6;
lean_inc(x_822);
x_1067 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1067, 0, x_822);
lean_ctor_set(x_1067, 1, x_1066);
x_1068 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__118;
lean_inc(x_825);
lean_inc(x_999);
x_1069 = l_Lean_addMacroScope(x_999, x_1068, x_825);
x_1070 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__116;
x_1071 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__120;
lean_inc(x_822);
x_1072 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_1072, 0, x_822);
lean_ctor_set(x_1072, 1, x_1070);
lean_ctor_set(x_1072, 2, x_1069);
lean_ctor_set(x_1072, 3, x_1071);
x_1073 = lean_array_push(x_1008, x_809);
x_1074 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1074, 0, x_1010);
lean_ctor_set(x_1074, 1, x_1011);
lean_ctor_set(x_1074, 2, x_1073);
x_1075 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__97;
lean_inc(x_822);
x_1076 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1076, 0, x_822);
lean_ctor_set(x_1076, 1, x_1075);
x_1077 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__101;
x_1078 = lean_array_push(x_1077, x_1058);
x_1079 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__100;
x_1080 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1080, 0, x_1010);
lean_ctor_set(x_1080, 1, x_1079);
lean_ctor_set(x_1080, 2, x_1078);
x_1081 = lean_array_push(x_1008, x_1080);
x_1082 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1082, 0, x_1010);
lean_ctor_set(x_1082, 1, x_1011);
lean_ctor_set(x_1082, 2, x_1081);
x_1083 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__102;
lean_inc(x_822);
x_1084 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1084, 0, x_822);
lean_ctor_set(x_1084, 1, x_1083);
x_1085 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__4;
x_1086 = l_Array_append___rarg(x_1085, x_3);
x_1087 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__1;
lean_inc(x_822);
x_1088 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1088, 0, x_822);
lean_ctor_set(x_1088, 1, x_1087);
x_1089 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__56;
lean_inc(x_822);
x_1090 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_1090, 0, x_822);
lean_ctor_set(x_1090, 1, x_1089);
x_1091 = lean_array_push(x_1008, x_1090);
x_1092 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__55;
x_1093 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1093, 0, x_1010);
lean_ctor_set(x_1093, 1, x_1092);
lean_ctor_set(x_1093, 2, x_1091);
x_1094 = lean_array_push(x_1008, x_1093);
x_1095 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1095, 0, x_1010);
lean_ctor_set(x_1095, 1, x_1011);
lean_ctor_set(x_1095, 2, x_1094);
x_1096 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__60;
x_1097 = l_Lean_addMacroScope(x_999, x_1096, x_825);
x_1098 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__59;
x_1099 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__63;
x_1100 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_1100, 0, x_822);
lean_ctor_set(x_1100, 1, x_1098);
lean_ctor_set(x_1100, 2, x_1097);
lean_ctor_set(x_1100, 3, x_1099);
x_1101 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___lambda__2___closed__7;
x_1102 = lean_array_push(x_1101, x_1088);
x_1103 = lean_array_push(x_1102, x_1095);
lean_inc(x_1067);
x_1104 = lean_array_push(x_1103, x_1067);
x_1105 = lean_array_push(x_1104, x_1100);
x_1106 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__8;
x_1107 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1107, 0, x_1010);
lean_ctor_set(x_1107, 1, x_1106);
lean_ctor_set(x_1107, 2, x_1105);
x_1108 = lean_array_push(x_1086, x_1107);
x_1109 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1109, 0, x_1010);
lean_ctor_set(x_1109, 1, x_1011);
lean_ctor_set(x_1109, 2, x_1108);
x_1110 = lean_array_push(x_1008, x_1109);
x_1111 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__53;
x_1112 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1112, 0, x_1010);
lean_ctor_set(x_1112, 1, x_1111);
lean_ctor_set(x_1112, 2, x_1110);
x_1113 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__103;
x_1114 = lean_array_push(x_1113, x_1076);
x_1115 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__22;
x_1116 = lean_array_push(x_1114, x_1115);
x_1117 = lean_array_push(x_1116, x_1082);
x_1118 = lean_array_push(x_1117, x_1115);
x_1119 = lean_array_push(x_1118, x_1084);
x_1120 = lean_array_push(x_1119, x_1112);
x_1121 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__98;
x_1122 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1122, 0, x_1010);
lean_ctor_set(x_1122, 1, x_1121);
lean_ctor_set(x_1122, 2, x_1120);
x_1123 = lean_array_push(x_1026, x_1074);
lean_inc(x_1067);
x_1124 = lean_array_push(x_1123, x_1067);
x_1125 = lean_array_push(x_1124, x_1122);
x_1126 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__92;
x_1127 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1127, 0, x_1010);
lean_ctor_set(x_1127, 1, x_1126);
lean_ctor_set(x_1127, 2, x_1125);
x_1128 = lean_array_push(x_1013, x_1054);
lean_inc(x_1128);
x_1129 = lean_array_push(x_1128, x_1127);
x_1130 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__51;
x_1131 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1131, 0, x_1010);
lean_ctor_set(x_1131, 1, x_1130);
lean_ctor_set(x_1131, 2, x_1129);
x_1132 = lean_array_push(x_1013, x_1062);
x_1133 = lean_array_push(x_1132, x_1131);
x_1134 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1134, 0, x_1010);
lean_ctor_set(x_1134, 1, x_1011);
lean_ctor_set(x_1134, 2, x_1133);
x_1135 = lean_array_push(x_1013, x_1072);
x_1136 = lean_array_push(x_1135, x_1134);
x_1137 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__113;
x_1138 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1138, 0, x_1010);
lean_ctor_set(x_1138, 1, x_1137);
lean_ctor_set(x_1138, 2, x_1136);
x_1139 = lean_array_push(x_1026, x_1065);
x_1140 = lean_array_push(x_1139, x_1067);
x_1141 = lean_array_push(x_1140, x_1138);
x_1142 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1142, 0, x_1010);
lean_ctor_set(x_1142, 1, x_1126);
lean_ctor_set(x_1142, 2, x_1141);
x_1143 = lean_array_push(x_1128, x_1142);
x_1144 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1144, 0, x_1010);
lean_ctor_set(x_1144, 1, x_1130);
lean_ctor_set(x_1144, 2, x_1143);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_1145; lean_object* x_1146; lean_object* x_1147; lean_object* x_1148; lean_object* x_1149; lean_object* x_1150; lean_object* x_1151; lean_object* x_1152; lean_object* x_1153; lean_object* x_1154; lean_object* x_1155; 
x_1145 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__67;
x_1146 = lean_array_push(x_1145, x_1033);
x_1147 = lean_array_push(x_1146, x_1035);
x_1148 = lean_array_push(x_1147, x_1043);
x_1149 = lean_array_push(x_1148, x_1045);
x_1150 = lean_array_push(x_1149, x_1050);
x_1151 = lean_array_push(x_1150, x_1052);
x_1152 = lean_array_push(x_1151, x_1144);
x_1153 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__14;
x_1154 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1154, 0, x_1010);
lean_ctor_set(x_1154, 1, x_1153);
lean_ctor_set(x_1154, 2, x_1152);
x_1155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1155, 0, x_1154);
lean_ctor_set(x_1155, 1, x_1000);
return x_1155;
}
else
{
lean_object* x_1156; lean_object* x_1157; lean_object* x_1158; lean_object* x_1159; lean_object* x_1160; lean_object* x_1161; lean_object* x_1162; lean_object* x_1163; lean_object* x_1164; lean_object* x_1165; lean_object* x_1166; lean_object* x_1167; lean_object* x_1168; lean_object* x_1169; lean_object* x_1170; lean_object* x_1171; 
x_1156 = lean_ctor_get(x_4, 0);
lean_inc(x_1156);
lean_dec(x_4);
x_1157 = lean_array_push(x_1008, x_1156);
x_1158 = l_Array_append___rarg(x_1085, x_1157);
x_1159 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1159, 0, x_1010);
lean_ctor_set(x_1159, 1, x_1011);
lean_ctor_set(x_1159, 2, x_1158);
x_1160 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__64;
x_1161 = lean_array_push(x_1160, x_1159);
x_1162 = lean_array_push(x_1161, x_1033);
x_1163 = lean_array_push(x_1162, x_1035);
x_1164 = lean_array_push(x_1163, x_1043);
x_1165 = lean_array_push(x_1164, x_1045);
x_1166 = lean_array_push(x_1165, x_1050);
x_1167 = lean_array_push(x_1166, x_1052);
x_1168 = lean_array_push(x_1167, x_1144);
x_1169 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__14;
x_1170 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1170, 0, x_1010);
lean_ctor_set(x_1170, 1, x_1169);
lean_ctor_set(x_1170, 2, x_1168);
x_1171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1171, 0, x_1170);
lean_ctor_set(x_1171, 1, x_1000);
return x_1171;
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
lean_dec(x_2);
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
x_24 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1(x_5, x_3, x_21, x_1, x_23, x_7, x_8, x_22);
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
x_29 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1(x_5, x_3, x_25, x_1, x_28, x_7, x_8, x_26);
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
x_14 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__52;
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
x_27 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__23;
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
x_76 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__49;
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
x_64 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__40;
lean_inc(x_13);
x_65 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_65, 0, x_13);
lean_ctor_set(x_65, 1, x_64);
x_66 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__32;
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
x_45 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__66;
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
x_53 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__32;
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
x_14 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__52;
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
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabElabRules___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_dec(x_4);
x_9 = lean_unsigned_to_nat(1u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
x_11 = l_Array_mapMUnsafe_map___at_Lean_Elab_Command_elabElabRulesAux___spec__2___closed__5;
x_12 = lean_name_mk_string(x_2, x_11);
x_13 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__20;
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
x_1 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__23;
x_2 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__22;
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
x_40 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__49;
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
x_51 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__23;
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
x_75 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__40;
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
x_82 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__32;
lean_inc(x_76);
x_83 = lean_array_push(x_82, x_76);
lean_inc(x_7);
lean_inc(x_83);
x_84 = lean_array_push(x_83, x_7);
x_85 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_85, 0, x_22);
lean_ctor_set(x_85, 1, x_53);
lean_ctor_set(x_85, 2, x_84);
x_86 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__52;
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
x_96 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__35;
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
x_126 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__22;
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
x_140 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__66;
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
x_12 = l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__20;
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
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__116 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__116();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__116);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__117 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__117();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__117);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__118 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__118();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__118);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__119 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__119();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__119);
l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__120 = _init_l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__120();
lean_mark_persistent(l_Lean_Elab_Command_elabElabRulesAux___lambda__1___closed__120);
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
