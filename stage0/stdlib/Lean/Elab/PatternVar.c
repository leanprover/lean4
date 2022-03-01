// Lean compiler output
// Module: Lean.Elab.PatternVar
// Imports: Init Lean.Meta.Match.MatchPatternAttr Lean.Elab.Arg Lean.Elab.MatchAltView
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
lean_object* l_List_reverse___rarg(lean_object*);
lean_object* l_Lean_getConstInfo___at_Lean_Elab_Term_mkConst___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_collectPatternVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_resolveGlobalConstNoOverloadWithInfo___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___closed__8;
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwIllFormedSyntax___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_quotedNameToPattern___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__29;
lean_object* lean_erase_macro_scopes(lean_object*);
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__4___closed__3;
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Elab_Term_getPatternsVars___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Elab_Term_CollectPatternVars_instInhabitedContext___closed__1;
lean_object* l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Array_filterMapM___at_Lean_Elab_Term_getPatternVarNames___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___lambda__2___closed__2;
lean_object* l_Lean_throwError___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___closed__4;
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_pushNewArg___closed__2;
lean_object* l_Lean_LocalDecl_userName(lean_object*);
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___closed__17;
extern lean_object* l_Lean_nullKind;
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__25;
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__3___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Array_eraseIdx___rarg(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_Term_addDotCompletionInfo___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___closed__9;
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_pushNewArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_resolveGlobalConstNoOverloadWithInfo___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___spec__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_pushNewArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___closed__1;
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__6;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_getPatternsVars___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTRAux___at_Lean_resolveGlobalConstCore___spec__2(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_getPatternsVars___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Lean_SourceInfo_fromRef(lean_object*);
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__2___closed__1;
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___rarg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_filterMap___at_Lean_resolveGlobalConst___spec__1(lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l_Lean_addTrace___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__6;
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__4___closed__2;
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__4___closed__1;
static lean_object* l_Lean_Elab_throwIllFormedSyntax___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_quotedNameToPattern___spec__1___closed__1;
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__33;
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___lambda__2___closed__1;
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__14;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_main___spec__3___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__28;
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___rarg___closed__1;
lean_object* lean_environment_find(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__3___closed__1;
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___lambda__2___closed__3;
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_mkAuxName___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_getPatternsVars___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_mkMVarSyntax(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___closed__23;
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__2___closed__2;
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__2;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_getPatternsVars___spec__6___rarg___closed__1;
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___closed__2;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_main___spec__3___closed__6;
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___closed__21;
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__30;
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_getPatternsVars___spec__1___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__18;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___closed__13;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_main___spec__3___closed__2;
lean_object* l_Lean_MessageData_ofList(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___rarg___closed__2;
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_throwIllFormedSyntax___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_quotedNameToPattern___spec__1___closed__2;
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__3___closed__4;
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__7;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_main___spec__3___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_expandDeclId___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__3___closed__8;
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__3;
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__15;
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_getPatternsVars___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__3___closed__9;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___lambda__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getMainModule___rarg(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_pushNewArg___closed__4;
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__3___closed__1;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_getPatternsVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern(lean_object*);
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__9;
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__3;
static lean_object* l_Lean_resolveGlobalConst___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__3___closed__2;
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_mkMVarSyntax___closed__3;
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Elab_Term_getPatternsVars___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__8;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_main___spec__3___closed__1;
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__10___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_main___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__5;
extern lean_object* l_Lean_LocalContext_empty;
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__5;
lean_object* l_Lean_Elab_liftMacroM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTRAux___at_Lean_resolveGlobalConstNoOverload___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___closed__2;
lean_object* l_Lean_throwError___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_resolveGlobalConst___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_getMVarSyntaxMVarId___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__27;
LEAN_EXPORT uint8_t l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_isDone(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_pushNewArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___closed__12;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_main___spec__3___closed__4;
lean_object* l_Lean_Syntax_mkApp(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__3___closed__7;
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_getNextParam(lean_object*);
lean_object* l_Lean_ResolveName_resolveNamespace_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___closed__1;
static lean_object* l_Lean_resolveGlobalConst___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__3___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_isDone___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Elab_Term_CollectPatternVars_main___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_processExplicitArg___closed__1;
lean_object* l_Lean_Elab_expandMacroImpl_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
extern lean_object* l_Lean_numLitKind;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_Context_newArgs___default;
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__3___closed__5;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_getPatternVarNames___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_mkMVarSyntax___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__17;
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_getPatternVarNames(lean_object*);
extern lean_object* l_Lean_strLitKind;
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__3___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_0__Array_mapSepElemsMAux___at_Lean_Elab_Term_CollectPatternVars_collect___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_State_found___default;
LEAN_EXPORT lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_main___spec__3___closed__3;
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstCore___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__5___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__34;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_processImplicitArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__31;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_getPatternsVars___spec__6___rarg(lean_object*);
static lean_object* l_Lean_addTrace___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__3;
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__9;
lean_object* l_instInhabited___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_mkMVarSyntax___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__4;
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__21;
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__8;
LEAN_EXPORT uint8_t l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_isNextArgAccessible(lean_object*);
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___closed__19;
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__4___closed__4;
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstCore___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__5___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__2;
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___closed__11;
lean_object* l_Nat_repr(lean_object*);
uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Elab_Term_CollectPatternVars_main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_collectPatternVars___closed__1;
lean_object* lean_format_pretty(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstCore___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_choiceKind;
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__6;
extern lean_object* l_Lean_charLitKind;
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_getNextParam___closed__1;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_main___spec__3___closed__5;
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__23;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_quotedNameToPattern(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_isNextArgAccessible___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_processCtor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__13;
lean_object* l_Lean_Elab_Term_getCurrMacroScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*, lean_object*);
uint8_t l_Lean_Name_isAtomic(lean_object*);
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___closed__20;
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___closed__10;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_getPatternVarNames___spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_pure___at_Lean_Elab_liftMacroM___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Elab_Term_getPatternsVars___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkStrLit(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_resolveId_x3f(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandApp(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___rarg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_collect___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__12;
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___closed__16;
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___closed__24;
size_t lean_usize_of_nat(lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_getPatternsVars___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__12;
lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceOptions(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__26;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_instToStringPatternVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_getMVarSyntaxMVarId(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_filterAux___at_Lean_resolveGlobalConstCore___spec__1(lean_object*, lean_object*);
extern uint8_t l_Lean_instInhabitedBinderInfo;
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__11;
extern lean_object* l_Lean_identKind;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_getPatternVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_mkMVarSyntax___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_getPatternsVars___spec__1___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_mkMVarSyntax___closed__2;
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_mkMVarSyntax___spec__1___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_push___rarg(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__19;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_getPatternsVars___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Meta_0__Array_mapSepElemsMAux___at_Lean_Elab_Term_CollectPatternVars_collect___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__10;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_instMonadTermElabM;
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__32;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_processExplicitArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_scientificLitKind;
lean_object* l_Lean_Syntax_setArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_main_module(lean_object*);
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__20;
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Elab_Term_CollectPatternVars_main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___spec__3(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__3___closed__10;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_getPatternsVars___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_main___spec__3(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at_Lean_Elab_Term_CollectPatternVars_collect_processExplicitArg___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l_Lean_BinderInfo_isExplicit(uint8_t);
lean_object* l_Lean_Syntax_getKind(lean_object*);
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__35;
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__11;
static lean_object* l_Lean_throwUnknownConstant___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__6___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_State_vars___default;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_collect_processExplicitArg___spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_processExplicitArg___closed__2;
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_mkMVarSyntax___closed__1;
uint8_t l_Lean_TagAttribute_hasTag(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_processImplicitArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_getPatternsVars___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTRAux___at_Lean_mkConstWithLevelParams___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at_Lean_Elab_Term_getPatternVarNames___spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_collect___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected(lean_object*);
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__24;
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_getPatternsVars___spec__1___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___closed__22;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Elab_Term_CollectPatternVars_collect_pushNewArg___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapSepElemsM___at_Lean_Elab_Term_CollectPatternVars_collect___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapSepElemsM___at_Lean_Elab_Term_CollectPatternVars_collect___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_resolveGlobalName___at_Lean_Elab_Term_resolveName___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_processExplicitArg___closed__3;
extern lean_object* l_Lean_instInhabitedName;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_Context_paramDeclIdx___default;
lean_object* l_Lean_Elab_Term_withFreshMacroScope___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* lean_name_mk_numeral(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_CollectPatternVars_collect_processExplicitArg___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Elab_Term_CollectPatternVars_collect_pushNewArg___spec__1___closed__2;
lean_object* l_Lean_expandMacros(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_getPatternsVars___spec__1___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_instInhabitedNamedArg;
lean_object* l_Lean_Syntax_isNameLit_x3f(lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverload___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___closed__25;
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_getPatternVarNames___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Elab_Term_getPatternsVars___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___closed__7;
LEAN_EXPORT lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___spec__1___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
LEAN_EXPORT lean_object* l_Lean_Elab_throwIllFormedSyntax___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_quotedNameToPattern___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__16;
static lean_object* l_panic___at_Lean_Elab_Term_CollectPatternVars_collect_pushNewArg___spec__1___closed__1;
lean_object* l_ReaderT_instMonadReaderT___rarg(lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_processExplicitArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_resolveGlobalConstNoOverloadWithInfo___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_getPatternsVars___spec__5___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_getPatternsVars___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_processId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_mkMVarSyntax___closed__4;
lean_object* lean_nat_mod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_getPatternsVars___spec__7(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_pushNewArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_pushNewArg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_getPatternsVars___spec__1___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppContext___closed__1;
lean_object* l_Array_findIdx_x3f_loop___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___spec__2___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwUnknownConstant___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__6___closed__4;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_collect_processExplicitArg___spec__1(size_t, size_t, lean_object*);
uint8_t l_List_isEmpty___rarg(lean_object*);
static lean_object* l_Lean_addTrace___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_CollectPatternVars_collect_processExplicitArg___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwUnknownConstant___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__6___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___spec__4___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_toString___at_Lean_resolveGlobalConstNoOverloadCore___spec__2(lean_object*);
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__22;
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___closed__3;
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___closed__18;
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_getPatternsVars___spec__1___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__2___closed__4;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_getPatternsVars___spec__5___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___closed__14;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_getPatternsVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_instToStringPatternVar___closed__1;
static lean_object* l_Lean_Elab_Term_instToStringPatternVar___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___closed__15;
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__10;
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___closed__5;
lean_object* l_Lean_Syntax_formatStxAux(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_resolveGlobalConstNoOverload___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__2___closed__1;
static lean_object* l_Lean_throwUnknownConstant___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__6___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___spec__4(lean_object*);
static lean_object* l_Lean_resolveGlobalConstNoOverload___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_mkMVarSyntax___spec__1___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___closed__2;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_getPatternsVars___spec__6___rarg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_pushNewArg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___closed__1;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkLit(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_instInhabitedContext;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppContext___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppContext___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFVarLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_matchPatternAttr;
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isIdent(lean_object*);
static lean_object* l_Lean_addTrace___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_getPatternsVars___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Elab_Term_instToStringPatternVar___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("?m");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_instToStringPatternVar___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_instToStringPatternVar(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = 1;
x_4 = l_Lean_Name_toString(x_2, x_3);
return x_4;
}
else
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = 1;
x_7 = l_Lean_Name_toString(x_5, x_6);
x_8 = l_Lean_Elab_Term_instToStringPatternVar___closed__1;
x_9 = lean_string_append(x_8, x_7);
lean_dec(x_7);
x_10 = l_Lean_Elab_Term_instToStringPatternVar___closed__2;
x_11 = lean_string_append(x_9, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_mkMVarSyntax___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 2);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
lean_inc(x_8);
x_10 = lean_name_mk_numeral(x_8, x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_9, x_11);
lean_dec(x_9);
lean_ctor_set(x_5, 1, x_12);
x_13 = lean_st_ref_take(x_1, x_6);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_14, 2);
lean_dec(x_17);
lean_ctor_set(x_14, 2, x_5);
x_18 = lean_st_ref_set(x_1, x_14, x_15);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
lean_ctor_set(x_18, 0, x_10);
return x_18;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_10);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_14, 0);
x_24 = lean_ctor_get(x_14, 1);
x_25 = lean_ctor_get(x_14, 3);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_14);
x_26 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_24);
lean_ctor_set(x_26, 2, x_5);
lean_ctor_set(x_26, 3, x_25);
x_27 = lean_st_ref_set(x_1, x_26, x_15);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_29 = x_27;
} else {
 lean_dec_ref(x_27);
 x_29 = lean_box(0);
}
if (lean_is_scalar(x_29)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_29;
}
lean_ctor_set(x_30, 0, x_10);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_31 = lean_ctor_get(x_5, 0);
x_32 = lean_ctor_get(x_5, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_5);
lean_inc(x_32);
lean_inc(x_31);
x_33 = lean_name_mk_numeral(x_31, x_32);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_add(x_32, x_34);
lean_dec(x_32);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_31);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_st_ref_take(x_1, x_6);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_38, 3);
lean_inc(x_42);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 lean_ctor_release(x_38, 2);
 lean_ctor_release(x_38, 3);
 x_43 = x_38;
} else {
 lean_dec_ref(x_38);
 x_43 = lean_box(0);
}
if (lean_is_scalar(x_43)) {
 x_44 = lean_alloc_ctor(0, 4, 0);
} else {
 x_44 = x_43;
}
lean_ctor_set(x_44, 0, x_40);
lean_ctor_set(x_44, 1, x_41);
lean_ctor_set(x_44, 2, x_36);
lean_ctor_set(x_44, 3, x_42);
x_45 = lean_st_ref_set(x_1, x_44, x_39);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_47 = x_45;
} else {
 lean_dec_ref(x_45);
 x_47 = lean_box(0);
}
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_33);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_mkMVarSyntax___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l_Lean_mkFreshId___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_mkMVarSyntax___spec__1___rarg___boxed), 2, 0);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_mkMVarSyntax___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("MVarWithIdKind");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_mkMVarSyntax___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_mkMVarSyntax___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_mkMVarSyntax___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_mkMVarSyntax___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_mkMVarSyntax(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_mkFreshId___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_mkMVarSyntax___spec__1___rarg(x_6, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_box(2);
x_12 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_mkMVarSyntax___closed__3;
x_13 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set(x_13, 2, x_12);
x_14 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_mkMVarSyntax___closed__4;
x_15 = lean_array_push(x_14, x_13);
x_16 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_mkMVarSyntax___closed__2;
x_17 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_17, 0, x_11);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_17, 2, x_15);
lean_ctor_set(x_8, 0, x_17);
return x_8;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_18 = lean_ctor_get(x_8, 0);
x_19 = lean_ctor_get(x_8, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_8);
x_20 = lean_box(2);
x_21 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_mkMVarSyntax___closed__3;
x_22 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_18);
lean_ctor_set(x_22, 2, x_21);
x_23 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_mkMVarSyntax___closed__4;
x_24 = lean_array_push(x_23, x_22);
x_25 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_mkMVarSyntax___closed__2;
x_26 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_26, 0, x_20);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_26, 2, x_24);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_19);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_mkMVarSyntax___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkFreshId___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_mkMVarSyntax___spec__1___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_mkMVarSyntax___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_mkFreshId___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_mkMVarSyntax___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_mkMVarSyntax___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_mkMVarSyntax(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_getMVarSyntaxMVarId(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Syntax_getArg(x_1, x_2);
x_4 = l_Lean_Syntax_getKind(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_getMVarSyntaxMVarId___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_getMVarSyntaxMVarId(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_State_found___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_NameSet_empty;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_State_vars___default() {
_start:
{
lean_object* x_1; 
x_1 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_mkMVarSyntax___closed__3;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_7, 3);
x_11 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_5, x_6, x_7, x_8, x_9);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_13);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_11);
lean_inc(x_10);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___spec__1___rarg___boxed), 9, 0);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid pattern, constructor or constant marked with '[matchPattern]' expected");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___rarg___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___rarg___closed__2;
x_10 = l_Lean_throwError___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___spec__1___rarg(x_9, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___rarg), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwError___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_7, 3);
x_11 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_5, x_6, x_7, x_8, x_9);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_13);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_11);
lean_inc(x_10);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___spec__1___rarg___boxed), 9, 0);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid pattern");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___rarg___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___rarg___closed__2;
x_10 = l_Lean_throwError___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___spec__1___rarg(x_9, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___rarg), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwError___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_Context_paramDeclIdx___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(0u);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_Context_newArgs___default() {
_start:
{
lean_object* x_1; 
x_1 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_mkMVarSyntax___closed__3;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_instInhabitedContext___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_box(0);
x_4 = 0;
x_5 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_mkMVarSyntax___closed__3;
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_1);
lean_ctor_set(x_7, 2, x_5);
lean_ctor_set(x_7, 3, x_6);
lean_ctor_set(x_7, 4, x_5);
lean_ctor_set(x_7, 5, x_2);
lean_ctor_set(x_7, 6, x_5);
lean_ctor_set_uint8(x_7, sizeof(void*)*7, x_4);
lean_ctor_set_uint8(x_7, sizeof(void*)*7 + 1, x_4);
return x_7;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_instInhabitedContext() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_CollectPatternVars_instInhabitedContext___closed__1;
return x_1;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_isDone(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = lean_array_get_size(x_2);
x_4 = lean_ctor_get(x_1, 3);
x_5 = lean_nat_dec_le(x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_isDone___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_isDone(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_7, 3);
x_11 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_5, x_6, x_7, x_8, x_9);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_13);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_11);
lean_inc(x_10);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 3);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_Lean_SourceInfo_fromRef(x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___spec__2___rarg___boxed), 3, 0);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("too many arguments");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Parser");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__4;
x_2 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Term");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__6;
x_2 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("explicit");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__8;
x_2 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__9;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("@");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_1, 4);
lean_inc(x_10);
x_11 = l_Array_isEmpty___rarg(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_1);
x_12 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__2;
x_13 = l_Lean_throwError___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___spec__1(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_1, 5);
lean_inc(x_14);
x_15 = l_List_isEmpty___rarg(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_1);
x_16 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__2;
x_17 = l_Lean_throwError___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___spec__1(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
lean_inc(x_7);
x_18 = l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___spec__2___rarg(x_7, x_8, x_9);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_20);
lean_dec(x_7);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Lean_Elab_Term_getMainModule___rarg(x_8, x_22);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
x_26 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__11;
x_27 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_27, 0, x_19);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_ctor_get(x_1, 0);
lean_inc(x_28);
x_29 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__12;
x_30 = lean_array_push(x_29, x_27);
x_31 = lean_array_push(x_30, x_28);
x_32 = lean_box(2);
x_33 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__10;
x_34 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_34, 2, x_31);
x_35 = lean_ctor_get(x_1, 6);
lean_inc(x_35);
lean_dec(x_1);
x_36 = l_Lean_Syntax_mkApp(x_34, x_35);
lean_ctor_set(x_23, 0, x_36);
return x_23;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_37 = lean_ctor_get(x_23, 1);
lean_inc(x_37);
lean_dec(x_23);
x_38 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__11;
x_39 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_39, 0, x_19);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_ctor_get(x_1, 0);
lean_inc(x_40);
x_41 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__12;
x_42 = lean_array_push(x_41, x_39);
x_43 = lean_array_push(x_42, x_40);
x_44 = lean_box(2);
x_45 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__10;
x_46 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set(x_46, 2, x_43);
x_47 = lean_ctor_get(x_1, 6);
lean_inc(x_47);
lean_dec(x_1);
x_48 = l_Lean_Syntax_mkApp(x_46, x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_37);
return x_49;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwError___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___spec__2___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_isNextArgAccessible(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 3);
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_array_get_size(x_4);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; 
x_8 = lean_array_fget(x_4, x_3);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
x_11 = l_Lean_BinderInfo_isExplicit(x_10);
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_1, 3);
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_ctor_get(x_13, 3);
x_15 = lean_nat_dec_le(x_14, x_12);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_isNextArgAccessible___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_isNextArgAccessible(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_getNextParam___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_instInhabitedName;
x_2 = l_Lean_instInhabitedBinderInfo;
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_getNextParam(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_1, 2);
x_4 = lean_ctor_get(x_1, 3);
x_5 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_getNextParam___closed__1;
x_6 = lean_array_get(x_5, x_3, x_4);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_add(x_4, x_7);
lean_dec(x_4);
lean_ctor_set(x_1, 3, x_8);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_1);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
x_12 = lean_ctor_get_uint8(x_1, sizeof(void*)*7);
x_13 = lean_ctor_get_uint8(x_1, sizeof(void*)*7 + 1);
x_14 = lean_ctor_get(x_1, 2);
x_15 = lean_ctor_get(x_1, 3);
x_16 = lean_ctor_get(x_1, 4);
x_17 = lean_ctor_get(x_1, 5);
x_18 = lean_ctor_get(x_1, 6);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
x_19 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_getNextParam___closed__1;
x_20 = lean_array_get(x_19, x_14, x_15);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_15, x_21);
lean_dec(x_15);
x_23 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_23, 0, x_10);
lean_ctor_set(x_23, 1, x_11);
lean_ctor_set(x_23, 2, x_14);
lean_ctor_set(x_23, 3, x_22);
lean_ctor_set(x_23, 4, x_16);
lean_ctor_set(x_23, 5, x_17);
lean_ctor_set(x_23, 6, x_18);
lean_ctor_set_uint8(x_23, sizeof(void*)*7, x_12);
lean_ctor_set_uint8(x_23, sizeof(void*)*7 + 1, x_13);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_7, 3);
x_11 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_5, x_6, x_7, x_8, x_9);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_13);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_11);
lean_inc(x_10);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 3);
x_13 = l_Lean_replaceRef(x_1, x_12);
lean_dec(x_12);
lean_dec(x_1);
lean_ctor_set(x_8, 3, x_13);
x_14 = l_Lean_throwError___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___spec__1(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_15 = lean_ctor_get(x_8, 0);
x_16 = lean_ctor_get(x_8, 1);
x_17 = lean_ctor_get(x_8, 2);
x_18 = lean_ctor_get(x_8, 3);
x_19 = lean_ctor_get(x_8, 4);
x_20 = lean_ctor_get(x_8, 5);
x_21 = lean_ctor_get(x_8, 6);
x_22 = lean_ctor_get(x_8, 7);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_8);
x_23 = l_Lean_replaceRef(x_1, x_18);
lean_dec(x_18);
lean_dec(x_1);
x_24 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_24, 0, x_15);
lean_ctor_set(x_24, 1, x_16);
lean_ctor_set(x_24, 2, x_17);
lean_ctor_set(x_24, 3, x_23);
lean_ctor_set(x_24, 4, x_19);
lean_ctor_set(x_24, 5, x_20);
lean_ctor_set(x_24, 6, x_21);
lean_ctor_set(x_24, 7, x_22);
x_25 = l_Lean_throwError___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___spec__1(x_2, x_3, x_4, x_5, x_6, x_7, x_24, x_9, x_10);
lean_dec(x_9);
lean_dec(x_24);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_12 = lean_st_ref_get(x_10, x_11);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_st_ref_take(x_4, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = lean_box(0);
lean_inc(x_1);
x_19 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_17, x_1, x_18);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_dec(x_15);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_1);
x_22 = lean_array_push(x_20, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_19);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_st_ref_set(x_4, x_23, x_16);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
lean_ctor_set(x_24, 0, x_2);
return x_24;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_2);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid pattern, variable '");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' occurred more than once");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__2___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_dec(x_3);
x_12 = lean_st_ref_get(x_10, x_11);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_st_ref_get(x_4, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_NameSet_contains(x_17, x_1);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_box(0);
x_20 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__1(x_1, x_2, x_19, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_16);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
lean_dec(x_2);
x_21 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_21, 0, x_1);
x_22 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__2___closed__2;
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__2___closed__4;
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_throwError___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___spec__1(x_25, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_16);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
return x_26;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_26);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid pattern variable, must be atomic");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
lean_dec(x_2);
x_11 = l_Lean_Syntax_getId(x_1);
lean_inc(x_11);
x_12 = lean_erase_macro_scopes(x_11);
x_13 = l_Lean_Name_isAtomic(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
lean_dec(x_11);
lean_dec(x_1);
x_14 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__3___closed__2;
x_15 = l_Lean_throwError___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___spec__1(x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_object* x_20; lean_object* x_21; 
x_20 = lean_box(0);
x_21 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__2(x_11, x_1, x_20, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_21;
}
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("identifier expected");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = l_Lean_Syntax_isIdent(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___closed__2;
x_12 = l_Lean_throwErrorAt___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___spec__2(x_1, x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
return x_12;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_12);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_box(0);
x_18 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__3(x_1, x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwError___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 3);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_Lean_SourceInfo_fromRef(x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___spec__1___rarg___boxed), 3, 0);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Name.anonymous");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Name");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("anonymous");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__5;
x_2 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__6;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__4;
x_2 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__8;
x_2 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__6;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__9;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__10;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("app");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__8;
x_2 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__12;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Name.str");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__14;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__14;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__15;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("str");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__5;
x_2 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__17;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__8;
x_2 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__17;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__19;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__20;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__22() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("null");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__22;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__24() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("hole");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__8;
x_2 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__24;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__26() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__28() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Name.num");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__28;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__28;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__29;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__31() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("num");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__5;
x_2 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__31;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__8;
x_2 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__31;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__34() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__33;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__35() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__34;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
lean_inc(x_6);
x_9 = l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___spec__1___rarg(x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Elab_Term_getCurrMacroScope(x_2, x_3, x_4, x_5, x_6, x_7, x_11);
lean_dec(x_6);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Elab_Term_getMainModule___rarg(x_7, x_14);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__7;
x_19 = l_Lean_addMacroScope(x_17, x_18, x_13);
x_20 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__3;
x_21 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__11;
x_22 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_22, 0, x_10);
lean_ctor_set(x_22, 1, x_20);
lean_ctor_set(x_22, 2, x_19);
lean_ctor_set(x_22, 3, x_21);
lean_ctor_set(x_15, 0, x_22);
return x_15;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_15, 0);
x_24 = lean_ctor_get(x_15, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_15);
x_25 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__7;
x_26 = l_Lean_addMacroScope(x_23, x_25, x_13);
x_27 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__3;
x_28 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__11;
x_29 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_29, 0, x_10);
lean_ctor_set(x_29, 1, x_27);
lean_ctor_set(x_29, 2, x_26);
lean_ctor_set(x_29, 3, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_24);
return x_30;
}
}
case 1:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_31 = lean_ctor_get(x_1, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_1, 1);
lean_inc(x_32);
lean_dec(x_1);
lean_inc(x_6);
x_33 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern(x_31, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
lean_inc(x_6);
x_36 = l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___spec__1___rarg(x_6, x_7, x_35);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Lean_Elab_Term_getCurrMacroScope(x_2, x_3, x_4, x_5, x_6, x_7, x_38);
lean_dec(x_6);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Lean_Elab_Term_getMainModule___rarg(x_7, x_41);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_44 = lean_ctor_get(x_42, 0);
x_45 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__18;
x_46 = l_Lean_addMacroScope(x_44, x_45, x_40);
x_47 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__16;
x_48 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__21;
lean_inc(x_37);
x_49 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_49, 0, x_37);
lean_ctor_set(x_49, 1, x_47);
lean_ctor_set(x_49, 2, x_46);
lean_ctor_set(x_49, 3, x_48);
x_50 = lean_box(2);
x_51 = l_Lean_Syntax_mkStrLit(x_32, x_50);
lean_dec(x_32);
x_52 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__26;
x_53 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_53, 0, x_37);
lean_ctor_set(x_53, 1, x_52);
x_54 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_mkMVarSyntax___closed__4;
x_55 = lean_array_push(x_54, x_53);
x_56 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__25;
x_57 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_57, 0, x_50);
lean_ctor_set(x_57, 1, x_56);
lean_ctor_set(x_57, 2, x_55);
x_58 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__27;
x_59 = lean_array_push(x_58, x_34);
x_60 = lean_array_push(x_59, x_51);
x_61 = lean_array_push(x_60, x_57);
x_62 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__23;
x_63 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_63, 0, x_50);
lean_ctor_set(x_63, 1, x_62);
lean_ctor_set(x_63, 2, x_61);
x_64 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__12;
x_65 = lean_array_push(x_64, x_49);
x_66 = lean_array_push(x_65, x_63);
x_67 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__13;
x_68 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_68, 0, x_50);
lean_ctor_set(x_68, 1, x_67);
lean_ctor_set(x_68, 2, x_66);
lean_ctor_set(x_42, 0, x_68);
return x_42;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_69 = lean_ctor_get(x_42, 0);
x_70 = lean_ctor_get(x_42, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_42);
x_71 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__18;
x_72 = l_Lean_addMacroScope(x_69, x_71, x_40);
x_73 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__16;
x_74 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__21;
lean_inc(x_37);
x_75 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_75, 0, x_37);
lean_ctor_set(x_75, 1, x_73);
lean_ctor_set(x_75, 2, x_72);
lean_ctor_set(x_75, 3, x_74);
x_76 = lean_box(2);
x_77 = l_Lean_Syntax_mkStrLit(x_32, x_76);
lean_dec(x_32);
x_78 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__26;
x_79 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_79, 0, x_37);
lean_ctor_set(x_79, 1, x_78);
x_80 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_mkMVarSyntax___closed__4;
x_81 = lean_array_push(x_80, x_79);
x_82 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__25;
x_83 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_83, 0, x_76);
lean_ctor_set(x_83, 1, x_82);
lean_ctor_set(x_83, 2, x_81);
x_84 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__27;
x_85 = lean_array_push(x_84, x_34);
x_86 = lean_array_push(x_85, x_77);
x_87 = lean_array_push(x_86, x_83);
x_88 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__23;
x_89 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_89, 0, x_76);
lean_ctor_set(x_89, 1, x_88);
lean_ctor_set(x_89, 2, x_87);
x_90 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__12;
x_91 = lean_array_push(x_90, x_75);
x_92 = lean_array_push(x_91, x_89);
x_93 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__13;
x_94 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_94, 0, x_76);
lean_ctor_set(x_94, 1, x_93);
lean_ctor_set(x_94, 2, x_92);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_70);
return x_95;
}
}
default: 
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_96 = lean_ctor_get(x_1, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_1, 1);
lean_inc(x_97);
lean_dec(x_1);
lean_inc(x_6);
x_98 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern(x_96, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
lean_inc(x_6);
x_101 = l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___spec__1___rarg(x_6, x_7, x_100);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
x_104 = l_Lean_Elab_Term_getCurrMacroScope(x_2, x_3, x_4, x_5, x_6, x_7, x_103);
lean_dec(x_6);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
x_107 = l_Lean_Elab_Term_getMainModule___rarg(x_7, x_106);
x_108 = !lean_is_exclusive(x_107);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_109 = lean_ctor_get(x_107, 0);
x_110 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__32;
x_111 = l_Lean_addMacroScope(x_109, x_110, x_105);
x_112 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__30;
x_113 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__35;
lean_inc(x_102);
x_114 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_114, 0, x_102);
lean_ctor_set(x_114, 1, x_112);
lean_ctor_set(x_114, 2, x_111);
lean_ctor_set(x_114, 3, x_113);
x_115 = l_Nat_repr(x_97);
x_116 = l_Lean_numLitKind;
x_117 = lean_box(2);
x_118 = l_Lean_Syntax_mkLit(x_116, x_115, x_117);
x_119 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__26;
x_120 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_120, 0, x_102);
lean_ctor_set(x_120, 1, x_119);
x_121 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_mkMVarSyntax___closed__4;
x_122 = lean_array_push(x_121, x_120);
x_123 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__25;
x_124 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_124, 0, x_117);
lean_ctor_set(x_124, 1, x_123);
lean_ctor_set(x_124, 2, x_122);
x_125 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__27;
x_126 = lean_array_push(x_125, x_99);
x_127 = lean_array_push(x_126, x_118);
x_128 = lean_array_push(x_127, x_124);
x_129 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__23;
x_130 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_130, 0, x_117);
lean_ctor_set(x_130, 1, x_129);
lean_ctor_set(x_130, 2, x_128);
x_131 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__12;
x_132 = lean_array_push(x_131, x_114);
x_133 = lean_array_push(x_132, x_130);
x_134 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__13;
x_135 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_135, 0, x_117);
lean_ctor_set(x_135, 1, x_134);
lean_ctor_set(x_135, 2, x_133);
lean_ctor_set(x_107, 0, x_135);
return x_107;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_136 = lean_ctor_get(x_107, 0);
x_137 = lean_ctor_get(x_107, 1);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_107);
x_138 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__32;
x_139 = l_Lean_addMacroScope(x_136, x_138, x_105);
x_140 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__30;
x_141 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__35;
lean_inc(x_102);
x_142 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_142, 0, x_102);
lean_ctor_set(x_142, 1, x_140);
lean_ctor_set(x_142, 2, x_139);
lean_ctor_set(x_142, 3, x_141);
x_143 = l_Nat_repr(x_97);
x_144 = l_Lean_numLitKind;
x_145 = lean_box(2);
x_146 = l_Lean_Syntax_mkLit(x_144, x_143, x_145);
x_147 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__26;
x_148 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_148, 0, x_102);
lean_ctor_set(x_148, 1, x_147);
x_149 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_mkMVarSyntax___closed__4;
x_150 = lean_array_push(x_149, x_148);
x_151 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__25;
x_152 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_152, 0, x_145);
lean_ctor_set(x_152, 1, x_151);
lean_ctor_set(x_152, 2, x_150);
x_153 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__27;
x_154 = lean_array_push(x_153, x_99);
x_155 = lean_array_push(x_154, x_146);
x_156 = lean_array_push(x_155, x_152);
x_157 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__23;
x_158 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_158, 0, x_145);
lean_ctor_set(x_158, 1, x_157);
lean_ctor_set(x_158, 2, x_156);
x_159 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__12;
x_160 = lean_array_push(x_159, x_142);
x_161 = lean_array_push(x_160, x_158);
x_162 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__13;
x_163 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_163, 0, x_145);
lean_ctor_set(x_163, 1, x_162);
lean_ctor_set(x_163, 2, x_161);
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_137);
return x_164;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___spec__1___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
static lean_object* _init_l_Lean_Elab_throwIllFormedSyntax___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_quotedNameToPattern___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ill-formed syntax");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_throwIllFormedSyntax___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_quotedNameToPattern___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_throwIllFormedSyntax___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_quotedNameToPattern___spec__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwIllFormedSyntax___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_quotedNameToPattern___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Elab_throwIllFormedSyntax___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_quotedNameToPattern___spec__1___closed__2;
x_9 = l_Lean_throwError___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__11(x_8, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_quotedNameToPattern(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
lean_dec(x_1);
x_11 = l_Lean_Syntax_isNameLit_x3f(x_10);
lean_dec(x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = l_Lean_Elab_throwIllFormedSyntax___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_quotedNameToPattern___spec__1(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwIllFormedSyntax___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_quotedNameToPattern___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_throwIllFormedSyntax___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_quotedNameToPattern___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 3);
x_12 = l_Lean_replaceRef(x_1, x_11);
lean_dec(x_11);
lean_ctor_set(x_7, 3, x_12);
x_13 = l_Lean_throwError___at_Lean_Elab_Term_expandDeclId___spec__11(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_7, 1);
x_16 = lean_ctor_get(x_7, 2);
x_17 = lean_ctor_get(x_7, 3);
x_18 = lean_ctor_get(x_7, 4);
x_19 = lean_ctor_get(x_7, 5);
x_20 = lean_ctor_get(x_7, 6);
x_21 = lean_ctor_get(x_7, 7);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_7);
x_22 = l_Lean_replaceRef(x_1, x_17);
lean_dec(x_17);
x_23 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_23, 0, x_14);
lean_ctor_set(x_23, 1, x_15);
lean_ctor_set(x_23, 2, x_16);
lean_ctor_set(x_23, 3, x_22);
lean_ctor_set(x_23, 4, x_18);
lean_ctor_set(x_23, 5, x_19);
lean_ctor_set(x_23, 6, x_20);
lean_ctor_set(x_23, 7, x_21);
x_24 = l_Lean_throwError___at_Lean_Elab_Term_expandDeclId___spec__11(x_2, x_3, x_4, x_5, x_6, x_23, x_8, x_9);
lean_dec(x_23);
return x_24;
}
}
}
static lean_object* _init_l_Lean_throwUnknownConstant___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unknown constant '");
return x_1;
}
}
static lean_object* _init_l_Lean_throwUnknownConstant___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__6___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwUnknownConstant___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__6___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwUnknownConstant___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__6___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("'");
return x_1;
}
}
static lean_object* _init_l_Lean_throwUnknownConstant___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__6___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwUnknownConstant___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__6___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_box(0);
x_10 = l_Lean_mkConst(x_1, x_9);
x_11 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = l_Lean_throwUnknownConstant___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__6___closed__2;
x_13 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l_Lean_throwUnknownConstant___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__6___closed__4;
x_15 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_throwError___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__1(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstCore___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__5___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_List_mapTRAux___at_Lean_resolveGlobalConstCore___spec__2(x_1, x_2);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstCore___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_inc(x_6);
lean_inc(x_1);
x_9 = l_Lean_resolveGlobalName___at_Lean_Elab_Term_resolveName___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_box(0);
x_13 = l_List_filterAux___at_Lean_resolveGlobalConstCore___spec__1(x_10, x_12);
x_14 = l_List_isEmpty___rarg(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_15 = lean_box(0);
x_16 = l_Lean_resolveGlobalConstCore___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__5___lambda__1(x_13, x_12, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; 
lean_dec(x_13);
x_17 = l_Lean_throwUnknownConstant___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
static lean_object* _init_l_Lean_resolveGlobalConst___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("expected identifier");
return x_1;
}
}
static lean_object* _init_l_Lean_resolveGlobalConst___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_resolveGlobalConst___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__3___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_resolveGlobalConst___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_resolveGlobalConst___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__3___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 3);
lean_inc(x_10);
x_11 = l_List_filterMap___at_Lean_resolveGlobalConst___spec__1(x_10);
x_12 = l_List_isEmpty___rarg(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_8);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_11);
x_14 = !lean_is_exclusive(x_6);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_6, 3);
x_16 = l_Lean_replaceRef(x_1, x_15);
lean_dec(x_15);
lean_dec(x_1);
lean_ctor_set(x_6, 3, x_16);
x_17 = l_Lean_resolveGlobalConstCore___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__5(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_18 = lean_ctor_get(x_6, 0);
x_19 = lean_ctor_get(x_6, 1);
x_20 = lean_ctor_get(x_6, 2);
x_21 = lean_ctor_get(x_6, 3);
x_22 = lean_ctor_get(x_6, 4);
x_23 = lean_ctor_get(x_6, 5);
x_24 = lean_ctor_get(x_6, 6);
x_25 = lean_ctor_get(x_6, 7);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_6);
x_26 = l_Lean_replaceRef(x_1, x_21);
lean_dec(x_21);
lean_dec(x_1);
x_27 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_27, 0, x_18);
lean_ctor_set(x_27, 1, x_19);
lean_ctor_set(x_27, 2, x_20);
lean_ctor_set(x_27, 3, x_26);
lean_ctor_set(x_27, 4, x_22);
lean_ctor_set(x_27, 5, x_23);
lean_ctor_set(x_27, 6, x_24);
lean_ctor_set(x_27, 7, x_25);
x_28 = l_Lean_resolveGlobalConstCore___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__5(x_9, x_2, x_3, x_4, x_5, x_27, x_7, x_8);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = l_Lean_resolveGlobalConst___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__3___closed__3;
x_30 = l_Lean_throwErrorAt___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__4(x_1, x_29, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 3);
x_12 = l_Lean_replaceRef(x_1, x_11);
lean_dec(x_11);
lean_ctor_set(x_7, 3, x_12);
x_13 = l_Lean_throwError___at_Lean_Elab_Term_mkAuxName___spec__1(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_7, 1);
x_16 = lean_ctor_get(x_7, 2);
x_17 = lean_ctor_get(x_7, 3);
x_18 = lean_ctor_get(x_7, 4);
x_19 = lean_ctor_get(x_7, 5);
x_20 = lean_ctor_get(x_7, 6);
x_21 = lean_ctor_get(x_7, 7);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_7);
x_22 = l_Lean_replaceRef(x_1, x_17);
lean_dec(x_17);
x_23 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_23, 0, x_14);
lean_ctor_set(x_23, 1, x_15);
lean_ctor_set(x_23, 2, x_16);
lean_ctor_set(x_23, 3, x_22);
lean_ctor_set(x_23, 4, x_18);
lean_ctor_set(x_23, 5, x_19);
lean_ctor_set(x_23, 6, x_20);
lean_ctor_set(x_23, 7, x_21);
x_24 = l_Lean_throwError___at_Lean_Elab_Term_mkAuxName___spec__1(x_2, x_3, x_4, x_5, x_6, x_23, x_8, x_9);
lean_dec(x_23);
return x_24;
}
}
}
static lean_object* _init_l_Lean_resolveGlobalConstNoOverload___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ambiguous identifier '");
return x_1;
}
}
static lean_object* _init_l_Lean_resolveGlobalConstNoOverload___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("', possible interpretations: ");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverload___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_9 = l_Lean_resolveGlobalConst___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_box(0);
x_13 = 0;
x_14 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
x_15 = l_Lean_Syntax_formatStxAux(x_12, x_13, x_14, x_1);
x_16 = l_Std_Format_defWidth;
x_17 = lean_format_pretty(x_15, x_16);
x_18 = l_Lean_resolveGlobalConstNoOverload___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__2___closed__1;
x_19 = lean_string_append(x_18, x_17);
lean_dec(x_17);
x_20 = l_Lean_resolveGlobalConstNoOverload___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__2___closed__2;
x_21 = lean_string_append(x_19, x_20);
x_22 = lean_box(0);
x_23 = l_List_mapTRAux___at_Lean_resolveGlobalConstNoOverload___spec__1(x_10, x_22);
x_24 = l_List_toString___at_Lean_resolveGlobalConstNoOverloadCore___spec__2(x_23);
x_25 = lean_string_append(x_21, x_24);
lean_dec(x_24);
x_26 = l_Lean_Elab_Term_instToStringPatternVar___closed__2;
x_27 = lean_string_append(x_25, x_26);
x_28 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = l_Lean_throwErrorAt___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__7(x_1, x_29, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_30;
}
else
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_10, 1);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_9);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_9, 0);
lean_dec(x_33);
x_34 = lean_ctor_get(x_10, 0);
lean_inc(x_34);
lean_dec(x_10);
lean_ctor_set(x_9, 0, x_34);
return x_9;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_9, 1);
lean_inc(x_35);
lean_dec(x_9);
x_36 = lean_ctor_get(x_10, 0);
lean_inc(x_36);
lean_dec(x_10);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_31);
x_38 = lean_ctor_get(x_9, 1);
lean_inc(x_38);
lean_dec(x_9);
x_39 = lean_box(0);
x_40 = 0;
x_41 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
x_42 = l_Lean_Syntax_formatStxAux(x_39, x_40, x_41, x_1);
x_43 = l_Std_Format_defWidth;
x_44 = lean_format_pretty(x_42, x_43);
x_45 = l_Lean_resolveGlobalConstNoOverload___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__2___closed__1;
x_46 = lean_string_append(x_45, x_44);
lean_dec(x_44);
x_47 = l_Lean_resolveGlobalConstNoOverload___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__2___closed__2;
x_48 = lean_string_append(x_46, x_47);
x_49 = lean_box(0);
x_50 = l_List_mapTRAux___at_Lean_resolveGlobalConstNoOverload___spec__1(x_10, x_49);
x_51 = l_List_toString___at_Lean_resolveGlobalConstNoOverloadCore___spec__2(x_50);
x_52 = lean_string_append(x_48, x_51);
lean_dec(x_51);
x_53 = l_Lean_Elab_Term_instToStringPatternVar___closed__2;
x_54 = lean_string_append(x_52, x_53);
x_55 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_55, 0, x_54);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_55);
x_57 = l_Lean_throwErrorAt___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__7(x_1, x_56, x_2, x_3, x_4, x_5, x_6, x_7, x_38);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_57;
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_9);
if (x_58 == 0)
{
return x_9;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_9, 0);
x_60 = lean_ctor_get(x_9, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_9);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_1);
x_9 = l_Lean_getConstInfo___at_Lean_Elab_Term_mkConst___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = l_Lean_ConstantInfo_levelParams(x_11);
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = l_List_mapTRAux___at_Lean_mkConstWithLevelParams___spec__1(x_12, x_13);
x_15 = l_Lean_mkConst(x_1, x_14);
lean_ctor_set(x_9, 0, x_15);
return x_9;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_9, 0);
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_9);
x_18 = l_Lean_ConstantInfo_levelParams(x_16);
lean_dec(x_16);
x_19 = lean_box(0);
x_20 = l_List_mapTRAux___at_Lean_mkConstWithLevelParams___spec__1(x_18, x_19);
x_21 = l_Lean_mkConst(x_1, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_17);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_9);
if (x_23 == 0)
{
return x_9;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_9, 0);
x_25 = lean_ctor_get(x_9, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_9);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_resolveGlobalConstNoOverloadWithInfo___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_resolveGlobalConstNoOverloadWithInfo___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_10 = l_Lean_resolveGlobalConstNoOverload___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__2(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_st_ref_get(x_8, x_12);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_st_ref_get(x_4, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 5);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_ctor_get_uint8(x_17, sizeof(void*)*2);
lean_dec(x_17);
if (x_18 == 0)
{
uint8_t x_19; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_15);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_15, 0);
lean_dec(x_20);
lean_ctor_set(x_15, 0, x_11);
return x_15;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_dec(x_15);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_11);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
lean_dec(x_15);
lean_inc(x_3);
lean_inc(x_11);
x_24 = l_Lean_mkConstWithLevelParams___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__8(x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_1);
x_29 = l_Lean_LocalContext_empty;
x_30 = 0;
x_31 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_29);
lean_ctor_set(x_31, 2, x_2);
lean_ctor_set(x_31, 3, x_25);
lean_ctor_set_uint8(x_31, sizeof(void*)*4, x_30);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_Term_addDotCompletionInfo___spec__2(x_32, x_3, x_4, x_5, x_6, x_7, x_8, x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_33, 0);
lean_dec(x_35);
lean_ctor_set(x_33, 0, x_11);
return x_33;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_11);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
else
{
uint8_t x_38; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_24);
if (x_38 == 0)
{
return x_24;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_24, 0);
x_40 = lean_ctor_get(x_24, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_24);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_10);
if (x_42 == 0)
{
return x_10;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_10, 0);
x_44 = lean_ctor_get(x_10, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_10);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_unsigned_to_nat(2u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
x_11 = lean_box(0);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_12 = l_Lean_Elab_resolveGlobalConstNoOverloadWithInfo___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__1(x_10, x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_12, 0);
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_12);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwErrorAt___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwUnknownConstant___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstCore___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__5___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_resolveGlobalConstCore___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__5___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwErrorAt___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_mkConstWithLevelParams___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_resolveGlobalConstNoOverloadWithInfo___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_resolveGlobalConstNoOverloadWithInfo___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = 1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_11 = l_Lean_Elab_Term_expandApp(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_ctor_get(x_14, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
x_21 = l_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore(x_16, x_17, x_18, x_20, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_15);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_22 = !lean_is_exclusive(x_11);
if (x_22 == 0)
{
return x_11;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_11, 0);
x_24 = lean_ctor_get(x_11, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_11);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_7, 3);
x_11 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_5, x_6, x_7, x_8, x_9);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_13);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_11);
lean_inc(x_10);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_st_ref_get(x_8, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_1);
x_15 = lean_environment_find(x_14, x_1);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_free_object(x_10);
x_16 = lean_box(0);
x_17 = l_Lean_mkConst(x_1, x_16);
x_18 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = l_Lean_throwUnknownConstant___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__6___closed__2;
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = l_Lean_throwUnknownConstant___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__6___closed__4;
x_22 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_throwError___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___spec__2(x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_13);
return x_23;
}
else
{
lean_object* x_24; 
lean_dec(x_1);
x_24 = lean_ctor_get(x_15, 0);
lean_inc(x_24);
lean_dec(x_15);
lean_ctor_set(x_10, 0, x_24);
return x_10;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_10, 0);
x_26 = lean_ctor_get(x_10, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_10);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
lean_dec(x_25);
lean_inc(x_1);
x_28 = lean_environment_find(x_27, x_1);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_29 = lean_box(0);
x_30 = l_Lean_mkConst(x_1, x_29);
x_31 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = l_Lean_throwUnknownConstant___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__6___closed__2;
x_33 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
x_34 = l_Lean_throwUnknownConstant___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__6___closed__4;
x_35 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_throwError___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___spec__2(x_35, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_26);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_1);
x_37 = lean_ctor_get(x_28, 0);
lean_inc(x_37);
lean_dec(x_28);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_26);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___spec__3(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_2, x_1);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_7);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_array_uget(x_3, x_2);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_uset(x_3, x_2, x_15);
lean_inc(x_7);
x_17 = l_Lean_Meta_getFVarLocalDecl(x_14, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; lean_object* x_26; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_LocalDecl_userName(x_18);
x_21 = l_Lean_LocalDecl_binderInfo(x_18);
lean_dec(x_18);
x_22 = lean_box(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_22);
x_24 = 1;
x_25 = lean_usize_add(x_2, x_24);
x_26 = lean_array_uset(x_16, x_2, x_23);
x_2 = x_25;
x_3 = x_26;
x_11 = x_19;
goto _start;
}
else
{
uint8_t x_28; 
lean_dec(x_16);
lean_dec(x_7);
x_28 = !lean_is_exclusive(x_17);
if (x_28 == 0)
{
return x_17;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_17, 0);
x_30 = lean_ctor_get(x_17, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_17);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___spec__4___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = lean_apply_10(x_1, x_5, x_6, x_2, x_3, x_4, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___spec__4___rarg___lambda__1), 11, 4);
lean_closure_set(x_11, 0, x_2);
lean_closure_set(x_11, 1, x_3);
lean_closure_set(x_11, 2, x_4);
lean_closure_set(x_11, 3, x_5);
x_12 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp___rarg(x_1, x_11, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
return x_12;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_12, 0);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_12);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___spec__4___rarg), 10, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_7, 3);
x_11 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_5, x_6, x_7, x_8, x_9);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_13);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_11);
lean_inc(x_10);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; 
lean_dec(x_2);
x_11 = lean_array_get_size(x_1);
x_12 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_13 = 0;
x_14 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___spec__3(x_12, x_13, x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("pattern");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___lambda__1), 10, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_matchPatternAttr;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___lambda__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_4, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
lean_dec(x_4);
x_15 = l_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___lambda__2___closed__1;
x_16 = 1;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_13);
x_17 = l_Lean_Elab_Term_resolveId_x3f(x_13, x_15, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_3);
lean_dec(x_2);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___rarg(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_19);
return x_20;
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_18, 0);
if (lean_obj_tag(x_22) == 4)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_dec(x_17);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_24);
x_25 = l_Lean_getConstInfo___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___spec__1(x_24, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_23);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_ConstantInfo_type(x_26);
x_29 = l_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___lambda__2___closed__2;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_30 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___spec__4___rarg(x_28, x_29, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_27);
if (lean_obj_tag(x_30) == 0)
{
if (lean_obj_tag(x_26) == 6)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; 
lean_dec(x_24);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_26, 0);
lean_inc(x_33);
lean_dec(x_26);
lean_ctor_set(x_18, 0, x_33);
x_34 = lean_unsigned_to_nat(0u);
x_35 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_mkMVarSyntax___closed__3;
x_36 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_36, 0, x_13);
lean_ctor_set(x_36, 1, x_18);
lean_ctor_set(x_36, 2, x_31);
lean_ctor_set(x_36, 3, x_34);
lean_ctor_set(x_36, 4, x_2);
lean_ctor_set(x_36, 5, x_3);
lean_ctor_set(x_36, 6, x_35);
x_37 = lean_unbox(x_14);
lean_dec(x_14);
lean_ctor_set_uint8(x_36, sizeof(void*)*7, x_37);
lean_ctor_set_uint8(x_36, sizeof(void*)*7 + 1, x_1);
x_38 = l_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppContext(x_36, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_32);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
lean_dec(x_26);
lean_free_object(x_18);
x_39 = lean_ctor_get(x_30, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_30, 1);
lean_inc(x_40);
lean_dec(x_30);
x_41 = lean_st_ref_get(x_11, x_40);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_ctor_get(x_42, 0);
lean_inc(x_44);
lean_dec(x_42);
x_45 = l_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___lambda__2___closed__3;
x_46 = l_Lean_TagAttribute_hasTag(x_45, x_44, x_24);
if (x_46 == 0)
{
lean_object* x_47; 
lean_dec(x_39);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_3);
lean_dec(x_2);
x_47 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___rarg(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_43);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; 
x_48 = lean_box(0);
x_49 = lean_unsigned_to_nat(0u);
x_50 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_mkMVarSyntax___closed__3;
x_51 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_51, 0, x_13);
lean_ctor_set(x_51, 1, x_48);
lean_ctor_set(x_51, 2, x_39);
lean_ctor_set(x_51, 3, x_49);
lean_ctor_set(x_51, 4, x_2);
lean_ctor_set(x_51, 5, x_3);
lean_ctor_set(x_51, 6, x_50);
x_52 = lean_unbox(x_14);
lean_dec(x_14);
lean_ctor_set_uint8(x_51, sizeof(void*)*7, x_52);
lean_ctor_set_uint8(x_51, sizeof(void*)*7 + 1, x_1);
x_53 = l_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppContext(x_51, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_43);
return x_53;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_26);
lean_dec(x_24);
lean_free_object(x_18);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_54 = !lean_is_exclusive(x_30);
if (x_54 == 0)
{
return x_30;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_30, 0);
x_56 = lean_ctor_get(x_30, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_30);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_24);
lean_free_object(x_18);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_58 = !lean_is_exclusive(x_25);
if (x_58 == 0)
{
return x_25;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_25, 0);
x_60 = lean_ctor_get(x_25, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_25);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; 
lean_free_object(x_18);
lean_dec(x_22);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_3);
lean_dec(x_2);
x_62 = lean_ctor_get(x_17, 1);
lean_inc(x_62);
lean_dec(x_17);
x_63 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___rarg(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_62);
return x_63;
}
}
else
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_18, 0);
lean_inc(x_64);
lean_dec(x_18);
if (lean_obj_tag(x_64) == 4)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_17, 1);
lean_inc(x_65);
lean_dec(x_17);
x_66 = lean_ctor_get(x_64, 0);
lean_inc(x_66);
lean_dec(x_64);
lean_inc(x_66);
x_67 = l_Lean_getConstInfo___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___spec__1(x_66, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_65);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = l_Lean_ConstantInfo_type(x_68);
x_71 = l_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___lambda__2___closed__2;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_72 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___spec__4___rarg(x_70, x_71, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_69);
if (lean_obj_tag(x_72) == 0)
{
if (lean_obj_tag(x_68) == 6)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; 
lean_dec(x_66);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_ctor_get(x_68, 0);
lean_inc(x_75);
lean_dec(x_68);
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_75);
x_77 = lean_unsigned_to_nat(0u);
x_78 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_mkMVarSyntax___closed__3;
x_79 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_79, 0, x_13);
lean_ctor_set(x_79, 1, x_76);
lean_ctor_set(x_79, 2, x_73);
lean_ctor_set(x_79, 3, x_77);
lean_ctor_set(x_79, 4, x_2);
lean_ctor_set(x_79, 5, x_3);
lean_ctor_set(x_79, 6, x_78);
x_80 = lean_unbox(x_14);
lean_dec(x_14);
lean_ctor_set_uint8(x_79, sizeof(void*)*7, x_80);
lean_ctor_set_uint8(x_79, sizeof(void*)*7 + 1, x_1);
x_81 = l_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppContext(x_79, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_74);
return x_81;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
lean_dec(x_68);
x_82 = lean_ctor_get(x_72, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_72, 1);
lean_inc(x_83);
lean_dec(x_72);
x_84 = lean_st_ref_get(x_11, x_83);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = lean_ctor_get(x_85, 0);
lean_inc(x_87);
lean_dec(x_85);
x_88 = l_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___lambda__2___closed__3;
x_89 = l_Lean_TagAttribute_hasTag(x_88, x_87, x_66);
if (x_89 == 0)
{
lean_object* x_90; 
lean_dec(x_82);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_3);
lean_dec(x_2);
x_90 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___rarg(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_86);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; lean_object* x_96; 
x_91 = lean_box(0);
x_92 = lean_unsigned_to_nat(0u);
x_93 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_mkMVarSyntax___closed__3;
x_94 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_94, 0, x_13);
lean_ctor_set(x_94, 1, x_91);
lean_ctor_set(x_94, 2, x_82);
lean_ctor_set(x_94, 3, x_92);
lean_ctor_set(x_94, 4, x_2);
lean_ctor_set(x_94, 5, x_3);
lean_ctor_set(x_94, 6, x_93);
x_95 = lean_unbox(x_14);
lean_dec(x_14);
lean_ctor_set_uint8(x_94, sizeof(void*)*7, x_95);
lean_ctor_set_uint8(x_94, sizeof(void*)*7 + 1, x_1);
x_96 = l_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppContext(x_94, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_86);
return x_96;
}
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_68);
lean_dec(x_66);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_97 = lean_ctor_get(x_72, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_72, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_99 = x_72;
} else {
 lean_dec_ref(x_72);
 x_99 = lean_box(0);
}
if (lean_is_scalar(x_99)) {
 x_100 = lean_alloc_ctor(1, 2, 0);
} else {
 x_100 = x_99;
}
lean_ctor_set(x_100, 0, x_97);
lean_ctor_set(x_100, 1, x_98);
return x_100;
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_66);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_101 = lean_ctor_get(x_67, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_67, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_103 = x_67;
} else {
 lean_dec_ref(x_67);
 x_103 = lean_box(0);
}
if (lean_is_scalar(x_103)) {
 x_104 = lean_alloc_ctor(1, 2, 0);
} else {
 x_104 = x_103;
}
lean_ctor_set(x_104, 0, x_101);
lean_ctor_set(x_104, 1, x_102);
return x_104;
}
}
else
{
lean_object* x_105; lean_object* x_106; 
lean_dec(x_64);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_3);
lean_dec(x_2);
x_105 = lean_ctor_get(x_17, 1);
lean_inc(x_105);
lean_dec(x_17);
x_106 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___rarg(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_105);
return x_106;
}
}
}
}
else
{
uint8_t x_107; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_107 = !lean_is_exclusive(x_17);
if (x_107 == 0)
{
return x_17;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_17, 0);
x_109 = lean_ctor_get(x_17, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_17);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ident");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_array_to_list(lean_box(0), x_3);
x_14 = l_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___closed__2;
lean_inc(x_1);
x_15 = l_Lean_Syntax_isOfKind(x_1, x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__10;
lean_inc(x_1);
x_17 = l_Lean_Syntax_isOfKind(x_1, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_dec(x_13);
lean_dec(x_2);
lean_dec(x_1);
x_18 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___closed__2;
x_19 = l_Lean_throwError___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___spec__5(x_18, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
return x_19;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_19);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_unsigned_to_nat(1u);
x_25 = l_Lean_Syntax_getArg(x_1, x_24);
lean_dec(x_1);
lean_inc(x_25);
x_26 = l_Lean_Syntax_isOfKind(x_25, x_14);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
lean_dec(x_25);
lean_dec(x_13);
lean_dec(x_2);
x_27 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___closed__2;
x_28 = l_Lean_throwError___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___spec__5(x_27, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = 1;
x_34 = lean_box(x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_25);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___lambda__2(x_4, x_2, x_13, x_35, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_36;
}
}
}
else
{
uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = 0;
x_38 = lean_box(x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_1);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___lambda__2(x_4, x_2, x_13, x_39, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_40;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppContext___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_name_eq(x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppContext___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppContext), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppContext(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_isDone(x_1);
if (x_10 == 0)
{
uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_11 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_isNextArgAccessible(x_1);
x_12 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_getNextParam(x_1);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
x_17 = lean_ctor_get_uint8(x_13, sizeof(void*)*7);
x_18 = lean_ctor_get_uint8(x_13, sizeof(void*)*7 + 1);
x_19 = lean_ctor_get(x_13, 2);
lean_inc(x_19);
x_20 = lean_ctor_get(x_13, 3);
lean_inc(x_20);
x_21 = lean_ctor_get(x_13, 4);
lean_inc(x_21);
x_22 = lean_ctor_get(x_13, 5);
lean_inc(x_22);
x_23 = lean_ctor_get(x_13, 6);
lean_inc(x_23);
lean_inc(x_14);
x_24 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppContext___lambda__1___boxed), 2, 1);
lean_closure_set(x_24, 0, x_14);
x_25 = lean_array_get_size(x_21);
x_26 = lean_unsigned_to_nat(0u);
x_27 = l_Array_findIdx_x3f_loop___rarg(x_21, x_24, x_25, x_26, lean_box(0));
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_15);
x_28 = l_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppContext___closed__1;
x_29 = lean_ctor_get(x_14, 1);
lean_inc(x_29);
lean_dec(x_14);
switch (lean_obj_tag(x_29)) {
case 0:
{
lean_object* x_30; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_30 = l_Lean_Elab_Term_CollectPatternVars_collect_processExplicitArg(x_11, x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_apply_9(x_28, x_31, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_32);
return x_33;
}
else
{
uint8_t x_34; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_34 = !lean_is_exclusive(x_30);
if (x_34 == 0)
{
return x_30;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_30, 0);
x_36 = lean_ctor_get(x_30, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_30);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
case 4:
{
lean_object* x_38; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_38 = l_Lean_Elab_Term_CollectPatternVars_collect_processExplicitArg(x_11, x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_apply_9(x_28, x_39, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_40);
return x_41;
}
else
{
uint8_t x_42; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_42 = !lean_is_exclusive(x_38);
if (x_42 == 0)
{
return x_38;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_38, 0);
x_44 = lean_ctor_get(x_38, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_38);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
default: 
{
lean_object* x_46; 
lean_dec(x_29);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_46 = l_Lean_Elab_Term_CollectPatternVars_collect_processImplicitArg(x_11, x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_apply_9(x_28, x_47, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_48);
return x_49;
}
else
{
uint8_t x_50; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_50 = !lean_is_exclusive(x_46);
if (x_50 == 0)
{
return x_46;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_46, 0);
x_52 = lean_ctor_get(x_46, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_46);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_14);
x_54 = !lean_is_exclusive(x_13);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_55 = lean_ctor_get(x_13, 6);
lean_dec(x_55);
x_56 = lean_ctor_get(x_13, 5);
lean_dec(x_56);
x_57 = lean_ctor_get(x_13, 4);
lean_dec(x_57);
x_58 = lean_ctor_get(x_13, 3);
lean_dec(x_58);
x_59 = lean_ctor_get(x_13, 2);
lean_dec(x_59);
x_60 = lean_ctor_get(x_13, 1);
lean_dec(x_60);
x_61 = lean_ctor_get(x_13, 0);
lean_dec(x_61);
x_62 = lean_ctor_get(x_27, 0);
lean_inc(x_62);
lean_dec(x_27);
x_63 = l_Lean_Elab_Term_instInhabitedNamedArg;
x_64 = lean_array_get(x_63, x_21, x_62);
x_65 = l_Array_eraseIdx___rarg(x_21, x_62);
lean_dec(x_62);
lean_ctor_set(x_13, 4, x_65);
x_66 = lean_ctor_get(x_64, 2);
lean_inc(x_66);
lean_dec(x_64);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_67 = l_Lean_Elab_Term_CollectPatternVars_collect_pushNewArg(x_11, x_13, x_66, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_1 = x_68;
x_9 = x_69;
goto _start;
}
else
{
uint8_t x_71; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_71 = !lean_is_exclusive(x_67);
if (x_71 == 0)
{
return x_67;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_67, 0);
x_73 = lean_ctor_get(x_67, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_67);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_13);
x_75 = lean_ctor_get(x_27, 0);
lean_inc(x_75);
lean_dec(x_27);
x_76 = l_Lean_Elab_Term_instInhabitedNamedArg;
x_77 = lean_array_get(x_76, x_21, x_75);
x_78 = l_Array_eraseIdx___rarg(x_21, x_75);
lean_dec(x_75);
x_79 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_79, 0, x_15);
lean_ctor_set(x_79, 1, x_16);
lean_ctor_set(x_79, 2, x_19);
lean_ctor_set(x_79, 3, x_20);
lean_ctor_set(x_79, 4, x_78);
lean_ctor_set(x_79, 5, x_22);
lean_ctor_set(x_79, 6, x_23);
lean_ctor_set_uint8(x_79, sizeof(void*)*7, x_17);
lean_ctor_set_uint8(x_79, sizeof(void*)*7 + 1, x_18);
x_80 = lean_ctor_get(x_77, 2);
lean_inc(x_80);
lean_dec(x_77);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_81 = l_Lean_Elab_Term_CollectPatternVars_collect_pushNewArg(x_11, x_79, x_80, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_1 = x_82;
x_9 = x_83;
goto _start;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_85 = lean_ctor_get(x_81, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_81, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_87 = x_81;
} else {
 lean_dec_ref(x_81);
 x_87 = lean_box(0);
}
if (lean_is_scalar(x_87)) {
 x_88 = lean_alloc_ctor(1, 2, 0);
} else {
 x_88 = x_87;
}
lean_ctor_set(x_88, 0, x_85);
lean_ctor_set(x_88, 1, x_86);
return x_88;
}
}
}
}
else
{
lean_object* x_89; 
x_89 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_89;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_collect_processExplicitArg___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_mapTRAux___at_Lean_Elab_Term_CollectPatternVars_collect_processExplicitArg___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___rarg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_7);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_CollectPatternVars_collect_processExplicitArg___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_7, 3);
x_11 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_5, x_6, x_7, x_8, x_9);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_13);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_11);
lean_inc(x_10);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect_processExplicitArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("explicit parameter is missing, unused named arguments ");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect_processExplicitArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_CollectPatternVars_collect_processExplicitArg___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect_processExplicitArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_instToStringPatternVar___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_processExplicitArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_2, 5);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 1);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_13 = lean_ctor_get(x_2, 4);
lean_inc(x_13);
lean_dec(x_2);
x_14 = lean_array_get_size(x_13);
x_15 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_16 = 0;
x_17 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_collect_processExplicitArg___spec__1(x_15, x_16, x_13);
x_18 = lean_array_to_list(lean_box(0), x_17);
x_19 = lean_box(0);
x_20 = l_List_mapTRAux___at_Lean_Elab_Term_CollectPatternVars_collect_processExplicitArg___spec__2(x_18, x_19);
x_21 = l_Lean_MessageData_ofList(x_20);
lean_dec(x_20);
x_22 = l_Lean_Elab_Term_CollectPatternVars_collect_processExplicitArg___closed__2;
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = l_Lean_Elab_Term_CollectPatternVars_collect_processExplicitArg___closed__3;
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_throwError___at_Lean_Elab_Term_CollectPatternVars_collect_processExplicitArg___spec__3(x_25, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_inc(x_8);
x_27 = l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___spec__2___rarg(x_8, x_9, x_10);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_5, x_6, x_7, x_8, x_9, x_29);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = l_Lean_Elab_Term_getMainModule___rarg(x_9, x_31);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__26;
x_35 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_35, 0, x_28);
lean_ctor_set(x_35, 1, x_34);
x_36 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_mkMVarSyntax___closed__4;
x_37 = lean_array_push(x_36, x_35);
x_38 = lean_box(2);
x_39 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__25;
x_40 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set(x_40, 2, x_37);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = l_Lean_Elab_Term_CollectPatternVars_collect_pushNewArg(x_1, x_2, x_41, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_33);
return x_42;
}
}
else
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_2);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_2, 5);
lean_dec(x_44);
x_45 = lean_ctor_get(x_11, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_11, 1);
lean_inc(x_46);
lean_dec(x_11);
lean_ctor_set(x_2, 5, x_46);
x_47 = l_Lean_Elab_Term_CollectPatternVars_collect_pushNewArg(x_1, x_2, x_45, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_48 = lean_ctor_get(x_2, 0);
x_49 = lean_ctor_get(x_2, 1);
x_50 = lean_ctor_get_uint8(x_2, sizeof(void*)*7);
x_51 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 1);
x_52 = lean_ctor_get(x_2, 2);
x_53 = lean_ctor_get(x_2, 3);
x_54 = lean_ctor_get(x_2, 4);
x_55 = lean_ctor_get(x_2, 6);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_2);
x_56 = lean_ctor_get(x_11, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_11, 1);
lean_inc(x_57);
lean_dec(x_11);
x_58 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_58, 0, x_48);
lean_ctor_set(x_58, 1, x_49);
lean_ctor_set(x_58, 2, x_52);
lean_ctor_set(x_58, 3, x_53);
lean_ctor_set(x_58, 4, x_54);
lean_ctor_set(x_58, 5, x_57);
lean_ctor_set(x_58, 6, x_55);
lean_ctor_set_uint8(x_58, sizeof(void*)*7, x_50);
lean_ctor_set_uint8(x_58, sizeof(void*)*7 + 1, x_51);
x_59 = l_Lean_Elab_Term_CollectPatternVars_collect_pushNewArg(x_1, x_58, x_56, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_59;
}
}
}
}
static lean_object* _init_l_panic___at_Lean_Elab_Term_CollectPatternVars_collect_pushNewArg___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_instMonadTermElabM;
x_2 = l_ReaderT_instMonadReaderT___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_Elab_Term_CollectPatternVars_collect_pushNewArg___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_panic___at_Lean_Elab_Term_CollectPatternVars_collect_pushNewArg___spec__1___closed__1;
x_2 = l_Lean_Elab_Term_CollectPatternVars_instInhabitedContext;
x_3 = l_instInhabited___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Elab_Term_CollectPatternVars_collect_pushNewArg___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_panic___at_Lean_Elab_Term_CollectPatternVars_collect_pushNewArg___spec__1___closed__2;
x_11 = lean_panic_fn(x_10, x_1);
x_12 = lean_apply_8(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_pushNewArg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_1, 6);
x_13 = lean_array_push(x_12, x_2);
lean_ctor_set(x_1, 6, x_13);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_ctor_get(x_1, 1);
x_17 = lean_ctor_get_uint8(x_1, sizeof(void*)*7);
x_18 = lean_ctor_get_uint8(x_1, sizeof(void*)*7 + 1);
x_19 = lean_ctor_get(x_1, 2);
x_20 = lean_ctor_get(x_1, 3);
x_21 = lean_ctor_get(x_1, 4);
x_22 = lean_ctor_get(x_1, 5);
x_23 = lean_ctor_get(x_1, 6);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_1);
x_24 = lean_array_push(x_23, x_2);
x_25 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_25, 0, x_15);
lean_ctor_set(x_25, 1, x_16);
lean_ctor_set(x_25, 2, x_19);
lean_ctor_set(x_25, 3, x_20);
lean_ctor_set(x_25, 4, x_21);
lean_ctor_set(x_25, 5, x_22);
lean_ctor_set(x_25, 6, x_24);
lean_ctor_set_uint8(x_25, sizeof(void*)*7, x_17);
lean_ctor_set_uint8(x_25, sizeof(void*)*7 + 1, x_18);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_10);
return x_26;
}
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect_pushNewArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Elab.PatternVar");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect_pushNewArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Elab.Term.CollectPatternVars.collect.pushNewArg");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect_pushNewArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unreachable code has been reached");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect_pushNewArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_Term_CollectPatternVars_collect_pushNewArg___closed__1;
x_2 = l_Lean_Elab_Term_CollectPatternVars_collect_pushNewArg___closed__2;
x_3 = lean_unsigned_to_nat(273u);
x_4 = lean_unsigned_to_nat(11u);
x_5 = l_Lean_Elab_Term_CollectPatternVars_collect_pushNewArg___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_pushNewArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
if (x_1 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
lean_dec(x_3);
x_13 = l_Lean_Elab_Term_CollectPatternVars_collect_pushNewArg___lambda__1(x_2, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_3, 0);
lean_inc(x_14);
lean_dec(x_3);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_15 = l_Lean_Elab_Term_CollectPatternVars_collect(x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Elab_Term_CollectPatternVars_collect_pushNewArg___lambda__1(x_2, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_19 = !lean_is_exclusive(x_15);
if (x_19 == 0)
{
return x_15;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_15, 0);
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_15);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_3);
lean_dec(x_2);
x_23 = l_Lean_Elab_Term_CollectPatternVars_collect_pushNewArg___closed__4;
x_24 = l_panic___at_Lean_Elab_Term_CollectPatternVars_collect_pushNewArg___spec__1(x_23, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_collect___spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_2, x_1);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_array_uget(x_3, x_2);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_uset(x_3, x_2, x_15);
x_17 = l_Lean_Syntax_getArg(x_14, x_15);
lean_dec(x_14);
x_18 = lean_unsigned_to_nat(2u);
x_19 = l_Lean_Syntax_getArg(x_17, x_18);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_20 = l_Lean_Elab_Term_CollectPatternVars_collect(x_19, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Syntax_setArg(x_17, x_18, x_21);
lean_inc(x_23);
x_24 = l_Lean_Syntax_setArg(x_23, x_15, x_23);
x_25 = 1;
x_26 = lean_usize_add(x_2, x_25);
x_27 = lean_array_uset(x_16, x_2, x_24);
x_2 = x_26;
x_3 = x_27;
x_11 = x_22;
goto _start;
}
else
{
uint8_t x_29; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_29 = !lean_is_exclusive(x_20);
if (x_29 == 0)
{
return x_20;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_20, 0);
x_31 = lean_ctor_get(x_20, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_20);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_0__Array_mapSepElemsMAux___at_Lean_Elab_Term_CollectPatternVars_collect___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_get_size(x_1);
x_14 = lean_nat_dec_lt(x_3, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_array_fget(x_1, x_3);
x_17 = lean_unsigned_to_nat(2u);
x_18 = lean_nat_mod(x_3, x_17);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_nat_dec_eq(x_18, x_19);
lean_dec(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_3, x_21);
lean_dec(x_3);
x_23 = lean_array_push(x_4, x_16);
x_3 = x_22;
x_4 = x_23;
goto _start;
}
else
{
lean_object* x_25; 
lean_inc(x_2);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_25 = lean_apply_9(x_2, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_3, x_28);
lean_dec(x_3);
x_30 = lean_array_push(x_4, x_26);
x_3 = x_29;
x_4 = x_30;
x_12 = x_27;
goto _start;
}
else
{
uint8_t x_32; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_32 = !lean_is_exclusive(x_25);
if (x_32 == 0)
{
return x_25;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_25, 0);
x_34 = lean_ctor_get(x_25, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_25);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElemsM___at_Lean_Elab_Term_CollectPatternVars_collect___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_mkMVarSyntax___closed__3;
x_13 = l___private_Init_Meta_0__Array_mapSepElemsMAux___at_Lean_Elab_Term_CollectPatternVars_collect___spec__3(x_1, x_2, x_11, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_11 = l_Lean_Elab_Term_CollectPatternVars_collect(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_unsigned_to_nat(3u);
x_15 = l_Lean_Syntax_getArg(x_3, x_14);
x_16 = l_Lean_Elab_Term_CollectPatternVars_collect(x_15, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_unsigned_to_nat(2u);
x_20 = l_Lean_Syntax_setArg(x_3, x_19, x_12);
x_21 = l_Lean_Syntax_setArg(x_20, x_14, x_18);
lean_ctor_set(x_16, 0, x_21);
return x_16;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_16, 0);
x_23 = lean_ctor_get(x_16, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_16);
x_24 = lean_unsigned_to_nat(2u);
x_25 = l_Lean_Syntax_setArg(x_3, x_24, x_12);
x_26 = l_Lean_Syntax_setArg(x_25, x_14, x_22);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_23);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_12);
lean_dec(x_3);
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
else
{
uint8_t x_32; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_32 = !lean_is_exclusive(x_11);
if (x_32 == 0)
{
return x_11;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_11, 0);
x_34 = lean_ctor_get(x_11, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_11);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_root_.namedPattern");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__3___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___lambda__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__3___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__3___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___lambda__3___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_root_");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___lambda__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__3___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___lambda__3___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("namedPattern");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___lambda__3___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__3___closed__5;
x_2 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__3___closed__6;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___lambda__3___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__3___closed__6;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___lambda__3___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__3___closed__8;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___lambda__3___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__3___closed__9;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_unsigned_to_nat(3u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_15 = l_Lean_Elab_Term_CollectPatternVars_collect(x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_18 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
lean_inc(x_10);
x_20 = l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___spec__2___rarg(x_10, x_11, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Elab_Term_getCurrMacroScope(x_6, x_7, x_8, x_9, x_10, x_11, x_22);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_Elab_Term_getMainModule___rarg(x_11, x_25);
lean_dec(x_11);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__3___closed__7;
x_30 = l_Lean_addMacroScope(x_28, x_29, x_24);
x_31 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__3___closed__3;
x_32 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__3___closed__10;
x_33 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_33, 0, x_21);
lean_ctor_set(x_33, 1, x_31);
lean_ctor_set(x_33, 2, x_30);
lean_ctor_set(x_33, 3, x_32);
x_34 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__27;
x_35 = lean_array_push(x_34, x_2);
x_36 = lean_array_push(x_35, x_16);
x_37 = lean_array_push(x_36, x_4);
x_38 = lean_box(2);
x_39 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__23;
x_40 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set(x_40, 2, x_37);
x_41 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__12;
x_42 = lean_array_push(x_41, x_33);
x_43 = lean_array_push(x_42, x_40);
x_44 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_44, 0, x_38);
lean_ctor_set(x_44, 1, x_3);
lean_ctor_set(x_44, 2, x_43);
lean_ctor_set(x_26, 0, x_44);
return x_26;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_45 = lean_ctor_get(x_26, 0);
x_46 = lean_ctor_get(x_26, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_26);
x_47 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__3___closed__7;
x_48 = l_Lean_addMacroScope(x_45, x_47, x_24);
x_49 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__3___closed__3;
x_50 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__3___closed__10;
x_51 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_51, 0, x_21);
lean_ctor_set(x_51, 1, x_49);
lean_ctor_set(x_51, 2, x_48);
lean_ctor_set(x_51, 3, x_50);
x_52 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__27;
x_53 = lean_array_push(x_52, x_2);
x_54 = lean_array_push(x_53, x_16);
x_55 = lean_array_push(x_54, x_4);
x_56 = lean_box(2);
x_57 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__23;
x_58 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
lean_ctor_set(x_58, 2, x_55);
x_59 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__12;
x_60 = lean_array_push(x_59, x_51);
x_61 = lean_array_push(x_60, x_58);
x_62 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_62, 0, x_56);
lean_ctor_set(x_62, 1, x_3);
lean_ctor_set(x_62, 2, x_61);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_46);
return x_63;
}
}
else
{
uint8_t x_64; 
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_64 = !lean_is_exclusive(x_18);
if (x_64 == 0)
{
return x_18;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_18, 0);
x_66 = lean_ctor_get(x_18, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_18);
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
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_68 = !lean_is_exclusive(x_15);
if (x_68 == 0)
{
return x_15;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_15, 0);
x_70 = lean_ctor_get(x_15, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_15);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("h");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___lambda__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__4___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___lambda__4___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__4___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__4___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___lambda__4___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__4___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_2);
lean_inc(x_1);
x_12 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar(x_1, x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_unsigned_to_nat(2u);
x_15 = l_Lean_Syntax_getArg(x_3, x_14);
x_16 = l_Lean_Syntax_isNone(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_Lean_Syntax_getArg(x_15, x_17);
lean_dec(x_15);
x_19 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__3(x_3, x_1, x_4, x_18, x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_13);
lean_dec(x_3);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_15);
lean_inc(x_9);
x_20 = l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___spec__2___rarg(x_9, x_10, x_13);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_6, x_7, x_8, x_9, x_10, x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_Elab_Term_getMainModule___rarg(x_10, x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__4___closed__4;
x_30 = l_Lean_addMacroScope(x_27, x_29, x_24);
x_31 = lean_box(0);
x_32 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__4___closed__3;
x_33 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_33, 0, x_21);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_33, 2, x_30);
lean_ctor_set(x_33, 3, x_31);
x_34 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__3(x_3, x_1, x_4, x_33, x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_28);
lean_dec(x_3);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_12);
if (x_35 == 0)
{
return x_12;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_12, 0);
x_37 = lean_ctor_get(x_12, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_12);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Term_CollectPatternVars_collect(x_1, x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Lean_Syntax_setArg(x_3, x_15, x_14);
x_17 = lean_unsigned_to_nat(1u);
x_18 = l_Lean_Syntax_setArg(x_4, x_17, x_16);
lean_ctor_set(x_12, 0, x_18);
return x_12;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_12, 0);
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_12);
x_21 = lean_unsigned_to_nat(0u);
x_22 = l_Lean_Syntax_setArg(x_3, x_21, x_19);
x_23 = lean_unsigned_to_nat(1u);
x_24 = l_Lean_Syntax_setArg(x_4, x_23, x_22);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_20);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_4);
lean_dec(x_3);
x_26 = !lean_is_exclusive(x_12);
if (x_26 == 0)
{
return x_12;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_12, 0);
x_28 = lean_ctor_get(x_12, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_12);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_10 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_mkMVarSyntax(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_unsigned_to_nat(1u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
x_15 = l_Lean_Syntax_isIdent(x_14);
x_16 = lean_st_ref_get(x_8, x_12);
if (x_15 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_dec(x_14);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_st_ref_take(x_2, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_22 = lean_ctor_get(x_19, 1);
x_23 = l_Lean_Elab_Term_getMVarSyntaxMVarId(x_11);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_array_push(x_22, x_25);
lean_ctor_set(x_19, 1, x_26);
x_27 = lean_st_ref_set(x_2, x_19, x_20);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_11);
return x_27;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_11);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_32 = lean_ctor_get(x_19, 0);
x_33 = lean_ctor_get(x_19, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_19);
x_34 = l_Lean_Elab_Term_getMVarSyntaxMVarId(x_11);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_array_push(x_33, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_32);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_st_ref_set(x_2, x_38, x_20);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_41 = x_39;
} else {
 lean_dec_ref(x_39);
 x_41 = lean_box(0);
}
if (lean_is_scalar(x_41)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_41;
}
lean_ctor_set(x_42, 0, x_11);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_43 = lean_ctor_get(x_16, 1);
lean_inc(x_43);
lean_dec(x_16);
x_44 = l_Lean_Syntax_getId(x_14);
lean_dec(x_14);
x_45 = lean_st_ref_take(x_2, x_43);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = !lean_is_exclusive(x_46);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_49 = lean_ctor_get(x_46, 1);
x_50 = l_Lean_Elab_Term_getMVarSyntaxMVarId(x_11);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_44);
x_52 = lean_array_push(x_49, x_51);
lean_ctor_set(x_46, 1, x_52);
x_53 = lean_st_ref_set(x_2, x_46, x_47);
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_53, 0);
lean_dec(x_55);
lean_ctor_set(x_53, 0, x_11);
return x_53;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_53, 1);
lean_inc(x_56);
lean_dec(x_53);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_11);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_58 = lean_ctor_get(x_46, 0);
x_59 = lean_ctor_get(x_46, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_46);
x_60 = l_Lean_Elab_Term_getMVarSyntaxMVarId(x_11);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_44);
x_62 = lean_array_push(x_59, x_61);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_58);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_st_ref_set(x_2, x_63, x_47);
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
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_11);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_9 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_mkMVarSyntax(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_st_ref_get(x_7, x_11);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_st_ref_take(x_1, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_18 = lean_ctor_get(x_15, 1);
x_19 = l_Lean_Elab_Term_getMVarSyntaxMVarId(x_10);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_array_push(x_18, x_21);
lean_ctor_set(x_15, 1, x_22);
x_23 = lean_st_ref_set(x_1, x_15, x_16);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
lean_ctor_set(x_23, 0, x_10);
return x_23;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_10);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_28 = lean_ctor_get(x_15, 0);
x_29 = lean_ctor_get(x_15, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_15);
x_30 = l_Lean_Elab_Term_getMVarSyntaxMVarId(x_10);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_array_push(x_29, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_28);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_st_ref_set(x_1, x_34, x_16);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_37 = x_35;
} else {
 lean_dec_ref(x_35);
 x_37 = lean_box(0);
}
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_10);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_11 = lean_unsigned_to_nat(2u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = l_Lean_Syntax_getArgs(x_12);
lean_dec(x_12);
x_14 = lean_array_get_size(x_13);
x_15 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_16 = 0;
x_17 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_collect___spec__1(x_15, x_16, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_box(2);
x_21 = l_Lean_nullKind;
x_22 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set(x_22, 2, x_19);
x_23 = l_Lean_Syntax_setArg(x_1, x_11, x_22);
lean_ctor_set(x_17, 0, x_23);
return x_17;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_24 = lean_ctor_get(x_17, 0);
x_25 = lean_ctor_get(x_17, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_17);
x_26 = lean_box(2);
x_27 = l_Lean_nullKind;
x_28 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set(x_28, 2, x_24);
x_29 = l_Lean_Syntax_setArg(x_1, x_11, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_25);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_1);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_Lean_throwErrorAt___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___spec__2(x_1, x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
return x_12;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_12);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___lambda__10___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__10___closed__1;
x_12 = l_Array_mapSepElemsM___at_Lean_Elab_Term_CollectPatternVars_collect___spec__2(x_1, x_11, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_box(2);
x_16 = l_Lean_nullKind;
x_17 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_17, 2, x_14);
x_18 = lean_unsigned_to_nat(1u);
x_19 = l_Lean_Syntax_setArg(x_3, x_18, x_17);
lean_ctor_set(x_12, 0, x_19);
return x_12;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_20 = lean_ctor_get(x_12, 0);
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_12);
x_22 = lean_box(2);
x_23 = l_Lean_nullKind;
x_24 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_24, 2, x_20);
x_25 = lean_unsigned_to_nat(1u);
x_26 = l_Lean_Syntax_setArg(x_3, x_25, x_24);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_21);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_3);
x_28 = !lean_is_exclusive(x_12);
if (x_28 == 0)
{
return x_12;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_12, 0);
x_30 = lean_ctor_get(x_12, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_12);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("anonymousCtor");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__8;
x_2 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("structInst");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__8;
x_2 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("syntheticHole");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__8;
x_2 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("paren");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__8;
x_2 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("explicitUniv");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__8;
x_2 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__9;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__8;
x_2 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__3___closed__6;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("binop");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__8;
x_2 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__12;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("inaccessible");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__8;
x_2 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__14;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("quotedName");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__8;
x_2 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__16;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("doubleQuotedName");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__8;
x_2 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__18;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid pattern, notation is ambiguous");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__20;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__22() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("typeAscription");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__8;
x_2 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__22;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__24() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid struct instance pattern, 'with' is not allowed in patterns");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__24;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; 
lean_inc(x_1);
x_10 = l_Lean_Syntax_getKind(x_1);
x_11 = l_Lean_identKind;
x_12 = lean_name_eq(x_10, x_11);
x_13 = !lean_is_exclusive(x_7);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_7, 3);
x_15 = l_Lean_replaceRef(x_1, x_14);
lean_dec(x_14);
lean_ctor_set(x_7, 3, x_15);
if (x_12 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__13;
x_17 = lean_name_eq(x_10, x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__2;
x_19 = lean_name_eq(x_10, x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__4;
x_21 = lean_name_eq(x_10, x_20);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__25;
x_23 = lean_name_eq(x_10, x_22);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__6;
x_25 = lean_name_eq(x_10, x_24);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__8;
x_27 = lean_name_eq(x_10, x_26);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__10;
x_29 = lean_name_eq(x_10, x_28);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__11;
x_31 = lean_name_eq(x_10, x_30);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__13;
x_33 = lean_name_eq(x_10, x_32);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__15;
x_35 = lean_name_eq(x_10, x_34);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = l_Lean_strLitKind;
x_37 = lean_name_eq(x_10, x_36);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = l_Lean_numLitKind;
x_39 = lean_name_eq(x_10, x_38);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = l_Lean_scientificLitKind;
x_41 = lean_name_eq(x_10, x_40);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = l_Lean_charLitKind;
x_43 = lean_name_eq(x_10, x_42);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__17;
x_45 = lean_name_eq(x_10, x_44);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__19;
x_47 = lean_name_eq(x_10, x_46);
if (x_47 == 0)
{
lean_object* x_48; uint8_t x_49; 
lean_dec(x_1);
x_48 = l_Lean_choiceKind;
x_49 = lean_name_eq(x_10, x_48);
lean_dec(x_10);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_alloc_closure((void*)(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___rarg), 8, 1);
lean_closure_set(x_50, 0, x_2);
x_51 = l_Lean_Elab_Term_withFreshMacroScope___rarg(x_50, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__21;
x_53 = lean_alloc_closure((void*)(l_Lean_throwError___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___spec__1___boxed), 9, 2);
lean_closure_set(x_53, 0, x_52);
lean_closure_set(x_53, 1, x_2);
x_54 = l_Lean_Elab_Term_withFreshMacroScope___rarg(x_53, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_10);
lean_dec(x_2);
x_55 = lean_alloc_closure((void*)(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___boxed), 8, 1);
lean_closure_set(x_55, 0, x_1);
x_56 = l_Lean_Elab_Term_withFreshMacroScope___rarg(x_55, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_56;
}
}
else
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_10);
lean_dec(x_2);
x_57 = lean_alloc_closure((void*)(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_quotedNameToPattern), 8, 1);
lean_closure_set(x_57, 0, x_1);
x_58 = l_Lean_Elab_Term_withFreshMacroScope___rarg(x_57, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_58;
}
}
else
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_10);
lean_dec(x_2);
x_59 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__1___boxed), 8, 1);
lean_closure_set(x_59, 0, x_1);
x_60 = l_Lean_Elab_Term_withFreshMacroScope___rarg(x_59, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_60;
}
}
else
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_10);
lean_dec(x_2);
x_61 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__1___boxed), 8, 1);
lean_closure_set(x_61, 0, x_1);
x_62 = l_Lean_Elab_Term_withFreshMacroScope___rarg(x_61, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_62;
}
}
else
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_10);
lean_dec(x_2);
x_63 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__1___boxed), 8, 1);
lean_closure_set(x_63, 0, x_1);
x_64 = l_Lean_Elab_Term_withFreshMacroScope___rarg(x_63, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_64;
}
}
else
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_10);
lean_dec(x_2);
x_65 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__1___boxed), 8, 1);
lean_closure_set(x_65, 0, x_1);
x_66 = l_Lean_Elab_Term_withFreshMacroScope___rarg(x_65, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_10);
lean_dec(x_2);
x_67 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__1___boxed), 8, 1);
lean_closure_set(x_67, 0, x_1);
x_68 = l_Lean_Elab_Term_withFreshMacroScope___rarg(x_67, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_68;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_10);
x_69 = lean_unsigned_to_nat(2u);
x_70 = l_Lean_Syntax_getArg(x_1, x_69);
x_71 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__2), 10, 3);
lean_closure_set(x_71, 0, x_70);
lean_closure_set(x_71, 1, x_2);
lean_closure_set(x_71, 2, x_1);
x_72 = l_Lean_Elab_Term_withFreshMacroScope___rarg(x_71, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_72;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_10);
x_73 = lean_unsigned_to_nat(0u);
x_74 = l_Lean_Syntax_getArg(x_1, x_73);
x_75 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__4), 11, 4);
lean_closure_set(x_75, 0, x_74);
lean_closure_set(x_75, 1, x_2);
lean_closure_set(x_75, 2, x_1);
lean_closure_set(x_75, 3, x_16);
x_76 = l_Lean_Elab_Term_withFreshMacroScope___rarg(x_75, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_76;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_10);
x_77 = lean_unsigned_to_nat(0u);
x_78 = l_Lean_Syntax_getArg(x_1, x_77);
lean_dec(x_1);
x_79 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect_processCtor), 9, 2);
lean_closure_set(x_79, 0, x_78);
lean_closure_set(x_79, 1, x_2);
x_80 = l_Lean_Elab_Term_withFreshMacroScope___rarg(x_79, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_80;
}
}
else
{
lean_object* x_81; lean_object* x_82; uint8_t x_83; 
lean_dec(x_10);
x_81 = lean_unsigned_to_nat(1u);
x_82 = l_Lean_Syntax_getArg(x_1, x_81);
x_83 = l_Lean_Syntax_isNone(x_82);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_84 = lean_unsigned_to_nat(0u);
x_85 = l_Lean_Syntax_getArg(x_82, x_84);
x_86 = l_Lean_Syntax_getArg(x_82, x_81);
x_87 = l_Lean_Syntax_isNone(x_86);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_88 = l_Lean_Syntax_getArg(x_86, x_84);
lean_dec(x_86);
x_89 = l_Lean_Syntax_getKind(x_88);
x_90 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__23;
x_91 = lean_name_eq(x_89, x_90);
lean_dec(x_89);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; 
lean_dec(x_85);
lean_dec(x_82);
lean_dec(x_2);
x_92 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__1___boxed), 8, 1);
lean_closure_set(x_92, 0, x_1);
x_93 = l_Lean_Elab_Term_withFreshMacroScope___rarg(x_92, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__5), 11, 4);
lean_closure_set(x_94, 0, x_85);
lean_closure_set(x_94, 1, x_2);
lean_closure_set(x_94, 2, x_82);
lean_closure_set(x_94, 3, x_1);
x_95 = l_Lean_Elab_Term_withFreshMacroScope___rarg(x_94, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_95;
}
}
else
{
lean_object* x_96; lean_object* x_97; 
lean_dec(x_86);
x_96 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__5), 11, 4);
lean_closure_set(x_96, 0, x_85);
lean_closure_set(x_96, 1, x_2);
lean_closure_set(x_96, 2, x_82);
lean_closure_set(x_96, 3, x_1);
x_97 = l_Lean_Elab_Term_withFreshMacroScope___rarg(x_96, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_97;
}
}
else
{
lean_object* x_98; lean_object* x_99; 
lean_dec(x_82);
lean_dec(x_2);
x_98 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__1___boxed), 8, 1);
lean_closure_set(x_98, 0, x_1);
x_99 = l_Lean_Elab_Term_withFreshMacroScope___rarg(x_98, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_99;
}
}
}
else
{
lean_object* x_100; lean_object* x_101; 
lean_dec(x_10);
x_100 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__6___boxed), 9, 2);
lean_closure_set(x_100, 0, x_1);
lean_closure_set(x_100, 1, x_2);
x_101 = l_Lean_Elab_Term_withFreshMacroScope___rarg(x_100, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_101;
}
}
else
{
lean_object* x_102; lean_object* x_103; 
lean_dec(x_10);
lean_dec(x_1);
x_102 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__7___boxed), 8, 1);
lean_closure_set(x_102, 0, x_2);
x_103 = l_Lean_Elab_Term_withFreshMacroScope___rarg(x_102, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_103;
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; 
lean_dec(x_10);
x_104 = lean_unsigned_to_nat(1u);
x_105 = l_Lean_Syntax_getArg(x_1, x_104);
lean_inc(x_1);
x_106 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__8___boxed), 10, 1);
lean_closure_set(x_106, 0, x_1);
x_107 = l_Lean_Syntax_isNone(x_105);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_1);
x_108 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__25;
x_109 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__9___boxed), 11, 4);
lean_closure_set(x_109, 0, x_105);
lean_closure_set(x_109, 1, x_108);
lean_closure_set(x_109, 2, x_2);
lean_closure_set(x_109, 3, x_106);
x_110 = l_Lean_Elab_Term_withFreshMacroScope___rarg(x_109, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_110;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_106);
lean_dec(x_105);
x_111 = lean_box(0);
x_112 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__8___boxed), 10, 3);
lean_closure_set(x_112, 0, x_1);
lean_closure_set(x_112, 1, x_111);
lean_closure_set(x_112, 2, x_2);
x_113 = l_Lean_Elab_Term_withFreshMacroScope___rarg(x_112, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_113;
}
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec(x_10);
x_114 = lean_unsigned_to_nat(1u);
x_115 = l_Lean_Syntax_getArg(x_1, x_114);
x_116 = l_Lean_Syntax_getArgs(x_115);
lean_dec(x_115);
x_117 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__10___boxed), 10, 3);
lean_closure_set(x_117, 0, x_116);
lean_closure_set(x_117, 1, x_2);
lean_closure_set(x_117, 2, x_1);
x_118 = l_Lean_Elab_Term_withFreshMacroScope___rarg(x_117, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_118;
}
}
else
{
lean_object* x_119; lean_object* x_120; 
lean_dec(x_10);
x_119 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp), 9, 2);
lean_closure_set(x_119, 0, x_1);
lean_closure_set(x_119, 1, x_2);
x_120 = l_Lean_Elab_Term_withFreshMacroScope___rarg(x_119, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_120;
}
}
else
{
lean_object* x_121; lean_object* x_122; 
lean_dec(x_10);
x_121 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect_processId), 9, 2);
lean_closure_set(x_121, 0, x_1);
lean_closure_set(x_121, 1, x_2);
x_122 = l_Lean_Elab_Term_withFreshMacroScope___rarg(x_121, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_122;
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_123 = lean_ctor_get(x_7, 0);
x_124 = lean_ctor_get(x_7, 1);
x_125 = lean_ctor_get(x_7, 2);
x_126 = lean_ctor_get(x_7, 3);
x_127 = lean_ctor_get(x_7, 4);
x_128 = lean_ctor_get(x_7, 5);
x_129 = lean_ctor_get(x_7, 6);
x_130 = lean_ctor_get(x_7, 7);
lean_inc(x_130);
lean_inc(x_129);
lean_inc(x_128);
lean_inc(x_127);
lean_inc(x_126);
lean_inc(x_125);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_7);
x_131 = l_Lean_replaceRef(x_1, x_126);
lean_dec(x_126);
x_132 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_132, 0, x_123);
lean_ctor_set(x_132, 1, x_124);
lean_ctor_set(x_132, 2, x_125);
lean_ctor_set(x_132, 3, x_131);
lean_ctor_set(x_132, 4, x_127);
lean_ctor_set(x_132, 5, x_128);
lean_ctor_set(x_132, 6, x_129);
lean_ctor_set(x_132, 7, x_130);
if (x_12 == 0)
{
lean_object* x_133; uint8_t x_134; 
x_133 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__13;
x_134 = lean_name_eq(x_10, x_133);
if (x_134 == 0)
{
lean_object* x_135; uint8_t x_136; 
x_135 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__2;
x_136 = lean_name_eq(x_10, x_135);
if (x_136 == 0)
{
lean_object* x_137; uint8_t x_138; 
x_137 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__4;
x_138 = lean_name_eq(x_10, x_137);
if (x_138 == 0)
{
lean_object* x_139; uint8_t x_140; 
x_139 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__25;
x_140 = lean_name_eq(x_10, x_139);
if (x_140 == 0)
{
lean_object* x_141; uint8_t x_142; 
x_141 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__6;
x_142 = lean_name_eq(x_10, x_141);
if (x_142 == 0)
{
lean_object* x_143; uint8_t x_144; 
x_143 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__8;
x_144 = lean_name_eq(x_10, x_143);
if (x_144 == 0)
{
lean_object* x_145; uint8_t x_146; 
x_145 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__10;
x_146 = lean_name_eq(x_10, x_145);
if (x_146 == 0)
{
lean_object* x_147; uint8_t x_148; 
x_147 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__11;
x_148 = lean_name_eq(x_10, x_147);
if (x_148 == 0)
{
lean_object* x_149; uint8_t x_150; 
x_149 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__13;
x_150 = lean_name_eq(x_10, x_149);
if (x_150 == 0)
{
lean_object* x_151; uint8_t x_152; 
x_151 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__15;
x_152 = lean_name_eq(x_10, x_151);
if (x_152 == 0)
{
lean_object* x_153; uint8_t x_154; 
x_153 = l_Lean_strLitKind;
x_154 = lean_name_eq(x_10, x_153);
if (x_154 == 0)
{
lean_object* x_155; uint8_t x_156; 
x_155 = l_Lean_numLitKind;
x_156 = lean_name_eq(x_10, x_155);
if (x_156 == 0)
{
lean_object* x_157; uint8_t x_158; 
x_157 = l_Lean_scientificLitKind;
x_158 = lean_name_eq(x_10, x_157);
if (x_158 == 0)
{
lean_object* x_159; uint8_t x_160; 
x_159 = l_Lean_charLitKind;
x_160 = lean_name_eq(x_10, x_159);
if (x_160 == 0)
{
lean_object* x_161; uint8_t x_162; 
x_161 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__17;
x_162 = lean_name_eq(x_10, x_161);
if (x_162 == 0)
{
lean_object* x_163; uint8_t x_164; 
x_163 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__19;
x_164 = lean_name_eq(x_10, x_163);
if (x_164 == 0)
{
lean_object* x_165; uint8_t x_166; 
lean_dec(x_1);
x_165 = l_Lean_choiceKind;
x_166 = lean_name_eq(x_10, x_165);
lean_dec(x_10);
if (x_166 == 0)
{
lean_object* x_167; lean_object* x_168; 
x_167 = lean_alloc_closure((void*)(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___rarg), 8, 1);
lean_closure_set(x_167, 0, x_2);
x_168 = l_Lean_Elab_Term_withFreshMacroScope___rarg(x_167, x_3, x_4, x_5, x_6, x_132, x_8, x_9);
return x_168;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_169 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__21;
x_170 = lean_alloc_closure((void*)(l_Lean_throwError___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___spec__1___boxed), 9, 2);
lean_closure_set(x_170, 0, x_169);
lean_closure_set(x_170, 1, x_2);
x_171 = l_Lean_Elab_Term_withFreshMacroScope___rarg(x_170, x_3, x_4, x_5, x_6, x_132, x_8, x_9);
return x_171;
}
}
else
{
lean_object* x_172; lean_object* x_173; 
lean_dec(x_10);
lean_dec(x_2);
x_172 = lean_alloc_closure((void*)(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___boxed), 8, 1);
lean_closure_set(x_172, 0, x_1);
x_173 = l_Lean_Elab_Term_withFreshMacroScope___rarg(x_172, x_3, x_4, x_5, x_6, x_132, x_8, x_9);
return x_173;
}
}
else
{
lean_object* x_174; lean_object* x_175; 
lean_dec(x_10);
lean_dec(x_2);
x_174 = lean_alloc_closure((void*)(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_quotedNameToPattern), 8, 1);
lean_closure_set(x_174, 0, x_1);
x_175 = l_Lean_Elab_Term_withFreshMacroScope___rarg(x_174, x_3, x_4, x_5, x_6, x_132, x_8, x_9);
return x_175;
}
}
else
{
lean_object* x_176; lean_object* x_177; 
lean_dec(x_10);
lean_dec(x_2);
x_176 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__1___boxed), 8, 1);
lean_closure_set(x_176, 0, x_1);
x_177 = l_Lean_Elab_Term_withFreshMacroScope___rarg(x_176, x_3, x_4, x_5, x_6, x_132, x_8, x_9);
return x_177;
}
}
else
{
lean_object* x_178; lean_object* x_179; 
lean_dec(x_10);
lean_dec(x_2);
x_178 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__1___boxed), 8, 1);
lean_closure_set(x_178, 0, x_1);
x_179 = l_Lean_Elab_Term_withFreshMacroScope___rarg(x_178, x_3, x_4, x_5, x_6, x_132, x_8, x_9);
return x_179;
}
}
else
{
lean_object* x_180; lean_object* x_181; 
lean_dec(x_10);
lean_dec(x_2);
x_180 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__1___boxed), 8, 1);
lean_closure_set(x_180, 0, x_1);
x_181 = l_Lean_Elab_Term_withFreshMacroScope___rarg(x_180, x_3, x_4, x_5, x_6, x_132, x_8, x_9);
return x_181;
}
}
else
{
lean_object* x_182; lean_object* x_183; 
lean_dec(x_10);
lean_dec(x_2);
x_182 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__1___boxed), 8, 1);
lean_closure_set(x_182, 0, x_1);
x_183 = l_Lean_Elab_Term_withFreshMacroScope___rarg(x_182, x_3, x_4, x_5, x_6, x_132, x_8, x_9);
return x_183;
}
}
else
{
lean_object* x_184; lean_object* x_185; 
lean_dec(x_10);
lean_dec(x_2);
x_184 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__1___boxed), 8, 1);
lean_closure_set(x_184, 0, x_1);
x_185 = l_Lean_Elab_Term_withFreshMacroScope___rarg(x_184, x_3, x_4, x_5, x_6, x_132, x_8, x_9);
return x_185;
}
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
lean_dec(x_10);
x_186 = lean_unsigned_to_nat(2u);
x_187 = l_Lean_Syntax_getArg(x_1, x_186);
x_188 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__2), 10, 3);
lean_closure_set(x_188, 0, x_187);
lean_closure_set(x_188, 1, x_2);
lean_closure_set(x_188, 2, x_1);
x_189 = l_Lean_Elab_Term_withFreshMacroScope___rarg(x_188, x_3, x_4, x_5, x_6, x_132, x_8, x_9);
return x_189;
}
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
lean_dec(x_10);
x_190 = lean_unsigned_to_nat(0u);
x_191 = l_Lean_Syntax_getArg(x_1, x_190);
x_192 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__4), 11, 4);
lean_closure_set(x_192, 0, x_191);
lean_closure_set(x_192, 1, x_2);
lean_closure_set(x_192, 2, x_1);
lean_closure_set(x_192, 3, x_133);
x_193 = l_Lean_Elab_Term_withFreshMacroScope___rarg(x_192, x_3, x_4, x_5, x_6, x_132, x_8, x_9);
return x_193;
}
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
lean_dec(x_10);
x_194 = lean_unsigned_to_nat(0u);
x_195 = l_Lean_Syntax_getArg(x_1, x_194);
lean_dec(x_1);
x_196 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect_processCtor), 9, 2);
lean_closure_set(x_196, 0, x_195);
lean_closure_set(x_196, 1, x_2);
x_197 = l_Lean_Elab_Term_withFreshMacroScope___rarg(x_196, x_3, x_4, x_5, x_6, x_132, x_8, x_9);
return x_197;
}
}
else
{
lean_object* x_198; lean_object* x_199; uint8_t x_200; 
lean_dec(x_10);
x_198 = lean_unsigned_to_nat(1u);
x_199 = l_Lean_Syntax_getArg(x_1, x_198);
x_200 = l_Lean_Syntax_isNone(x_199);
if (x_200 == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; uint8_t x_204; 
x_201 = lean_unsigned_to_nat(0u);
x_202 = l_Lean_Syntax_getArg(x_199, x_201);
x_203 = l_Lean_Syntax_getArg(x_199, x_198);
x_204 = l_Lean_Syntax_isNone(x_203);
if (x_204 == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; uint8_t x_208; 
x_205 = l_Lean_Syntax_getArg(x_203, x_201);
lean_dec(x_203);
x_206 = l_Lean_Syntax_getKind(x_205);
x_207 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__23;
x_208 = lean_name_eq(x_206, x_207);
lean_dec(x_206);
if (x_208 == 0)
{
lean_object* x_209; lean_object* x_210; 
lean_dec(x_202);
lean_dec(x_199);
lean_dec(x_2);
x_209 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__1___boxed), 8, 1);
lean_closure_set(x_209, 0, x_1);
x_210 = l_Lean_Elab_Term_withFreshMacroScope___rarg(x_209, x_3, x_4, x_5, x_6, x_132, x_8, x_9);
return x_210;
}
else
{
lean_object* x_211; lean_object* x_212; 
x_211 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__5), 11, 4);
lean_closure_set(x_211, 0, x_202);
lean_closure_set(x_211, 1, x_2);
lean_closure_set(x_211, 2, x_199);
lean_closure_set(x_211, 3, x_1);
x_212 = l_Lean_Elab_Term_withFreshMacroScope___rarg(x_211, x_3, x_4, x_5, x_6, x_132, x_8, x_9);
return x_212;
}
}
else
{
lean_object* x_213; lean_object* x_214; 
lean_dec(x_203);
x_213 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__5), 11, 4);
lean_closure_set(x_213, 0, x_202);
lean_closure_set(x_213, 1, x_2);
lean_closure_set(x_213, 2, x_199);
lean_closure_set(x_213, 3, x_1);
x_214 = l_Lean_Elab_Term_withFreshMacroScope___rarg(x_213, x_3, x_4, x_5, x_6, x_132, x_8, x_9);
return x_214;
}
}
else
{
lean_object* x_215; lean_object* x_216; 
lean_dec(x_199);
lean_dec(x_2);
x_215 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__1___boxed), 8, 1);
lean_closure_set(x_215, 0, x_1);
x_216 = l_Lean_Elab_Term_withFreshMacroScope___rarg(x_215, x_3, x_4, x_5, x_6, x_132, x_8, x_9);
return x_216;
}
}
}
else
{
lean_object* x_217; lean_object* x_218; 
lean_dec(x_10);
x_217 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__6___boxed), 9, 2);
lean_closure_set(x_217, 0, x_1);
lean_closure_set(x_217, 1, x_2);
x_218 = l_Lean_Elab_Term_withFreshMacroScope___rarg(x_217, x_3, x_4, x_5, x_6, x_132, x_8, x_9);
return x_218;
}
}
else
{
lean_object* x_219; lean_object* x_220; 
lean_dec(x_10);
lean_dec(x_1);
x_219 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__7___boxed), 8, 1);
lean_closure_set(x_219, 0, x_2);
x_220 = l_Lean_Elab_Term_withFreshMacroScope___rarg(x_219, x_3, x_4, x_5, x_6, x_132, x_8, x_9);
return x_220;
}
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; uint8_t x_224; 
lean_dec(x_10);
x_221 = lean_unsigned_to_nat(1u);
x_222 = l_Lean_Syntax_getArg(x_1, x_221);
lean_inc(x_1);
x_223 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__8___boxed), 10, 1);
lean_closure_set(x_223, 0, x_1);
x_224 = l_Lean_Syntax_isNone(x_222);
if (x_224 == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; 
lean_dec(x_1);
x_225 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__25;
x_226 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__9___boxed), 11, 4);
lean_closure_set(x_226, 0, x_222);
lean_closure_set(x_226, 1, x_225);
lean_closure_set(x_226, 2, x_2);
lean_closure_set(x_226, 3, x_223);
x_227 = l_Lean_Elab_Term_withFreshMacroScope___rarg(x_226, x_3, x_4, x_5, x_6, x_132, x_8, x_9);
return x_227;
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; 
lean_dec(x_223);
lean_dec(x_222);
x_228 = lean_box(0);
x_229 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__8___boxed), 10, 3);
lean_closure_set(x_229, 0, x_1);
lean_closure_set(x_229, 1, x_228);
lean_closure_set(x_229, 2, x_2);
x_230 = l_Lean_Elab_Term_withFreshMacroScope___rarg(x_229, x_3, x_4, x_5, x_6, x_132, x_8, x_9);
return x_230;
}
}
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
lean_dec(x_10);
x_231 = lean_unsigned_to_nat(1u);
x_232 = l_Lean_Syntax_getArg(x_1, x_231);
x_233 = l_Lean_Syntax_getArgs(x_232);
lean_dec(x_232);
x_234 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__10___boxed), 10, 3);
lean_closure_set(x_234, 0, x_233);
lean_closure_set(x_234, 1, x_2);
lean_closure_set(x_234, 2, x_1);
x_235 = l_Lean_Elab_Term_withFreshMacroScope___rarg(x_234, x_3, x_4, x_5, x_6, x_132, x_8, x_9);
return x_235;
}
}
else
{
lean_object* x_236; lean_object* x_237; 
lean_dec(x_10);
x_236 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp), 9, 2);
lean_closure_set(x_236, 0, x_1);
lean_closure_set(x_236, 1, x_2);
x_237 = l_Lean_Elab_Term_withFreshMacroScope___rarg(x_236, x_3, x_4, x_5, x_6, x_132, x_8, x_9);
return x_237;
}
}
else
{
lean_object* x_238; lean_object* x_239; 
lean_dec(x_10);
x_238 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect_processId), 9, 2);
lean_closure_set(x_238, 0, x_1);
lean_closure_set(x_238, 1, x_2);
x_239 = l_Lean_Elab_Term_withFreshMacroScope___rarg(x_238, x_3, x_4, x_5, x_6, x_132, x_8, x_9);
return x_239;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_processCtor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_10 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_mkMVarSyntax___closed__3;
x_11 = 0;
x_12 = l_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore(x_1, x_10, x_10, x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_processId(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_10 = l_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___lambda__2___closed__1;
x_11 = 1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_12 = l_Lean_Elab_Term_resolveId_x3f(x_1, x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_14);
return x_15;
}
else
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
if (lean_obj_tag(x_16) == 4)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_st_ref_get(x_8, x_17);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_18);
x_23 = lean_environment_find(x_22, x_18);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
lean_dec(x_18);
lean_dec(x_1);
x_24 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_21);
return x_24;
}
else
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
if (lean_obj_tag(x_25) == 6)
{
lean_object* x_26; 
lean_dec(x_25);
lean_dec(x_18);
x_26 = l_Lean_Elab_Term_CollectPatternVars_collect_processCtor(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_21);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
lean_dec(x_25);
x_27 = lean_st_ref_get(x_8, x_21);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___lambda__2___closed__3;
x_32 = l_Lean_TagAttribute_hasTag(x_31, x_30, x_18);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_29);
return x_33;
}
else
{
lean_object* x_34; 
x_34 = l_Lean_Elab_Term_CollectPatternVars_collect_processCtor(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_29);
return x_34;
}
}
}
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_16);
x_35 = lean_ctor_get(x_12, 1);
lean_inc(x_35);
lean_dec(x_12);
x_36 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_35);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_12);
if (x_37 == 0)
{
return x_12;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_12, 0);
x_39 = lean_ctor_get(x_12, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_12);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_processImplicitArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_ctor_get_uint8(x_2, sizeof(void*)*7);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_inc(x_8);
x_12 = l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___spec__2___rarg(x_8, x_9, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Elab_Term_getCurrMacroScope(x_4, x_5, x_6, x_7, x_8, x_9, x_14);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_Elab_Term_getMainModule___rarg(x_9, x_16);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__26;
x_20 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_20, 0, x_13);
lean_ctor_set(x_20, 1, x_19);
x_21 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_mkMVarSyntax___closed__4;
x_22 = lean_array_push(x_21, x_20);
x_23 = lean_box(2);
x_24 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__25;
x_25 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_25, 2, x_22);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = l_Lean_Elab_Term_CollectPatternVars_collect_pushNewArg(x_1, x_2, x_26, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_18);
return x_27;
}
else
{
lean_object* x_28; 
x_28 = l_Lean_Elab_Term_CollectPatternVars_collect_processExplicitArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwError___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_getConstInfo___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___spec__3(x_12, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwError___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_1);
lean_dec(x_1);
x_14 = l_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___lambda__2(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_4);
lean_dec(x_4);
x_14 = l_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore(x_1, x_2, x_3, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppContext___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppContext___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_collect_processExplicitArg___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_collect_processExplicitArg___spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_CollectPatternVars_collect_processExplicitArg___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwError___at_Lean_Elab_Term_CollectPatternVars_collect_processExplicitArg___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_processExplicitArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = l_Lean_Elab_Term_CollectPatternVars_collect_processExplicitArg(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_pushNewArg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Term_CollectPatternVars_collect_pushNewArg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_pushNewArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_1);
lean_dec(x_1);
x_13 = l_Lean_Elab_Term_CollectPatternVars_collect_pushNewArg(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_collect___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_collect___spec__1(x_12, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_0__Array_mapSepElemsMAux___at_Lean_Elab_Term_CollectPatternVars_collect___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Init_Meta_0__Array_mapSepElemsMAux___at_Lean_Elab_Term_CollectPatternVars_collect___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElemsM___at_Lean_Elab_Term_CollectPatternVars_collect___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_mapSepElemsM___at_Lean_Elab_Term_CollectPatternVars_collect___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_processImplicitArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = l_Lean_Elab_Term_CollectPatternVars_collect_processImplicitArg(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_traceMsg");
return x_1;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_addTrace___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("[");
return x_1;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addTrace___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("] ");
return x_1;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addTrace___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Elab_Term_CollectPatternVars_main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_11 = lean_ctor_get(x_8, 3);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_2, x_6, x_7, x_8, x_9, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l___private_Lean_Util_Trace_0__Lean_addTraceOptions(x_13);
x_16 = lean_st_ref_take(x_9, x_14);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 3);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_17, 3);
lean_dec(x_21);
x_22 = !lean_is_exclusive(x_18);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_23 = lean_ctor_get(x_18, 0);
x_24 = l_Lean_addTrace___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__2;
x_25 = l_Lean_Name_append(x_1, x_24);
x_26 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_26, 0, x_1);
x_27 = l_Lean_addTrace___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__4;
x_28 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = l_Lean_addTrace___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__6;
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_15);
x_32 = l_Lean_Elab_Term_CollectPatternVars_collect_processExplicitArg___closed__3;
x_33 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_34, 0, x_25);
lean_ctor_set(x_34, 1, x_33);
lean_inc(x_11);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_11);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Std_PersistentArray_push___rarg(x_23, x_35);
lean_ctor_set(x_18, 0, x_36);
x_37 = lean_st_ref_set(x_9, x_17, x_19);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_37, 0);
lean_dec(x_39);
x_40 = lean_box(0);
lean_ctor_set(x_37, 0, x_40);
return x_37;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_37, 1);
lean_inc(x_41);
lean_dec(x_37);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
}
else
{
uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_44 = lean_ctor_get_uint8(x_18, sizeof(void*)*1);
x_45 = lean_ctor_get(x_18, 0);
lean_inc(x_45);
lean_dec(x_18);
x_46 = l_Lean_addTrace___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__2;
x_47 = l_Lean_Name_append(x_1, x_46);
x_48 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_48, 0, x_1);
x_49 = l_Lean_addTrace___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__4;
x_50 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
x_51 = l_Lean_addTrace___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__6;
x_52 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_15);
x_54 = l_Lean_Elab_Term_CollectPatternVars_collect_processExplicitArg___closed__3;
x_55 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_56, 0, x_47);
lean_ctor_set(x_56, 1, x_55);
lean_inc(x_11);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_11);
lean_ctor_set(x_57, 1, x_56);
x_58 = l_Std_PersistentArray_push___rarg(x_45, x_57);
x_59 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set_uint8(x_59, sizeof(void*)*1, x_44);
lean_ctor_set(x_17, 3, x_59);
x_60 = lean_st_ref_set(x_9, x_17, x_19);
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_62 = x_60;
} else {
 lean_dec_ref(x_60);
 x_62 = lean_box(0);
}
x_63 = lean_box(0);
if (lean_is_scalar(x_62)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_62;
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_61);
return x_64;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_65 = lean_ctor_get(x_17, 0);
x_66 = lean_ctor_get(x_17, 1);
x_67 = lean_ctor_get(x_17, 2);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_17);
x_68 = lean_ctor_get_uint8(x_18, sizeof(void*)*1);
x_69 = lean_ctor_get(x_18, 0);
lean_inc(x_69);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 x_70 = x_18;
} else {
 lean_dec_ref(x_18);
 x_70 = lean_box(0);
}
x_71 = l_Lean_addTrace___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__2;
x_72 = l_Lean_Name_append(x_1, x_71);
x_73 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_73, 0, x_1);
x_74 = l_Lean_addTrace___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__4;
x_75 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_73);
x_76 = l_Lean_addTrace___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__6;
x_77 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_15);
x_79 = l_Lean_Elab_Term_CollectPatternVars_collect_processExplicitArg___closed__3;
x_80 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
x_81 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_81, 0, x_72);
lean_ctor_set(x_81, 1, x_80);
lean_inc(x_11);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_11);
lean_ctor_set(x_82, 1, x_81);
x_83 = l_Std_PersistentArray_push___rarg(x_69, x_82);
if (lean_is_scalar(x_70)) {
 x_84 = lean_alloc_ctor(0, 1, 1);
} else {
 x_84 = x_70;
}
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set_uint8(x_84, sizeof(void*)*1, x_68);
x_85 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_85, 0, x_65);
lean_ctor_set(x_85, 1, x_66);
lean_ctor_set(x_85, 2, x_67);
lean_ctor_set(x_85, 3, x_84);
x_86 = lean_st_ref_set(x_9, x_85, x_19);
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_88 = x_86;
} else {
 lean_dec_ref(x_86);
 x_88 = lean_box(0);
}
x_89 = lean_box(0);
if (lean_is_scalar(x_88)) {
 x_90 = lean_alloc_ctor(0, 2, 0);
} else {
 x_90 = x_88;
}
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_87);
return x_90;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Elab_Term_CollectPatternVars_main___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = l_Lean_checkTraceOption(x_10, x_1);
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_main___spec__3___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Term_CollectPatternVars_collect(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_main___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Elab");
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_main___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_main___spec__3___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_main___spec__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("match");
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_main___spec__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_main___spec__3___closed__2;
x_2 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_main___spec__3___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_main___spec__3___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("collecting variables at pattern: ");
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_main___spec__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_main___spec__3___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_main___spec__3(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_2, x_1);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_14 = lean_array_uget(x_3, x_2);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_uset(x_3, x_2, x_15);
x_17 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_main___spec__3___closed__4;
x_50 = lean_st_ref_get(x_10, x_11);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_51, 3);
lean_inc(x_52);
lean_dec(x_51);
x_53 = lean_ctor_get_uint8(x_52, sizeof(void*)*1);
lean_dec(x_52);
if (x_53 == 0)
{
lean_object* x_54; uint8_t x_55; 
x_54 = lean_ctor_get(x_50, 1);
lean_inc(x_54);
lean_dec(x_50);
x_55 = 0;
x_18 = x_55;
x_19 = x_54;
goto block_49;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_56 = lean_ctor_get(x_50, 1);
lean_inc(x_56);
lean_dec(x_50);
x_57 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Elab_Term_CollectPatternVars_main___spec__2(x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_56);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_unbox(x_58);
lean_dec(x_58);
x_18 = x_60;
x_19 = x_59;
goto block_49;
}
block_49:
{
if (x_18 == 0)
{
lean_object* x_20; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_20 = l_Lean_Elab_Term_CollectPatternVars_collect(x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = 1;
x_24 = lean_usize_add(x_2, x_23);
x_25 = lean_array_uset(x_16, x_2, x_21);
x_2 = x_24;
x_3 = x_25;
x_11 = x_22;
goto _start;
}
else
{
uint8_t x_27; 
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_inc(x_14);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_14);
x_32 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_main___spec__3___closed__6;
x_33 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
x_34 = l_Lean_Elab_Term_CollectPatternVars_collect_processExplicitArg___closed__3;
x_35 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_addTrace___at_Lean_Elab_Term_CollectPatternVars_main___spec__1(x_17, x_35, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_19);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_38 = l_Lean_Elab_Term_CollectPatternVars_collect(x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; size_t x_41; size_t x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = 1;
x_42 = lean_usize_add(x_2, x_41);
x_43 = lean_array_uset(x_16, x_2, x_39);
x_2 = x_42;
x_3 = x_43;
x_11 = x_40;
goto _start;
}
else
{
uint8_t x_45; 
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_45 = !lean_is_exclusive(x_38);
if (x_45 == 0)
{
return x_38;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_38, 0);
x_47 = lean_ctor_get(x_38, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_38);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
x_13 = lean_ctor_get(x_1, 2);
x_14 = lean_array_get_size(x_12);
x_15 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_16 = 0;
x_17 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_main___spec__3(x_15, x_16, x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_ctor_set(x_1, 1, x_19);
lean_ctor_set(x_17, 0, x_1);
return x_17;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_17, 0);
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_17);
lean_ctor_set(x_1, 1, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_free_object(x_1);
lean_dec(x_13);
lean_dec(x_11);
x_23 = !lean_is_exclusive(x_17);
if (x_23 == 0)
{
return x_17;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_17, 0);
x_25 = lean_ctor_get(x_17, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_17);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; size_t x_31; size_t x_32; lean_object* x_33; 
x_27 = lean_ctor_get(x_1, 0);
x_28 = lean_ctor_get(x_1, 1);
x_29 = lean_ctor_get(x_1, 2);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_1);
x_30 = lean_array_get_size(x_28);
x_31 = lean_usize_of_nat(x_30);
lean_dec(x_30);
x_32 = 0;
x_33 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_main___spec__3(x_31, x_32, x_28, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_36 = x_33;
} else {
 lean_dec_ref(x_33);
 x_36 = lean_box(0);
}
x_37 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_37, 0, x_27);
lean_ctor_set(x_37, 1, x_34);
lean_ctor_set(x_37, 2, x_29);
if (lean_is_scalar(x_36)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_36;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_35);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_29);
lean_dec(x_27);
x_39 = lean_ctor_get(x_33, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_33, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_41 = x_33;
} else {
 lean_dec_ref(x_33);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_addTrace___at_Lean_Elab_Term_CollectPatternVars_main___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Elab_Term_CollectPatternVars_main___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Elab_Term_CollectPatternVars_main___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_main___spec__3___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_main___spec__3___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_main___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_main___spec__3(x_12, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
static lean_object* _init_l_Lean_Elab_Term_collectPatternVars___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_NameSet_empty;
x_2 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_mkMVarSyntax___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_collectPatternVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_Elab_Term_collectPatternVars___closed__1;
x_12 = lean_st_mk_ref(x_11, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_7);
lean_inc(x_13);
x_15 = l_Lean_Elab_Term_CollectPatternVars_main(x_1, x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_st_ref_get(x_7, x_17);
lean_dec(x_7);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_st_ref_get(x_13, x_19);
lean_dec(x_13);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_16);
lean_ctor_set(x_20, 0, x_24);
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_20, 0);
x_26 = lean_ctor_get(x_20, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_20);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_16);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec(x_13);
lean_dec(x_7);
x_30 = !lean_is_exclusive(x_15);
if (x_30 == 0)
{
return x_15;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_15, 0);
x_32 = lean_ctor_get(x_15, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_15);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_getPatternVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_closure((void*)(l_Lean_expandMacros), 3, 1);
lean_closure_set(x_9, 0, x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_10 = l_Lean_Elab_liftMacroM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__9(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_st_ref_get(x_7, x_12);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lean_Elab_Term_collectPatternVars___closed__1;
x_16 = lean_st_mk_ref(x_15, x_14);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_7);
lean_inc(x_17);
x_19 = l_Lean_Elab_Term_CollectPatternVars_collect(x_11, x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_st_ref_get(x_7, x_20);
lean_dec(x_7);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_st_ref_get(x_17, x_22);
lean_dec(x_17);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
lean_ctor_set(x_23, 0, x_26);
return x_23;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_23, 0);
x_28 = lean_ctor_get(x_23, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_23);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_17);
lean_dec(x_7);
x_31 = !lean_is_exclusive(x_19);
if (x_31 == 0)
{
return x_19;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_19, 0);
x_33 = lean_ctor_get(x_19, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_19);
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
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_35 = !lean_is_exclusive(x_10);
if (x_35 == 0)
{
return x_10;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_10, 0);
x_37 = lean_ctor_get(x_10, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_10);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Elab_Term_getPatternsVars___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_11 = lean_ctor_get(x_8, 3);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_2, x_6, x_7, x_8, x_9, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l___private_Lean_Util_Trace_0__Lean_addTraceOptions(x_13);
x_16 = lean_st_ref_take(x_9, x_14);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 3);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_17, 3);
lean_dec(x_21);
x_22 = !lean_is_exclusive(x_18);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_23 = lean_ctor_get(x_18, 0);
x_24 = l_Lean_addTrace___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__2;
x_25 = l_Lean_Name_append(x_1, x_24);
x_26 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_26, 0, x_1);
x_27 = l_Lean_addTrace___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__4;
x_28 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = l_Lean_addTrace___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__6;
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_15);
x_32 = l_Lean_Elab_Term_CollectPatternVars_collect_processExplicitArg___closed__3;
x_33 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_34, 0, x_25);
lean_ctor_set(x_34, 1, x_33);
lean_inc(x_11);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_11);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Std_PersistentArray_push___rarg(x_23, x_35);
lean_ctor_set(x_18, 0, x_36);
x_37 = lean_st_ref_set(x_9, x_17, x_19);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_37, 0);
lean_dec(x_39);
x_40 = lean_box(0);
lean_ctor_set(x_37, 0, x_40);
return x_37;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_37, 1);
lean_inc(x_41);
lean_dec(x_37);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
}
else
{
uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_44 = lean_ctor_get_uint8(x_18, sizeof(void*)*1);
x_45 = lean_ctor_get(x_18, 0);
lean_inc(x_45);
lean_dec(x_18);
x_46 = l_Lean_addTrace___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__2;
x_47 = l_Lean_Name_append(x_1, x_46);
x_48 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_48, 0, x_1);
x_49 = l_Lean_addTrace___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__4;
x_50 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
x_51 = l_Lean_addTrace___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__6;
x_52 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_15);
x_54 = l_Lean_Elab_Term_CollectPatternVars_collect_processExplicitArg___closed__3;
x_55 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_56, 0, x_47);
lean_ctor_set(x_56, 1, x_55);
lean_inc(x_11);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_11);
lean_ctor_set(x_57, 1, x_56);
x_58 = l_Std_PersistentArray_push___rarg(x_45, x_57);
x_59 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set_uint8(x_59, sizeof(void*)*1, x_44);
lean_ctor_set(x_17, 3, x_59);
x_60 = lean_st_ref_set(x_9, x_17, x_19);
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_62 = x_60;
} else {
 lean_dec_ref(x_60);
 x_62 = lean_box(0);
}
x_63 = lean_box(0);
if (lean_is_scalar(x_62)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_62;
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_61);
return x_64;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_65 = lean_ctor_get(x_17, 0);
x_66 = lean_ctor_get(x_17, 1);
x_67 = lean_ctor_get(x_17, 2);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_17);
x_68 = lean_ctor_get_uint8(x_18, sizeof(void*)*1);
x_69 = lean_ctor_get(x_18, 0);
lean_inc(x_69);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 x_70 = x_18;
} else {
 lean_dec_ref(x_18);
 x_70 = lean_box(0);
}
x_71 = l_Lean_addTrace___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__2;
x_72 = l_Lean_Name_append(x_1, x_71);
x_73 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_73, 0, x_1);
x_74 = l_Lean_addTrace___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__4;
x_75 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_73);
x_76 = l_Lean_addTrace___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__6;
x_77 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_15);
x_79 = l_Lean_Elab_Term_CollectPatternVars_collect_processExplicitArg___closed__3;
x_80 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
x_81 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_81, 0, x_72);
lean_ctor_set(x_81, 1, x_80);
lean_inc(x_11);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_11);
lean_ctor_set(x_82, 1, x_81);
x_83 = l_Std_PersistentArray_push___rarg(x_69, x_82);
if (lean_is_scalar(x_70)) {
 x_84 = lean_alloc_ctor(0, 1, 1);
} else {
 x_84 = x_70;
}
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set_uint8(x_84, sizeof(void*)*1, x_68);
x_85 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_85, 0, x_65);
lean_ctor_set(x_85, 1, x_66);
lean_ctor_set(x_85, 2, x_67);
lean_ctor_set(x_85, 3, x_84);
x_86 = lean_st_ref_set(x_9, x_85, x_19);
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_88 = x_86;
} else {
 lean_dec_ref(x_86);
 x_88 = lean_box(0);
}
x_89 = lean_box(0);
if (lean_is_scalar(x_88)) {
 x_90 = lean_alloc_ctor(0, 2, 0);
} else {
 x_90 = x_88;
}
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_87);
return x_90;
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Elab_Term_getPatternsVars___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_st_ref_get(x_8, x_9);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 3);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_ctor_get_uint8(x_18, sizeof(void*)*1);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_15);
lean_dec(x_14);
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_1 = x_13;
x_9 = x_20;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_dec(x_16);
lean_inc(x_14);
x_23 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Elab_Term_CollectPatternVars_main___spec__2(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_unbox(x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_15);
lean_dec(x_14);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_1 = x_13;
x_9 = x_26;
goto _start;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_23, 1);
lean_inc(x_28);
lean_dec(x_23);
x_29 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_29, 0, x_15);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = l_Lean_addTrace___at_Lean_Elab_Term_getPatternsVars___spec__2(x_14, x_30, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_28);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_1 = x_13;
x_9 = x_32;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_getPatternsVars___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 3);
x_13 = l_Lean_replaceRef(x_1, x_12);
lean_dec(x_12);
lean_ctor_set(x_8, 3, x_13);
x_14 = l_Lean_throwError___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___spec__1(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_15 = lean_ctor_get(x_8, 0);
x_16 = lean_ctor_get(x_8, 1);
x_17 = lean_ctor_get(x_8, 2);
x_18 = lean_ctor_get(x_8, 3);
x_19 = lean_ctor_get(x_8, 4);
x_20 = lean_ctor_get(x_8, 5);
x_21 = lean_ctor_get(x_8, 6);
x_22 = lean_ctor_get(x_8, 7);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_8);
x_23 = l_Lean_replaceRef(x_1, x_18);
lean_dec(x_18);
x_24 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_24, 0, x_15);
lean_ctor_set(x_24, 1, x_16);
lean_ctor_set(x_24, 2, x_17);
lean_ctor_set(x_24, 3, x_23);
lean_ctor_set(x_24, 4, x_19);
lean_ctor_set(x_24, 5, x_20);
lean_ctor_set(x_24, 6, x_21);
lean_ctor_set(x_24, 7, x_22);
x_25 = l_Lean_throwError___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___spec__1(x_2, x_3, x_4, x_5, x_6, x_7, x_24, x_9, x_10);
lean_dec(x_24);
return x_25;
}
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_getPatternsVars___spec__5___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_maxRecDepthErrorMessage;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_getPatternsVars___spec__5___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_getPatternsVars___spec__5___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_getPatternsVars___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_getPatternsVars___spec__5___closed__2;
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_getPatternsVars___spec__6___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_unsupportedSyntaxExceptionId;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_getPatternsVars___spec__6___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_getPatternsVars___spec__6___rarg___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_getPatternsVars___spec__6___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_getPatternsVars___spec__6___rarg___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_getPatternsVars___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_alloc_closure((void*)(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_getPatternsVars___spec__6___rarg), 1, 0);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_getPatternsVars___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Elab_expandMacroImpl_x3f(x_1, x_2, x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_5, 0);
lean_dec(x_8);
x_9 = lean_box(0);
lean_ctor_set(x_5, 0, x_9);
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_6);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_6, 0);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
lean_dec(x_15);
lean_free_object(x_6);
x_16 = !lean_is_exclusive(x_5);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_5, 0);
lean_dec(x_17);
x_18 = lean_box(0);
lean_ctor_set(x_5, 0, x_18);
return x_5;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_5, 1);
lean_inc(x_19);
lean_dec(x_5);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_5);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_5, 0);
lean_dec(x_23);
x_24 = lean_ctor_get(x_15, 0);
lean_inc(x_24);
lean_dec(x_15);
lean_ctor_set(x_6, 0, x_24);
return x_5;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_5, 1);
lean_inc(x_25);
lean_dec(x_5);
x_26 = lean_ctor_get(x_15, 0);
lean_inc(x_26);
lean_dec(x_15);
lean_ctor_set(x_6, 0, x_26);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_6);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_6, 0);
lean_inc(x_28);
lean_dec(x_6);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_29);
x_30 = lean_ctor_get(x_5, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_31 = x_5;
} else {
 lean_dec_ref(x_5);
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
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_ctor_get(x_5, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_35 = x_5;
} else {
 lean_dec_ref(x_5);
 x_35 = lean_box(0);
}
x_36 = lean_ctor_get(x_29, 0);
lean_inc(x_36);
lean_dec(x_29);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
if (lean_is_scalar(x_35)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_35;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_34);
return x_38;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_getPatternsVars___spec__1___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Lean_Environment_contains(x_1, x_2);
x_6 = lean_box(x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_getPatternsVars___spec__1___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_ResolveName_resolveNamespace_x3f(x_1, x_2, x_3, x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_getPatternsVars___spec__1___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_ResolveName_resolveGlobalName(x_1, x_2, x_3, x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_getPatternsVars___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_10 = lean_st_ref_get(x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_7, 4);
lean_inc(x_14);
x_15 = lean_ctor_get(x_7, 5);
lean_inc(x_15);
lean_inc(x_13);
x_16 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_getPatternsVars___spec__1___lambda__1___boxed), 4, 1);
lean_closure_set(x_16, 0, x_13);
lean_inc(x_14);
x_17 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_Elab_liftMacroM___spec__1___rarg___boxed), 3, 1);
lean_closure_set(x_17, 0, x_14);
lean_inc(x_13);
x_18 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_getPatternsVars___spec__1___lambda__2___boxed), 4, 1);
lean_closure_set(x_18, 0, x_13);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_19 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_getPatternsVars___spec__1___lambda__3___boxed), 6, 3);
lean_closure_set(x_19, 0, x_13);
lean_closure_set(x_19, 1, x_14);
lean_closure_set(x_19, 2, x_15);
lean_inc(x_13);
x_20 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_getPatternsVars___spec__1___lambda__4___boxed), 6, 3);
lean_closure_set(x_20, 0, x_13);
lean_closure_set(x_20, 1, x_14);
lean_closure_set(x_20, 2, x_15);
x_21 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_21, 0, x_16);
lean_ctor_set(x_21, 1, x_17);
lean_ctor_set(x_21, 2, x_18);
lean_ctor_set(x_21, 3, x_19);
lean_ctor_set(x_21, 4, x_20);
x_22 = lean_ctor_get(x_7, 3);
lean_inc(x_22);
x_23 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_12);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_7, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_7, 2);
lean_inc(x_27);
x_28 = lean_st_ref_get(x_8, x_25);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_environment_main_module(x_13);
x_33 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_33, 0, x_21);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_33, 2, x_24);
lean_ctor_set(x_33, 3, x_26);
lean_ctor_set(x_33, 4, x_27);
lean_ctor_set(x_33, 5, x_22);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_31);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_apply_2(x_1, x_33, x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_st_ref_take(x_8, x_30);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = !lean_is_exclusive(x_41);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_44 = lean_ctor_get(x_41, 1);
lean_dec(x_44);
lean_ctor_set(x_41, 1, x_39);
x_45 = lean_st_ref_set(x_8, x_41, x_42);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_47 = lean_ctor_get(x_38, 1);
lean_inc(x_47);
lean_dec(x_38);
x_48 = l_List_reverse___rarg(x_47);
x_49 = l_List_forM___at_Lean_Elab_Term_getPatternsVars___spec__3(x_48, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_46);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_49, 0);
lean_dec(x_51);
lean_ctor_set(x_49, 0, x_37);
return x_49;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_dec(x_49);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_37);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_54 = lean_ctor_get(x_41, 0);
x_55 = lean_ctor_get(x_41, 2);
x_56 = lean_ctor_get(x_41, 3);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_41);
x_57 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_39);
lean_ctor_set(x_57, 2, x_55);
lean_ctor_set(x_57, 3, x_56);
x_58 = lean_st_ref_set(x_8, x_57, x_42);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_60 = lean_ctor_get(x_38, 1);
lean_inc(x_60);
lean_dec(x_38);
x_61 = l_List_reverse___rarg(x_60);
x_62 = l_List_forM___at_Lean_Elab_Term_getPatternsVars___spec__3(x_61, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_59);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_64 = x_62;
} else {
 lean_dec_ref(x_62);
 x_64 = lean_box(0);
}
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_64;
}
lean_ctor_set(x_65, 0, x_37);
lean_ctor_set(x_65, 1, x_63);
return x_65;
}
}
else
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_36, 0);
lean_inc(x_66);
lean_dec(x_36);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = l_Lean_maxRecDepthErrorMessage;
x_70 = lean_string_dec_eq(x_68, x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_71, 0, x_68);
x_72 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_72, 0, x_71);
x_73 = l_Lean_throwErrorAt___at_Lean_Elab_Term_getPatternsVars___spec__4(x_67, x_72, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_30);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_67);
return x_73;
}
else
{
lean_object* x_74; 
lean_dec(x_68);
x_74 = l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_getPatternsVars___spec__5(x_67, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_30);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_74;
}
}
else
{
lean_object* x_75; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_75 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_getPatternsVars___spec__6___rarg(x_30);
return x_75;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_getPatternsVars___spec__7(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_3, x_2);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_4);
x_15 = lean_array_uget(x_1, x_3);
x_16 = lean_alloc_closure((void*)(l_Lean_expandMacros), 3, 1);
lean_closure_set(x_16, 0, x_15);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_17 = l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_getPatternsVars___spec__1(x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_20 = l_Lean_Elab_Term_CollectPatternVars_collect(x_18, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = 1;
x_23 = lean_usize_add(x_3, x_22);
x_24 = lean_box(0);
x_3 = x_23;
x_4 = x_24;
x_12 = x_21;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_26 = !lean_is_exclusive(x_20);
if (x_26 == 0)
{
return x_20;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_20, 0);
x_28 = lean_ctor_get(x_20, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_20);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_30 = !lean_is_exclusive(x_17);
if (x_30 == 0)
{
return x_17;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_17, 0);
x_32 = lean_ctor_get(x_17, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_17);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_getPatternsVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_9 = lean_array_get_size(x_1);
x_10 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_11 = 0;
x_12 = lean_st_ref_get(x_7, x_8);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Lean_Elab_Term_collectPatternVars___closed__1;
x_15 = lean_st_mk_ref(x_14, x_13);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_box(0);
lean_inc(x_7);
lean_inc(x_16);
x_19 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_getPatternsVars___spec__7(x_1, x_10, x_11, x_18, x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_st_ref_get(x_7, x_20);
lean_dec(x_7);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_st_ref_get(x_16, x_22);
lean_dec(x_16);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
lean_ctor_set(x_23, 0, x_26);
return x_23;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_23, 0);
x_28 = lean_ctor_get(x_23, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_23);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_16);
lean_dec(x_7);
x_31 = !lean_is_exclusive(x_19);
if (x_31 == 0)
{
return x_19;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_19, 0);
x_33 = lean_ctor_get(x_19, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_19);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Elab_Term_getPatternsVars___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_addTrace___at_Lean_Elab_Term_getPatternsVars___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Elab_Term_getPatternsVars___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_List_forM___at_Lean_Elab_Term_getPatternsVars___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_getPatternsVars___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwErrorAt___at_Lean_Elab_Term_getPatternsVars___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_getPatternsVars___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_getPatternsVars___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_getPatternsVars___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_getPatternsVars___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_getPatternsVars___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_getPatternsVars___spec__1___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_getPatternsVars___spec__1___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_getPatternsVars___spec__1___lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_getPatternsVars___spec__1___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_getPatternsVars___spec__1___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_getPatternsVars___spec__1___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_getPatternsVars___spec__1___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_getPatternsVars___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_getPatternsVars___spec__7(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_getPatternsVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Term_getPatternsVars(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_getPatternVarNames___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = 1;
x_8 = lean_usize_add(x_2, x_7);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_array_push(x_4, x_9);
x_2 = x_8;
x_4 = x_10;
goto _start;
}
else
{
lean_dec(x_6);
x_2 = x_8;
goto _start;
}
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at_Lean_Elab_Term_getPatternVarNames___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_lt(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_3);
lean_dec(x_2);
x_5 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_mkMVarSyntax___closed__3;
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_le(x_3, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_2);
x_8 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_mkMVarSyntax___closed__3;
return x_8;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_usize_of_nat(x_2);
lean_dec(x_2);
x_10 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_11 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_mkMVarSyntax___closed__3;
x_12 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_getPatternVarNames___spec__2(x_1, x_9, x_10, x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_getPatternVarNames(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Array_filterMapM___at_Lean_Elab_Term_getPatternVarNames___spec__1(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_getPatternVarNames___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_getPatternVarNames___spec__2(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at_Lean_Elab_Term_getPatternVarNames___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_filterMapM___at_Lean_Elab_Term_getPatternVarNames___spec__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_getPatternVarNames___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_getPatternVarNames(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Match_MatchPatternAttr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Arg(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_MatchAltView(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_PatternVar(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Match_MatchPatternAttr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Arg(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_MatchAltView(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_instToStringPatternVar___closed__1 = _init_l_Lean_Elab_Term_instToStringPatternVar___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_instToStringPatternVar___closed__1);
l_Lean_Elab_Term_instToStringPatternVar___closed__2 = _init_l_Lean_Elab_Term_instToStringPatternVar___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_instToStringPatternVar___closed__2);
l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_mkMVarSyntax___closed__1 = _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_mkMVarSyntax___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_mkMVarSyntax___closed__1);
l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_mkMVarSyntax___closed__2 = _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_mkMVarSyntax___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_mkMVarSyntax___closed__2);
l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_mkMVarSyntax___closed__3 = _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_mkMVarSyntax___closed__3();
lean_mark_persistent(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_mkMVarSyntax___closed__3);
l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_mkMVarSyntax___closed__4 = _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_mkMVarSyntax___closed__4();
lean_mark_persistent(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_mkMVarSyntax___closed__4);
l_Lean_Elab_Term_CollectPatternVars_State_found___default = _init_l_Lean_Elab_Term_CollectPatternVars_State_found___default();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_State_found___default);
l_Lean_Elab_Term_CollectPatternVars_State_vars___default = _init_l_Lean_Elab_Term_CollectPatternVars_State_vars___default();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_State_vars___default);
l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___rarg___closed__1 = _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___rarg___closed__1);
l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___rarg___closed__2 = _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___rarg___closed__2);
l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___rarg___closed__1 = _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___rarg___closed__1);
l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___rarg___closed__2 = _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___rarg___closed__2);
l_Lean_Elab_Term_CollectPatternVars_Context_paramDeclIdx___default = _init_l_Lean_Elab_Term_CollectPatternVars_Context_paramDeclIdx___default();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_Context_paramDeclIdx___default);
l_Lean_Elab_Term_CollectPatternVars_Context_newArgs___default = _init_l_Lean_Elab_Term_CollectPatternVars_Context_newArgs___default();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_Context_newArgs___default);
l_Lean_Elab_Term_CollectPatternVars_instInhabitedContext___closed__1 = _init_l_Lean_Elab_Term_CollectPatternVars_instInhabitedContext___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_instInhabitedContext___closed__1);
l_Lean_Elab_Term_CollectPatternVars_instInhabitedContext = _init_l_Lean_Elab_Term_CollectPatternVars_instInhabitedContext();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_instInhabitedContext);
l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__1 = _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__1);
l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__2 = _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__2);
l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__3 = _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__3();
lean_mark_persistent(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__3);
l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__4 = _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__4();
lean_mark_persistent(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__4);
l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__5 = _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__5();
lean_mark_persistent(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__5);
l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__6 = _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__6();
lean_mark_persistent(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__6);
l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__7 = _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__7();
lean_mark_persistent(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__7);
l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__8 = _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__8();
lean_mark_persistent(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__8);
l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__9 = _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__9();
lean_mark_persistent(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__9);
l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__10 = _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__10();
lean_mark_persistent(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__10);
l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__11 = _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__11();
lean_mark_persistent(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__11);
l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__12 = _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__12();
lean_mark_persistent(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__12);
l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_getNextParam___closed__1 = _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_getNextParam___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_getNextParam___closed__1);
l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__2___closed__1 = _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__2___closed__1);
l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__2___closed__2 = _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__2___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__2___closed__2);
l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__2___closed__3 = _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__2___closed__3();
lean_mark_persistent(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__2___closed__3);
l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__2___closed__4 = _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__2___closed__4();
lean_mark_persistent(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__2___closed__4);
l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__3___closed__1 = _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__3___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__3___closed__1);
l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__3___closed__2 = _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__3___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__3___closed__2);
l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___closed__1 = _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___closed__1);
l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___closed__2 = _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___closed__2);
l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__1 = _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__1);
l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__2 = _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__2);
l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__3 = _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__3();
lean_mark_persistent(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__3);
l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__4 = _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__4();
lean_mark_persistent(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__4);
l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__5 = _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__5();
lean_mark_persistent(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__5);
l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__6 = _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__6();
lean_mark_persistent(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__6);
l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__7 = _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__7();
lean_mark_persistent(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__7);
l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__8 = _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__8();
lean_mark_persistent(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__8);
l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__9 = _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__9();
lean_mark_persistent(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__9);
l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__10 = _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__10();
lean_mark_persistent(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__10);
l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__11 = _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__11();
lean_mark_persistent(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__11);
l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__12 = _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__12();
lean_mark_persistent(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__12);
l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__13 = _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__13();
lean_mark_persistent(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__13);
l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__14 = _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__14();
lean_mark_persistent(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__14);
l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__15 = _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__15();
lean_mark_persistent(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__15);
l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__16 = _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__16();
lean_mark_persistent(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__16);
l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__17 = _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__17();
lean_mark_persistent(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__17);
l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__18 = _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__18();
lean_mark_persistent(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__18);
l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__19 = _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__19();
lean_mark_persistent(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__19);
l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__20 = _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__20();
lean_mark_persistent(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__20);
l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__21 = _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__21();
lean_mark_persistent(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__21);
l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__22 = _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__22();
lean_mark_persistent(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__22);
l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__23 = _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__23();
lean_mark_persistent(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__23);
l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__24 = _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__24();
lean_mark_persistent(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__24);
l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__25 = _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__25();
lean_mark_persistent(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__25);
l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__26 = _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__26();
lean_mark_persistent(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__26);
l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__27 = _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__27();
lean_mark_persistent(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__27);
l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__28 = _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__28();
lean_mark_persistent(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__28);
l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__29 = _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__29();
lean_mark_persistent(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__29);
l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__30 = _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__30();
lean_mark_persistent(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__30);
l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__31 = _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__31();
lean_mark_persistent(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__31);
l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__32 = _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__32();
lean_mark_persistent(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__32);
l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__33 = _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__33();
lean_mark_persistent(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__33);
l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__34 = _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__34();
lean_mark_persistent(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__34);
l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__35 = _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__35();
lean_mark_persistent(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__35);
l_Lean_Elab_throwIllFormedSyntax___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_quotedNameToPattern___spec__1___closed__1 = _init_l_Lean_Elab_throwIllFormedSyntax___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_quotedNameToPattern___spec__1___closed__1();
lean_mark_persistent(l_Lean_Elab_throwIllFormedSyntax___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_quotedNameToPattern___spec__1___closed__1);
l_Lean_Elab_throwIllFormedSyntax___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_quotedNameToPattern___spec__1___closed__2 = _init_l_Lean_Elab_throwIllFormedSyntax___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_quotedNameToPattern___spec__1___closed__2();
lean_mark_persistent(l_Lean_Elab_throwIllFormedSyntax___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_quotedNameToPattern___spec__1___closed__2);
l_Lean_throwUnknownConstant___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__6___closed__1 = _init_l_Lean_throwUnknownConstant___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__6___closed__1();
lean_mark_persistent(l_Lean_throwUnknownConstant___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__6___closed__1);
l_Lean_throwUnknownConstant___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__6___closed__2 = _init_l_Lean_throwUnknownConstant___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__6___closed__2();
lean_mark_persistent(l_Lean_throwUnknownConstant___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__6___closed__2);
l_Lean_throwUnknownConstant___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__6___closed__3 = _init_l_Lean_throwUnknownConstant___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__6___closed__3();
lean_mark_persistent(l_Lean_throwUnknownConstant___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__6___closed__3);
l_Lean_throwUnknownConstant___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__6___closed__4 = _init_l_Lean_throwUnknownConstant___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__6___closed__4();
lean_mark_persistent(l_Lean_throwUnknownConstant___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__6___closed__4);
l_Lean_resolveGlobalConst___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__3___closed__1 = _init_l_Lean_resolveGlobalConst___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__3___closed__1();
lean_mark_persistent(l_Lean_resolveGlobalConst___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__3___closed__1);
l_Lean_resolveGlobalConst___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__3___closed__2 = _init_l_Lean_resolveGlobalConst___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__3___closed__2();
lean_mark_persistent(l_Lean_resolveGlobalConst___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__3___closed__2);
l_Lean_resolveGlobalConst___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__3___closed__3 = _init_l_Lean_resolveGlobalConst___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__3___closed__3();
lean_mark_persistent(l_Lean_resolveGlobalConst___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__3___closed__3);
l_Lean_resolveGlobalConstNoOverload___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__2___closed__1 = _init_l_Lean_resolveGlobalConstNoOverload___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__2___closed__1();
lean_mark_persistent(l_Lean_resolveGlobalConstNoOverload___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__2___closed__1);
l_Lean_resolveGlobalConstNoOverload___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__2___closed__2 = _init_l_Lean_resolveGlobalConstNoOverload___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__2___closed__2();
lean_mark_persistent(l_Lean_resolveGlobalConstNoOverload___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__2___closed__2);
l_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___lambda__2___closed__1 = _init_l_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___lambda__2___closed__1);
l_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___lambda__2___closed__2 = _init_l_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___lambda__2___closed__2);
l_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___lambda__2___closed__3 = _init_l_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___lambda__2___closed__3);
l_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___closed__1 = _init_l_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___closed__1);
l_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___closed__2 = _init_l_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___closed__2);
l_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppContext___closed__1 = _init_l_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppContext___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppContext___closed__1);
l_Lean_Elab_Term_CollectPatternVars_collect_processExplicitArg___closed__1 = _init_l_Lean_Elab_Term_CollectPatternVars_collect_processExplicitArg___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect_processExplicitArg___closed__1);
l_Lean_Elab_Term_CollectPatternVars_collect_processExplicitArg___closed__2 = _init_l_Lean_Elab_Term_CollectPatternVars_collect_processExplicitArg___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect_processExplicitArg___closed__2);
l_Lean_Elab_Term_CollectPatternVars_collect_processExplicitArg___closed__3 = _init_l_Lean_Elab_Term_CollectPatternVars_collect_processExplicitArg___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect_processExplicitArg___closed__3);
l_panic___at_Lean_Elab_Term_CollectPatternVars_collect_pushNewArg___spec__1___closed__1 = _init_l_panic___at_Lean_Elab_Term_CollectPatternVars_collect_pushNewArg___spec__1___closed__1();
lean_mark_persistent(l_panic___at_Lean_Elab_Term_CollectPatternVars_collect_pushNewArg___spec__1___closed__1);
l_panic___at_Lean_Elab_Term_CollectPatternVars_collect_pushNewArg___spec__1___closed__2 = _init_l_panic___at_Lean_Elab_Term_CollectPatternVars_collect_pushNewArg___spec__1___closed__2();
lean_mark_persistent(l_panic___at_Lean_Elab_Term_CollectPatternVars_collect_pushNewArg___spec__1___closed__2);
l_Lean_Elab_Term_CollectPatternVars_collect_pushNewArg___closed__1 = _init_l_Lean_Elab_Term_CollectPatternVars_collect_pushNewArg___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect_pushNewArg___closed__1);
l_Lean_Elab_Term_CollectPatternVars_collect_pushNewArg___closed__2 = _init_l_Lean_Elab_Term_CollectPatternVars_collect_pushNewArg___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect_pushNewArg___closed__2);
l_Lean_Elab_Term_CollectPatternVars_collect_pushNewArg___closed__3 = _init_l_Lean_Elab_Term_CollectPatternVars_collect_pushNewArg___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect_pushNewArg___closed__3);
l_Lean_Elab_Term_CollectPatternVars_collect_pushNewArg___closed__4 = _init_l_Lean_Elab_Term_CollectPatternVars_collect_pushNewArg___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect_pushNewArg___closed__4);
l_Lean_Elab_Term_CollectPatternVars_collect___lambda__3___closed__1 = _init_l_Lean_Elab_Term_CollectPatternVars_collect___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__3___closed__1);
l_Lean_Elab_Term_CollectPatternVars_collect___lambda__3___closed__2 = _init_l_Lean_Elab_Term_CollectPatternVars_collect___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__3___closed__2);
l_Lean_Elab_Term_CollectPatternVars_collect___lambda__3___closed__3 = _init_l_Lean_Elab_Term_CollectPatternVars_collect___lambda__3___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__3___closed__3);
l_Lean_Elab_Term_CollectPatternVars_collect___lambda__3___closed__4 = _init_l_Lean_Elab_Term_CollectPatternVars_collect___lambda__3___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__3___closed__4);
l_Lean_Elab_Term_CollectPatternVars_collect___lambda__3___closed__5 = _init_l_Lean_Elab_Term_CollectPatternVars_collect___lambda__3___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__3___closed__5);
l_Lean_Elab_Term_CollectPatternVars_collect___lambda__3___closed__6 = _init_l_Lean_Elab_Term_CollectPatternVars_collect___lambda__3___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__3___closed__6);
l_Lean_Elab_Term_CollectPatternVars_collect___lambda__3___closed__7 = _init_l_Lean_Elab_Term_CollectPatternVars_collect___lambda__3___closed__7();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__3___closed__7);
l_Lean_Elab_Term_CollectPatternVars_collect___lambda__3___closed__8 = _init_l_Lean_Elab_Term_CollectPatternVars_collect___lambda__3___closed__8();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__3___closed__8);
l_Lean_Elab_Term_CollectPatternVars_collect___lambda__3___closed__9 = _init_l_Lean_Elab_Term_CollectPatternVars_collect___lambda__3___closed__9();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__3___closed__9);
l_Lean_Elab_Term_CollectPatternVars_collect___lambda__3___closed__10 = _init_l_Lean_Elab_Term_CollectPatternVars_collect___lambda__3___closed__10();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__3___closed__10);
l_Lean_Elab_Term_CollectPatternVars_collect___lambda__4___closed__1 = _init_l_Lean_Elab_Term_CollectPatternVars_collect___lambda__4___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__4___closed__1);
l_Lean_Elab_Term_CollectPatternVars_collect___lambda__4___closed__2 = _init_l_Lean_Elab_Term_CollectPatternVars_collect___lambda__4___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__4___closed__2);
l_Lean_Elab_Term_CollectPatternVars_collect___lambda__4___closed__3 = _init_l_Lean_Elab_Term_CollectPatternVars_collect___lambda__4___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__4___closed__3);
l_Lean_Elab_Term_CollectPatternVars_collect___lambda__4___closed__4 = _init_l_Lean_Elab_Term_CollectPatternVars_collect___lambda__4___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__4___closed__4);
l_Lean_Elab_Term_CollectPatternVars_collect___lambda__10___closed__1 = _init_l_Lean_Elab_Term_CollectPatternVars_collect___lambda__10___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__10___closed__1);
l_Lean_Elab_Term_CollectPatternVars_collect___closed__1 = _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect___closed__1);
l_Lean_Elab_Term_CollectPatternVars_collect___closed__2 = _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect___closed__2);
l_Lean_Elab_Term_CollectPatternVars_collect___closed__3 = _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect___closed__3);
l_Lean_Elab_Term_CollectPatternVars_collect___closed__4 = _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect___closed__4);
l_Lean_Elab_Term_CollectPatternVars_collect___closed__5 = _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect___closed__5);
l_Lean_Elab_Term_CollectPatternVars_collect___closed__6 = _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect___closed__6);
l_Lean_Elab_Term_CollectPatternVars_collect___closed__7 = _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__7();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect___closed__7);
l_Lean_Elab_Term_CollectPatternVars_collect___closed__8 = _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__8();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect___closed__8);
l_Lean_Elab_Term_CollectPatternVars_collect___closed__9 = _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__9();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect___closed__9);
l_Lean_Elab_Term_CollectPatternVars_collect___closed__10 = _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__10();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect___closed__10);
l_Lean_Elab_Term_CollectPatternVars_collect___closed__11 = _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__11();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect___closed__11);
l_Lean_Elab_Term_CollectPatternVars_collect___closed__12 = _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__12();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect___closed__12);
l_Lean_Elab_Term_CollectPatternVars_collect___closed__13 = _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__13();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect___closed__13);
l_Lean_Elab_Term_CollectPatternVars_collect___closed__14 = _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__14();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect___closed__14);
l_Lean_Elab_Term_CollectPatternVars_collect___closed__15 = _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__15();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect___closed__15);
l_Lean_Elab_Term_CollectPatternVars_collect___closed__16 = _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__16();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect___closed__16);
l_Lean_Elab_Term_CollectPatternVars_collect___closed__17 = _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__17();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect___closed__17);
l_Lean_Elab_Term_CollectPatternVars_collect___closed__18 = _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__18();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect___closed__18);
l_Lean_Elab_Term_CollectPatternVars_collect___closed__19 = _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__19();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect___closed__19);
l_Lean_Elab_Term_CollectPatternVars_collect___closed__20 = _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__20();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect___closed__20);
l_Lean_Elab_Term_CollectPatternVars_collect___closed__21 = _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__21();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect___closed__21);
l_Lean_Elab_Term_CollectPatternVars_collect___closed__22 = _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__22();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect___closed__22);
l_Lean_Elab_Term_CollectPatternVars_collect___closed__23 = _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__23();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect___closed__23);
l_Lean_Elab_Term_CollectPatternVars_collect___closed__24 = _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__24();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect___closed__24);
l_Lean_Elab_Term_CollectPatternVars_collect___closed__25 = _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__25();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect___closed__25);
l_Lean_addTrace___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__1 = _init_l_Lean_addTrace___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__1();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__1);
l_Lean_addTrace___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__2 = _init_l_Lean_addTrace___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__2();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__2);
l_Lean_addTrace___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__3 = _init_l_Lean_addTrace___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__3();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__3);
l_Lean_addTrace___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__4 = _init_l_Lean_addTrace___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__4();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__4);
l_Lean_addTrace___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__5 = _init_l_Lean_addTrace___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__5();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__5);
l_Lean_addTrace___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__6 = _init_l_Lean_addTrace___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__6();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__6);
l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_main___spec__3___closed__1 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_main___spec__3___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_main___spec__3___closed__1);
l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_main___spec__3___closed__2 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_main___spec__3___closed__2();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_main___spec__3___closed__2);
l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_main___spec__3___closed__3 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_main___spec__3___closed__3();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_main___spec__3___closed__3);
l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_main___spec__3___closed__4 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_main___spec__3___closed__4();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_main___spec__3___closed__4);
l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_main___spec__3___closed__5 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_main___spec__3___closed__5();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_main___spec__3___closed__5);
l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_main___spec__3___closed__6 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_main___spec__3___closed__6();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_main___spec__3___closed__6);
l_Lean_Elab_Term_collectPatternVars___closed__1 = _init_l_Lean_Elab_Term_collectPatternVars___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_collectPatternVars___closed__1);
l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_getPatternsVars___spec__5___closed__1 = _init_l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_getPatternsVars___spec__5___closed__1();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_getPatternsVars___spec__5___closed__1);
l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_getPatternsVars___spec__5___closed__2 = _init_l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_getPatternsVars___spec__5___closed__2();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_getPatternsVars___spec__5___closed__2);
l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_getPatternsVars___spec__6___rarg___closed__1 = _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_getPatternsVars___spec__6___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_getPatternsVars___spec__6___rarg___closed__1);
l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_getPatternsVars___spec__6___rarg___closed__2 = _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_getPatternsVars___spec__6___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_getPatternsVars___spec__6___rarg___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
