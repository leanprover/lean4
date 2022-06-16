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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___closed__8;
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwIllFormedSyntax___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_quotedNameToPattern___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__29;
lean_object* lean_erase_macro_scopes(lean_object*);
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__8___closed__9;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___spec__2___closed__2;
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__11___closed__2;
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Elab_Term_getPatternsVars___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Elab_Term_CollectPatternVars_instInhabitedContext___closed__1;
lean_object* l_Lean_Syntax_getHeadInfo_x3f(lean_object*);
lean_object* l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__1;
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___lambda__2___closed__2;
lean_object* l_Lean_throwError___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___closed__4;
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_pushNewArg___closed__2;
lean_object* l_Lean_LocalDecl_userName(lean_object*);
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___closed__17;
extern lean_object* l_Lean_nullKind;
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__8___closed__8;
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__25;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Array_eraseIdx___rarg(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__8___closed__10;
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Elab_pushInfoLeaf___at_Lean_Elab_Term_addDotCompletionInfo___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___closed__9;
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__2___closed__2;
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__5___closed__1;
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_pushNewArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_resolveGlobalConstNoOverloadWithInfo___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___spec__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_pushNewArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___closed__1;
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
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
static lean_object* l_Lean_Elab_Term_CollectPatternVars_instInhabitedState___closed__1;
static lean_object* l_Lean_addTrace___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__6;
static lean_object* l_Lean_Elab_throwIllFormedSyntax___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_quotedNameToPattern___spec__1___closed__1;
uint8_t l_Lean_Syntax_structEq(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__33;
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___lambda__2___closed__1;
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__14;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_main___spec__3___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__28;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_CollectPatternVars_collect___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___rarg___closed__1;
lean_object* lean_environment_find(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__3___closed__1;
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___lambda__2___closed__3;
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_resolveGlobalConstNoOverload___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__2___closed__3;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_mkAuxName___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_getPatternsVars___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__2___closed__2;
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__2;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_getPatternsVars___spec__6___rarg___closed__1;
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___closed__2;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_main___spec__3___closed__6;
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__30;
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_getPatternsVars___spec__1___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__2___closed__6;
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
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___spec__2___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___spec__2___closed__1;
static lean_object* l_Lean_Elab_throwIllFormedSyntax___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_quotedNameToPattern___spec__1___closed__2;
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__7;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_main___spec__3___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_expandDeclId___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__2___closed__8;
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__3;
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__15;
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_samePatternsVariables(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_getPatternsVars___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___lambda__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_liftExcept___at_Lean_Elab_liftMacroM___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__3___closed__1;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_getPatternsVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern(lean_object*);
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__9;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_samePatternsVariables___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__3;
lean_object* l_Lean_Syntax_SepArray_ofElems(lean_object*, lean_object*);
static lean_object* l_Lean_resolveGlobalConst___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Elab_Term_getPatternsVars___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___lambda__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__8;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_main___spec__3___closed__1;
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
lean_object* l_Lean_Core_withFreshMacroScope___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___closed__4;
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__27;
LEAN_EXPORT uint8_t l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_isDone(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_pushNewArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___closed__12;
lean_object* l_Lean_Syntax_SepArray_getElems___rarg(lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_main___spec__3___closed__4;
lean_object* l_Lean_Syntax_mkApp(lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_getNextParam(lean_object*);
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__8___closed__5;
lean_object* l_Lean_ResolveName_resolveNamespace_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___closed__1;
static lean_object* l_Lean_resolveGlobalConst___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__3___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_isDone___boxed(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Elab_Term_CollectPatternVars_main___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_processExplicitArg___closed__1;
lean_object* l_Lean_Elab_expandMacroImpl_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
extern lean_object* l_Lean_numLitKind;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_Context_newArgs___default;
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__2___closed__5;
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__17;
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_getPatternVarNames(lean_object*);
extern lean_object* l_Lean_strLitKind;
LEAN_EXPORT lean_object* l___private_Init_Meta_0__Array_mapSepElemsMAux___at_Lean_Elab_Term_CollectPatternVars_collect___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_State_found___default;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___spec__2(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_main___spec__3___closed__3;
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___closed__1;
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__8___closed__4;
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstCore___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__5___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_Term_CollectPatternVars_collect___spec__3___closed__1;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__8___closed__1;
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__34;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_processImplicitArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___closed__2;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_Term_CollectPatternVars_collect___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__31;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_getPatternsVars___spec__6___rarg(lean_object*);
static lean_object* l_Lean_addTrace___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__3;
static lean_object* l_panic___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___spec__1___closed__1;
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__9;
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Elab_Term_CollectPatternVars_collect___spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabited___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__4;
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__21;
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__2___closed__7;
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__8;
LEAN_EXPORT uint8_t l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_isNextArgAccessible(lean_object*);
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___closed__19;
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstCore___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__5___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__2;
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_samePatternsVariables___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___closed__11;
lean_object* l_Nat_repr(lean_object*);
static lean_object* l_panic___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___spec__1___closed__2;
uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__9___closed__3;
lean_object* l_Lean_Syntax_getId(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Elab_Term_CollectPatternVars_main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_quotedNameToPattern(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_isNextArgAccessible___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_processCtor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_CollectPatternVars_State_vars___default___closed__1;
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__13;
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*, lean_object*);
uint8_t l_Lean_Name_isAtomic(lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_CollectPatternVars_collect___spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___closed__10;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Elab_Term_getPatternsVars___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkStrLit(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_resolveId_x3f(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_expandApp(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___rarg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedSyntax;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__8___closed__7;
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__12;
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___closed__16;
LEAN_EXPORT lean_object* l___private_Init_Meta_0__Array_mapSepElemsMAux___at_Lean_Elab_Term_CollectPatternVars_collect___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___lambda__2___closed__2;
size_t lean_usize_of_nat(lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_ConstantInfo_type(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_instInhabitedState;
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_getPatternsVars___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__12;
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__9___closed__4;
lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceOptions(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__26;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAtomFrom(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNodeOf(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___spec__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_filterAux___at_Lean_resolveGlobalConstCore___spec__1(lean_object*, lean_object*);
extern uint8_t l_Lean_instInhabitedBinderInfo;
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__11;
extern lean_object* l_Lean_identKind;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_getPatternVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_getPatternsVars___spec__1___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__9___closed__2;
lean_object* l_Std_PersistentArray_push___rarg(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__19;
static lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Elab_Term_CollectPatternVars_collect___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_getPatternsVars___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Elab_Term_CollectPatternVars_collect___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__10;
extern lean_object* l_Lean_Elab_Term_instMonadTermElabM;
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__32;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_processExplicitArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_scientificLitKind;
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__8___closed__3;
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__9___closed__1;
lean_object* l_Lean_Syntax_setArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_main_module(lean_object*);
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__20;
LEAN_EXPORT lean_object* l_Array_mapSepElemsM___at_Lean_Elab_Term_CollectPatternVars_collect___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Elab_Term_CollectPatternVars_main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Elab_Term_CollectPatternVars_collect___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___spec__3(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t l_Lean_TagAttribute_hasTag(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__3___closed__2;
lean_object* l_ReaderT_pure___at_Lean_Elab_liftMacroM___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__11___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_processImplicitArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_getPatternsVars___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_samePatternsVariables___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTRAux___at_Lean_mkConstWithLevelParams___spec__1(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__36;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected(lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_collect___spec__2___closed__3;
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__24;
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_getPatternsVars___spec__1___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_panic___at_Lean_Elab_Term_CollectPatternVars_collect_pushNewArg___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_resolveGlobalName___at_Lean_Elab_Term_resolveName___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_processExplicitArg___closed__3;
extern lean_object* l_Lean_instInhabitedName;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_Context_paramDeclIdx___default;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_CollectPatternVars_collect_processExplicitArg___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__2___closed__1;
lean_object* l_Lean_expandMacros(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_getPatternsVars___spec__1___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_instInhabitedNamedArg;
lean_object* l_Lean_Syntax_isNameLit_x3f(lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__8___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverload___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_getPatternVarNames___spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Elab_Term_getPatternsVars___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___closed__7;
LEAN_EXPORT lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___spec__1___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_getPatternVarNames___spec__1(size_t, size_t, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
LEAN_EXPORT lean_object* l_Lean_Elab_throwIllFormedSyntax___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_quotedNameToPattern___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__16;
static lean_object* l_panic___at_Lean_Elab_Term_CollectPatternVars_collect_pushNewArg___spec__1___closed__1;
lean_object* l_ReaderT_instMonadReaderT___rarg(lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___closed__3;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_processExplicitArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_resolveGlobalConstNoOverloadWithInfo___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_getPatternsVars___spec__5___closed__2;
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Elab_Term_CollectPatternVars_collect___spec__3(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_getPatternsVars___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_processId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_getPatternsVars___spec__7(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_collect___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___closed__18;
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_getPatternsVars___spec__1___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__2___closed__4;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__8___closed__2;
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_getPatternsVars___spec__5___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_collect___spec__2___closed__2;
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___closed__14;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_collect___spec__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_getPatternsVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___closed__15;
static lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__10;
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__2___closed__4;
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___closed__5;
lean_object* l_Lean_Syntax_formatStxAux(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_resolveGlobalConstNoOverload___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__2___closed__1;
static lean_object* l_Lean_throwUnknownConstant___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__6___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___spec__4(lean_object*);
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__12___closed__1;
static lean_object* l_Lean_resolveGlobalConstNoOverload___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__2___closed__2;
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___closed__2;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_getPatternsVars___spec__6___rarg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_pushNewArg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_collect___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___closed__1;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkLit(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_instInhabitedContext;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppContext___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapSepElemsM___at_Lean_Elab_Term_CollectPatternVars_collect___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppContext___lambda__1(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__11___closed__1;
lean_object* l_Lean_Meta_getFVarLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_matchPatternAttr;
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isIdent(lean_object*);
static lean_object* l_Lean_addTrace___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_getPatternsVars___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_State_found___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_NameSet_empty;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_State_vars___default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_State_vars___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_CollectPatternVars_State_vars___default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_instInhabitedState___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_NameSet_empty;
x_2 = l_Lean_Elab_Term_CollectPatternVars_State_vars___default___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_instInhabitedState() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_CollectPatternVars_instInhabitedState___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwCtorExpected___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_7, 5);
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
x_1 = lean_mk_string_from_bytes("invalid pattern, constructor or constant marked with '[matchPattern]' expected", 78);
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
x_10 = lean_ctor_get(x_7, 5);
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
x_1 = lean_mk_string_from_bytes("invalid pattern", 15);
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
x_1 = l_Lean_Elab_Term_CollectPatternVars_State_vars___default___closed__1;
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
x_5 = l_Lean_Elab_Term_CollectPatternVars_State_vars___default___closed__1;
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
x_10 = lean_ctor_get(x_7, 5);
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
x_4 = lean_ctor_get(x_1, 5);
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
x_1 = lean_mk_string_from_bytes("too many arguments", 18);
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
x_1 = lean_mk_string_from_bytes("Lean", 4);
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
x_1 = lean_mk_string_from_bytes("Parser", 6);
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
x_1 = lean_mk_string_from_bytes("Term", 4);
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
x_1 = lean_mk_string_from_bytes("explicit", 8);
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
x_1 = lean_mk_string_from_bytes("@", 1);
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
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___spec__2___rarg(x_7, x_8, x_9);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_st_ref_get(x_8, x_20);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
x_24 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__11;
x_25 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_25, 0, x_19);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
x_27 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__12;
x_28 = lean_array_push(x_27, x_25);
x_29 = lean_array_push(x_28, x_26);
x_30 = lean_box(2);
x_31 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__10;
x_32 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_32, 2, x_29);
x_33 = lean_ctor_get(x_1, 6);
lean_inc(x_33);
lean_dec(x_1);
x_34 = l_Lean_Syntax_mkApp(x_32, x_33);
lean_ctor_set(x_21, 0, x_34);
return x_21;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_35 = lean_ctor_get(x_21, 1);
lean_inc(x_35);
lean_dec(x_21);
x_36 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__11;
x_37 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_37, 0, x_19);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_ctor_get(x_1, 0);
lean_inc(x_38);
x_39 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__12;
x_40 = lean_array_push(x_39, x_37);
x_41 = lean_array_push(x_40, x_38);
x_42 = lean_box(2);
x_43 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__10;
x_44 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set(x_44, 2, x_41);
x_45 = lean_ctor_get(x_1, 6);
lean_inc(x_45);
lean_dec(x_1);
x_46 = l_Lean_Syntax_mkApp(x_44, x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_35);
return x_47;
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
x_10 = lean_ctor_get(x_7, 5);
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
x_12 = lean_ctor_get(x_8, 5);
x_13 = l_Lean_replaceRef(x_1, x_12);
lean_dec(x_12);
lean_dec(x_1);
lean_ctor_set(x_8, 5, x_13);
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
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_15 = lean_ctor_get(x_8, 0);
x_16 = lean_ctor_get(x_8, 1);
x_17 = lean_ctor_get(x_8, 2);
x_18 = lean_ctor_get(x_8, 3);
x_19 = lean_ctor_get(x_8, 4);
x_20 = lean_ctor_get(x_8, 5);
x_21 = lean_ctor_get(x_8, 6);
x_22 = lean_ctor_get(x_8, 7);
x_23 = lean_ctor_get(x_8, 8);
x_24 = lean_ctor_get(x_8, 9);
x_25 = lean_ctor_get(x_8, 10);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_8);
x_26 = l_Lean_replaceRef(x_1, x_20);
lean_dec(x_20);
lean_dec(x_1);
x_27 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_27, 0, x_15);
lean_ctor_set(x_27, 1, x_16);
lean_ctor_set(x_27, 2, x_17);
lean_ctor_set(x_27, 3, x_18);
lean_ctor_set(x_27, 4, x_19);
lean_ctor_set(x_27, 5, x_26);
lean_ctor_set(x_27, 6, x_21);
lean_ctor_set(x_27, 7, x_22);
lean_ctor_set(x_27, 8, x_23);
lean_ctor_set(x_27, 9, x_24);
lean_ctor_set(x_27, 10, x_25);
x_28 = l_Lean_throwError___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___spec__1(x_2, x_3, x_4, x_5, x_6, x_7, x_27, x_9, x_10);
lean_dec(x_9);
lean_dec(x_27);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
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
x_19 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_17, x_1, x_18);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_dec(x_15);
lean_inc(x_2);
x_21 = lean_array_push(x_20, x_2);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_st_ref_set(x_4, x_22, x_16);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
lean_ctor_set(x_23, 0, x_2);
return x_23;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_2);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("invalid pattern, variable '", 27);
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
x_1 = lean_mk_string_from_bytes("' occurred more than once", 25);
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
x_1 = lean_mk_string_from_bytes("invalid pattern variable, must be atomic", 40);
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
x_1 = lean_mk_string_from_bytes("identifier expected", 19);
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
x_4 = lean_ctor_get(x_1, 5);
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
x_1 = lean_mk_string_from_bytes("Name.anonymous", 14);
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
x_1 = lean_mk_string_from_bytes("Name", 4);
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
x_1 = lean_mk_string_from_bytes("anonymous", 9);
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
x_1 = lean_mk_string_from_bytes("app", 3);
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
x_1 = lean_mk_string_from_bytes("Name.str", 8);
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
x_1 = lean_mk_string_from_bytes("str", 3);
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
x_1 = lean_mk_string_from_bytes("null", 4);
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
x_1 = lean_mk_string_from_bytes("hole", 4);
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
x_1 = lean_mk_string_from_bytes("_", 1);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__29() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Name.num", 8);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__29;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__29;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__30;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__32() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("num", 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__5;
x_2 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__32;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__34() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__8;
x_2 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__32;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__35() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__34;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__36() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__35;
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_inc(x_6);
x_9 = l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___spec__1___rarg(x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_6, 10);
lean_inc(x_12);
lean_dec(x_6);
x_13 = lean_st_ref_get(x_7, x_11);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_environment_main_module(x_16);
x_18 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__7;
x_19 = l_Lean_addMacroScope(x_17, x_18, x_12);
x_20 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__3;
x_21 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__11;
x_22 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_22, 0, x_10);
lean_ctor_set(x_22, 1, x_20);
lean_ctor_set(x_22, 2, x_19);
lean_ctor_set(x_22, 3, x_21);
lean_ctor_set(x_13, 0, x_22);
return x_13;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_23 = lean_ctor_get(x_13, 0);
x_24 = lean_ctor_get(x_13, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_13);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_environment_main_module(x_25);
x_27 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__7;
x_28 = l_Lean_addMacroScope(x_26, x_27, x_12);
x_29 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__3;
x_30 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__11;
x_31 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_31, 0, x_10);
lean_ctor_set(x_31, 1, x_29);
lean_ctor_set(x_31, 2, x_28);
lean_ctor_set(x_31, 3, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_24);
return x_32;
}
}
case 1:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_33 = lean_ctor_get(x_1, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_1, 1);
lean_inc(x_34);
lean_dec(x_1);
lean_inc(x_6);
x_35 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern(x_33, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
lean_inc(x_6);
x_38 = l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___spec__1___rarg(x_6, x_7, x_37);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_ctor_get(x_6, 10);
lean_inc(x_41);
lean_dec(x_6);
x_42 = lean_st_ref_get(x_7, x_40);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_44 = lean_ctor_get(x_42, 0);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_environment_main_module(x_45);
x_47 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__18;
x_48 = l_Lean_addMacroScope(x_46, x_47, x_41);
x_49 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__16;
x_50 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__21;
lean_inc(x_39);
x_51 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_51, 0, x_39);
lean_ctor_set(x_51, 1, x_49);
lean_ctor_set(x_51, 2, x_48);
lean_ctor_set(x_51, 3, x_50);
x_52 = lean_box(2);
x_53 = l_Lean_Syntax_mkStrLit(x_34, x_52);
lean_dec(x_34);
x_54 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__26;
x_55 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_55, 0, x_39);
lean_ctor_set(x_55, 1, x_54);
x_56 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__27;
x_57 = lean_array_push(x_56, x_55);
x_58 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__25;
x_59 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_59, 0, x_52);
lean_ctor_set(x_59, 1, x_58);
lean_ctor_set(x_59, 2, x_57);
x_60 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__28;
x_61 = lean_array_push(x_60, x_36);
x_62 = lean_array_push(x_61, x_53);
x_63 = lean_array_push(x_62, x_59);
x_64 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__23;
x_65 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_65, 0, x_52);
lean_ctor_set(x_65, 1, x_64);
lean_ctor_set(x_65, 2, x_63);
x_66 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__12;
x_67 = lean_array_push(x_66, x_51);
x_68 = lean_array_push(x_67, x_65);
x_69 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__13;
x_70 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_70, 0, x_52);
lean_ctor_set(x_70, 1, x_69);
lean_ctor_set(x_70, 2, x_68);
lean_ctor_set(x_42, 0, x_70);
return x_42;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_71 = lean_ctor_get(x_42, 0);
x_72 = lean_ctor_get(x_42, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_42);
x_73 = lean_ctor_get(x_71, 0);
lean_inc(x_73);
lean_dec(x_71);
x_74 = lean_environment_main_module(x_73);
x_75 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__18;
x_76 = l_Lean_addMacroScope(x_74, x_75, x_41);
x_77 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__16;
x_78 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__21;
lean_inc(x_39);
x_79 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_79, 0, x_39);
lean_ctor_set(x_79, 1, x_77);
lean_ctor_set(x_79, 2, x_76);
lean_ctor_set(x_79, 3, x_78);
x_80 = lean_box(2);
x_81 = l_Lean_Syntax_mkStrLit(x_34, x_80);
lean_dec(x_34);
x_82 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__26;
x_83 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_83, 0, x_39);
lean_ctor_set(x_83, 1, x_82);
x_84 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__27;
x_85 = lean_array_push(x_84, x_83);
x_86 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__25;
x_87 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_87, 0, x_80);
lean_ctor_set(x_87, 1, x_86);
lean_ctor_set(x_87, 2, x_85);
x_88 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__28;
x_89 = lean_array_push(x_88, x_36);
x_90 = lean_array_push(x_89, x_81);
x_91 = lean_array_push(x_90, x_87);
x_92 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__23;
x_93 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_93, 0, x_80);
lean_ctor_set(x_93, 1, x_92);
lean_ctor_set(x_93, 2, x_91);
x_94 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__12;
x_95 = lean_array_push(x_94, x_79);
x_96 = lean_array_push(x_95, x_93);
x_97 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__13;
x_98 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_98, 0, x_80);
lean_ctor_set(x_98, 1, x_97);
lean_ctor_set(x_98, 2, x_96);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_72);
return x_99;
}
}
default: 
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_100 = lean_ctor_get(x_1, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_1, 1);
lean_inc(x_101);
lean_dec(x_1);
lean_inc(x_6);
x_102 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern(x_100, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
lean_inc(x_6);
x_105 = l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___spec__1___rarg(x_6, x_7, x_104);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_108 = lean_ctor_get(x_6, 10);
lean_inc(x_108);
lean_dec(x_6);
x_109 = lean_st_ref_get(x_7, x_107);
x_110 = !lean_is_exclusive(x_109);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_111 = lean_ctor_get(x_109, 0);
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
lean_dec(x_111);
x_113 = lean_environment_main_module(x_112);
x_114 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__33;
x_115 = l_Lean_addMacroScope(x_113, x_114, x_108);
x_116 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__31;
x_117 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__36;
lean_inc(x_106);
x_118 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_118, 0, x_106);
lean_ctor_set(x_118, 1, x_116);
lean_ctor_set(x_118, 2, x_115);
lean_ctor_set(x_118, 3, x_117);
x_119 = l_Nat_repr(x_101);
x_120 = l_Lean_numLitKind;
x_121 = lean_box(2);
x_122 = l_Lean_Syntax_mkLit(x_120, x_119, x_121);
x_123 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__26;
x_124 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_124, 0, x_106);
lean_ctor_set(x_124, 1, x_123);
x_125 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__27;
x_126 = lean_array_push(x_125, x_124);
x_127 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__25;
x_128 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_128, 0, x_121);
lean_ctor_set(x_128, 1, x_127);
lean_ctor_set(x_128, 2, x_126);
x_129 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__28;
x_130 = lean_array_push(x_129, x_103);
x_131 = lean_array_push(x_130, x_122);
x_132 = lean_array_push(x_131, x_128);
x_133 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__23;
x_134 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_134, 0, x_121);
lean_ctor_set(x_134, 1, x_133);
lean_ctor_set(x_134, 2, x_132);
x_135 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__12;
x_136 = lean_array_push(x_135, x_118);
x_137 = lean_array_push(x_136, x_134);
x_138 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__13;
x_139 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_139, 0, x_121);
lean_ctor_set(x_139, 1, x_138);
lean_ctor_set(x_139, 2, x_137);
lean_ctor_set(x_109, 0, x_139);
return x_109;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_140 = lean_ctor_get(x_109, 0);
x_141 = lean_ctor_get(x_109, 1);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_109);
x_142 = lean_ctor_get(x_140, 0);
lean_inc(x_142);
lean_dec(x_140);
x_143 = lean_environment_main_module(x_142);
x_144 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__33;
x_145 = l_Lean_addMacroScope(x_143, x_144, x_108);
x_146 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__31;
x_147 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__36;
lean_inc(x_106);
x_148 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_148, 0, x_106);
lean_ctor_set(x_148, 1, x_146);
lean_ctor_set(x_148, 2, x_145);
lean_ctor_set(x_148, 3, x_147);
x_149 = l_Nat_repr(x_101);
x_150 = l_Lean_numLitKind;
x_151 = lean_box(2);
x_152 = l_Lean_Syntax_mkLit(x_150, x_149, x_151);
x_153 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__26;
x_154 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_154, 0, x_106);
lean_ctor_set(x_154, 1, x_153);
x_155 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__27;
x_156 = lean_array_push(x_155, x_154);
x_157 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__25;
x_158 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_158, 0, x_151);
lean_ctor_set(x_158, 1, x_157);
lean_ctor_set(x_158, 2, x_156);
x_159 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__28;
x_160 = lean_array_push(x_159, x_103);
x_161 = lean_array_push(x_160, x_152);
x_162 = lean_array_push(x_161, x_158);
x_163 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__23;
x_164 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_164, 0, x_151);
lean_ctor_set(x_164, 1, x_163);
lean_ctor_set(x_164, 2, x_162);
x_165 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__12;
x_166 = lean_array_push(x_165, x_148);
x_167 = lean_array_push(x_166, x_164);
x_168 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__13;
x_169 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_169, 0, x_151);
lean_ctor_set(x_169, 1, x_168);
lean_ctor_set(x_169, 2, x_167);
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_141);
return x_170;
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
x_1 = lean_mk_string_from_bytes("ill-formed syntax", 17);
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
x_11 = lean_ctor_get(x_7, 5);
x_12 = l_Lean_replaceRef(x_1, x_11);
lean_dec(x_11);
lean_ctor_set(x_7, 5, x_12);
x_13 = l_Lean_throwError___at_Lean_Elab_Term_expandDeclId___spec__11(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_7, 1);
x_16 = lean_ctor_get(x_7, 2);
x_17 = lean_ctor_get(x_7, 3);
x_18 = lean_ctor_get(x_7, 4);
x_19 = lean_ctor_get(x_7, 5);
x_20 = lean_ctor_get(x_7, 6);
x_21 = lean_ctor_get(x_7, 7);
x_22 = lean_ctor_get(x_7, 8);
x_23 = lean_ctor_get(x_7, 9);
x_24 = lean_ctor_get(x_7, 10);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_7);
x_25 = l_Lean_replaceRef(x_1, x_19);
lean_dec(x_19);
x_26 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_26, 0, x_14);
lean_ctor_set(x_26, 1, x_15);
lean_ctor_set(x_26, 2, x_16);
lean_ctor_set(x_26, 3, x_17);
lean_ctor_set(x_26, 4, x_18);
lean_ctor_set(x_26, 5, x_25);
lean_ctor_set(x_26, 6, x_20);
lean_ctor_set(x_26, 7, x_21);
lean_ctor_set(x_26, 8, x_22);
lean_ctor_set(x_26, 9, x_23);
lean_ctor_set(x_26, 10, x_24);
x_27 = l_Lean_throwError___at_Lean_Elab_Term_expandDeclId___spec__11(x_2, x_3, x_4, x_5, x_6, x_26, x_8, x_9);
lean_dec(x_26);
return x_27;
}
}
}
static lean_object* _init_l_Lean_throwUnknownConstant___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unknown constant '", 18);
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
x_1 = lean_mk_string_from_bytes("'", 1);
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
x_1 = lean_mk_string_from_bytes("expected identifier", 19);
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
x_15 = lean_ctor_get(x_6, 5);
x_16 = l_Lean_replaceRef(x_1, x_15);
lean_dec(x_15);
lean_dec(x_1);
lean_ctor_set(x_6, 5, x_16);
x_17 = l_Lean_resolveGlobalConstCore___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__5(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_18 = lean_ctor_get(x_6, 0);
x_19 = lean_ctor_get(x_6, 1);
x_20 = lean_ctor_get(x_6, 2);
x_21 = lean_ctor_get(x_6, 3);
x_22 = lean_ctor_get(x_6, 4);
x_23 = lean_ctor_get(x_6, 5);
x_24 = lean_ctor_get(x_6, 6);
x_25 = lean_ctor_get(x_6, 7);
x_26 = lean_ctor_get(x_6, 8);
x_27 = lean_ctor_get(x_6, 9);
x_28 = lean_ctor_get(x_6, 10);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_6);
x_29 = l_Lean_replaceRef(x_1, x_23);
lean_dec(x_23);
lean_dec(x_1);
x_30 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_30, 0, x_18);
lean_ctor_set(x_30, 1, x_19);
lean_ctor_set(x_30, 2, x_20);
lean_ctor_set(x_30, 3, x_21);
lean_ctor_set(x_30, 4, x_22);
lean_ctor_set(x_30, 5, x_29);
lean_ctor_set(x_30, 6, x_24);
lean_ctor_set(x_30, 7, x_25);
lean_ctor_set(x_30, 8, x_26);
lean_ctor_set(x_30, 9, x_27);
lean_ctor_set(x_30, 10, x_28);
x_31 = l_Lean_resolveGlobalConstCore___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__5(x_9, x_2, x_3, x_4, x_5, x_30, x_7, x_8);
return x_31;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = l_Lean_resolveGlobalConst___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__3___closed__3;
x_33 = l_Lean_throwErrorAt___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__4(x_1, x_32, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_33;
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
x_11 = lean_ctor_get(x_7, 5);
x_12 = l_Lean_replaceRef(x_1, x_11);
lean_dec(x_11);
lean_ctor_set(x_7, 5, x_12);
x_13 = l_Lean_throwError___at_Lean_Elab_Term_mkAuxName___spec__1(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_7, 1);
x_16 = lean_ctor_get(x_7, 2);
x_17 = lean_ctor_get(x_7, 3);
x_18 = lean_ctor_get(x_7, 4);
x_19 = lean_ctor_get(x_7, 5);
x_20 = lean_ctor_get(x_7, 6);
x_21 = lean_ctor_get(x_7, 7);
x_22 = lean_ctor_get(x_7, 8);
x_23 = lean_ctor_get(x_7, 9);
x_24 = lean_ctor_get(x_7, 10);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_7);
x_25 = l_Lean_replaceRef(x_1, x_19);
lean_dec(x_19);
x_26 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_26, 0, x_14);
lean_ctor_set(x_26, 1, x_15);
lean_ctor_set(x_26, 2, x_16);
lean_ctor_set(x_26, 3, x_17);
lean_ctor_set(x_26, 4, x_18);
lean_ctor_set(x_26, 5, x_25);
lean_ctor_set(x_26, 6, x_20);
lean_ctor_set(x_26, 7, x_21);
lean_ctor_set(x_26, 8, x_22);
lean_ctor_set(x_26, 9, x_23);
lean_ctor_set(x_26, 10, x_24);
x_27 = l_Lean_throwError___at_Lean_Elab_Term_mkAuxName___spec__1(x_2, x_3, x_4, x_5, x_6, x_26, x_8, x_9);
lean_dec(x_26);
return x_27;
}
}
}
static lean_object* _init_l_Lean_resolveGlobalConstNoOverload___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("ambiguous identifier '", 22);
return x_1;
}
}
static lean_object* _init_l_Lean_resolveGlobalConstNoOverload___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("', possible interpretations: ", 29);
return x_1;
}
}
static lean_object* _init_l_Lean_resolveGlobalConstNoOverload___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
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
x_26 = l_Lean_resolveGlobalConstNoOverload___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__2___closed__3;
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
x_53 = l_Lean_resolveGlobalConstNoOverload___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__2___closed__3;
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
x_17 = lean_ctor_get(x_16, 4);
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
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_samePatternsVariables___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_4);
x_8 = lean_nat_dec_lt(x_6, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_6);
x_9 = 1;
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_array_fget(x_4, x_6);
x_11 = lean_array_fget(x_5, x_6);
x_12 = l_Lean_Syntax_structEq(x_10, x_11);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_6);
x_13 = 0;
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_6, x_14);
lean_dec(x_6);
x_3 = lean_box(0);
x_6 = x_15;
goto _start;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_samePatternsVariables(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_array_get_size(x_4);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
x_7 = lean_array_get_size(x_6);
x_8 = lean_nat_dec_eq(x_5, x_7);
lean_dec(x_7);
lean_dec(x_5);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = 0;
return x_9;
}
else
{
uint8_t x_10; 
x_10 = l_Array_isEqvAux___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_samePatternsVariables___spec__1(x_2, x_3, lean_box(0), x_4, x_6, x_1);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_samePatternsVariables___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Array_isEqvAux___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_samePatternsVariables___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_samePatternsVariables___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_samePatternsVariables(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
static lean_object* _init_l_panic___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_instMonadTermElabM;
x_2 = l_ReaderT_instMonadReaderT___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_panic___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___spec__1___closed__1;
x_2 = l_Lean_instInhabitedSyntax;
x_3 = l_instInhabited___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_panic___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___spec__1___closed__2;
x_11 = lean_panic_fn(x_10, x_1);
x_12 = lean_apply_8(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Elab.PatternVar", 20);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___spec__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Elab.Term.CollectPatternVars.collect.processCtorApp", 56);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___spec__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unreachable code has been reached", 33);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___spec__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___spec__2___closed__1;
x_2 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___spec__2___closed__2;
x_3 = lean_unsigned_to_nat(242u);
x_4 = lean_unsigned_to_nat(74u);
x_5 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___spec__2___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___spec__2(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_array_uget(x_3, x_2);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_uset(x_3, x_2, x_15);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
lean_dec(x_14);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_18 = l_Lean_Elab_Term_CollectPatternVars_collect(x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = 1;
x_22 = lean_usize_add(x_2, x_21);
x_23 = lean_array_uset(x_16, x_2, x_19);
x_2 = x_22;
x_3 = x_23;
x_11 = x_20;
goto _start;
}
else
{
uint8_t x_25; 
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_25 = !lean_is_exclusive(x_18);
if (x_25 == 0)
{
return x_18;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_18, 0);
x_27 = lean_ctor_get(x_18, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_18);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_14);
x_29 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___spec__2___closed__4;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_30 = l_panic___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___spec__1(x_29, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; size_t x_33; size_t x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = 1;
x_34 = lean_usize_add(x_2, x_33);
x_35 = lean_array_uset(x_16, x_2, x_31);
x_2 = x_34;
x_3 = x_35;
x_11 = x_32;
goto _start;
}
else
{
uint8_t x_37; 
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_37 = !lean_is_exclusive(x_30);
if (x_37 == 0)
{
return x_30;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_30, 0);
x_39 = lean_ctor_get(x_30, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_30);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_Syntax_mkApp(x_1, x_2);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("ellipsis", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("..", 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___lambda__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
lean_dec(x_6);
x_15 = lean_array_get_size(x_1);
x_16 = lean_usize_of_nat(x_15);
lean_dec(x_15);
x_17 = 0;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_18 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___spec__2(x_16, x_17, x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_18) == 0)
{
if (x_3 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_5);
lean_dec(x_4);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_box(0);
x_22 = l_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___lambda__1(x_2, x_19, x_21, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_20);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_23 = lean_ctor_get(x_18, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
lean_dec(x_18);
x_25 = l_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___lambda__2___closed__1;
x_26 = lean_name_mk_string(x_4, x_25);
x_27 = l_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___lambda__2___closed__2;
x_28 = l_Lean_mkAtomFrom(x_5, x_27);
x_29 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__27;
x_30 = lean_array_push(x_29, x_28);
x_31 = lean_box(2);
x_32 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_26);
lean_ctor_set(x_32, 2, x_30);
x_33 = lean_array_push(x_23, x_32);
x_34 = lean_box(0);
x_35 = l_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___lambda__1(x_2, x_33, x_34, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_24);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_36 = !lean_is_exclusive(x_18);
if (x_36 == 0)
{
return x_18;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_18, 0);
x_38 = lean_ctor_get(x_18, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_18);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("dotIdent", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__8;
x_2 = l_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("invalid dotted notation in a pattern, named arguments are not supported yet", 75);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
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
x_11 = l_Lean_Elab_Term_expandApp(x_1, x_10, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
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
lean_inc(x_16);
x_20 = l_Lean_Syntax_getKind(x_16);
x_21 = l_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___closed__2;
x_22 = lean_name_eq(x_20, x_21);
lean_dec(x_20);
if (x_22 == 0)
{
uint8_t x_23; lean_object* x_24; 
lean_dec(x_1);
x_23 = lean_unbox(x_19);
lean_dec(x_19);
x_24 = l_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore(x_16, x_17, x_18, x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_15);
return x_24;
}
else
{
uint8_t x_25; 
x_25 = l_Array_isEmpty___rarg(x_17);
lean_dec(x_17);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_1);
x_26 = l_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___closed__4;
x_27 = l_Lean_throwError___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___spec__1(x_26, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_15);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
return x_27;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_27);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; 
x_32 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__8;
x_33 = lean_box(0);
x_34 = lean_unbox(x_19);
lean_dec(x_19);
x_35 = l_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___lambda__2(x_18, x_16, x_34, x_32, x_1, x_33, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_15);
return x_35;
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_11);
if (x_36 == 0)
{
return x_11;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_11, 0);
x_38 = lean_ctor_get(x_11, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_11);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorAppCore___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_7, 5);
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
x_10 = lean_ctor_get(x_7, 5);
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
x_1 = lean_mk_string_from_bytes("pattern", 7);
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
x_35 = l_Lean_Elab_Term_CollectPatternVars_State_vars___default___closed__1;
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
x_50 = l_Lean_Elab_Term_CollectPatternVars_State_vars___default___closed__1;
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
x_78 = l_Lean_Elab_Term_CollectPatternVars_State_vars___default___closed__1;
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
x_93 = l_Lean_Elab_Term_CollectPatternVars_State_vars___default___closed__1;
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
x_1 = lean_mk_string_from_bytes("ident", 5);
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
x_10 = lean_ctor_get(x_7, 5);
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
x_1 = lean_mk_string_from_bytes("explicit parameter is missing, unused named arguments ", 54);
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
x_1 = l_Lean_resolveGlobalConstNoOverload___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__2___closed__3;
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
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_inc(x_8);
x_27 = l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___spec__2___rarg(x_8, x_9, x_10);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_st_ref_get(x_9, x_29);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__26;
x_33 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_33, 0, x_28);
lean_ctor_set(x_33, 1, x_32);
x_34 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__27;
x_35 = lean_array_push(x_34, x_33);
x_36 = lean_box(2);
x_37 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__25;
x_38 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set(x_38, 2, x_35);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_40 = l_Lean_Elab_Term_CollectPatternVars_collect_pushNewArg(x_1, x_2, x_39, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_31);
return x_40;
}
}
else
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_2);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_2, 5);
lean_dec(x_42);
x_43 = lean_ctor_get(x_11, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_11, 1);
lean_inc(x_44);
lean_dec(x_11);
lean_ctor_set(x_2, 5, x_44);
x_45 = l_Lean_Elab_Term_CollectPatternVars_collect_pushNewArg(x_1, x_2, x_43, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_46 = lean_ctor_get(x_2, 0);
x_47 = lean_ctor_get(x_2, 1);
x_48 = lean_ctor_get_uint8(x_2, sizeof(void*)*7);
x_49 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 1);
x_50 = lean_ctor_get(x_2, 2);
x_51 = lean_ctor_get(x_2, 3);
x_52 = lean_ctor_get(x_2, 4);
x_53 = lean_ctor_get(x_2, 6);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_2);
x_54 = lean_ctor_get(x_11, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_11, 1);
lean_inc(x_55);
lean_dec(x_11);
x_56 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_56, 0, x_46);
lean_ctor_set(x_56, 1, x_47);
lean_ctor_set(x_56, 2, x_50);
lean_ctor_set(x_56, 3, x_51);
lean_ctor_set(x_56, 4, x_52);
lean_ctor_set(x_56, 5, x_55);
lean_ctor_set(x_56, 6, x_53);
lean_ctor_set_uint8(x_56, sizeof(void*)*7, x_48);
lean_ctor_set_uint8(x_56, sizeof(void*)*7 + 1, x_49);
x_57 = l_Lean_Elab_Term_CollectPatternVars_collect_pushNewArg(x_1, x_56, x_54, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_57;
}
}
}
}
static lean_object* _init_l_panic___at_Lean_Elab_Term_CollectPatternVars_collect_pushNewArg___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_panic___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___spec__1___closed__1;
x_2 = l_Lean_Elab_Term_CollectPatternVars_instInhabitedContext;
x_3 = l_instInhabited___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Elab_Term_CollectPatternVars_collect_pushNewArg___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_panic___at_Lean_Elab_Term_CollectPatternVars_collect_pushNewArg___spec__1___closed__1;
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
x_1 = lean_mk_string_from_bytes("Lean.Elab.Term.CollectPatternVars.collect.pushNewArg", 52);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect_pushNewArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___spec__2___closed__1;
x_2 = l_Lean_Elab_Term_CollectPatternVars_collect_pushNewArg___closed__1;
x_3 = lean_unsigned_to_nat(273u);
x_4 = lean_unsigned_to_nat(11u);
x_5 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___spec__2___closed__3;
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
x_23 = l_Lean_Elab_Term_CollectPatternVars_collect_pushNewArg___closed__2;
x_24 = l_panic___at_Lean_Elab_Term_CollectPatternVars_collect_pushNewArg___spec__1(x_23, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_24;
}
}
}
static lean_object* _init_l_Subarray_forInUnsafe_loop___at_Lean_Elab_Term_CollectPatternVars_collect___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("invalid pattern, overloaded notation is only allowed when all alternative have the same set of pattern variables", 112);
return x_1;
}
}
static lean_object* _init_l_Subarray_forInUnsafe_loop___at_Lean_Elab_Term_CollectPatternVars_collect___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Subarray_forInUnsafe_loop___at_Lean_Elab_Term_CollectPatternVars_collect___spec__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Elab_Term_CollectPatternVars_collect___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = lean_usize_dec_lt(x_5, x_4);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_6);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_17 = lean_ctor_get(x_3, 0);
x_18 = lean_array_uget(x_17, x_5);
x_26 = lean_st_ref_get(x_13, x_14);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
lean_inc(x_1);
x_28 = lean_st_ref_set(x_7, x_1, x_27);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_30 = l_Lean_Elab_Term_CollectPatternVars_collect(x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_array_push(x_6, x_31);
x_34 = lean_st_ref_get(x_13, x_32);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_st_ref_get(x_7, x_35);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_ctor_get(x_1, 1);
lean_inc(x_39);
x_40 = lean_array_get_size(x_39);
lean_dec(x_39);
lean_inc(x_2);
x_41 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_samePatternsVariables(x_40, x_2, x_37);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
lean_dec(x_33);
lean_dec(x_2);
lean_dec(x_1);
x_42 = l_Subarray_forInUnsafe_loop___at_Lean_Elab_Term_CollectPatternVars_collect___spec__1___closed__2;
x_43 = l_Lean_throwError___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___spec__1(x_42, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_38);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
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
lean_object* x_48; 
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_33);
x_19 = x_48;
x_20 = x_38;
goto block_25;
}
}
else
{
uint8_t x_49; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_30);
if (x_49 == 0)
{
return x_30;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_30, 0);
x_51 = lean_ctor_get(x_30, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_30);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
block_25:
{
lean_object* x_21; size_t x_22; size_t x_23; 
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_22 = 1;
x_23 = lean_usize_add(x_5, x_22);
x_5 = x_23;
x_6 = x_21;
x_14 = x_20;
goto _start;
}
}
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_collect___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("structInstField", 15);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_collect___spec__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("structInstLVal", 14);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_collect___spec__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(":=", 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_collect___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_15 = lean_array_uget(x_4, x_3);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_uset(x_4, x_3, x_16);
x_18 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_collect___spec__2___closed__1;
lean_inc(x_1);
x_19 = lean_name_mk_string(x_1, x_18);
lean_inc(x_15);
x_20 = l_Lean_Syntax_isOfKind(x_15, x_19);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_1);
x_21 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___rarg(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
return x_21;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_21);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = l_Lean_Syntax_getArg(x_15, x_16);
x_27 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_collect___spec__2___closed__2;
lean_inc(x_1);
x_28 = lean_name_mk_string(x_1, x_27);
lean_inc(x_26);
x_29 = l_Lean_Syntax_isOfKind(x_26, x_28);
lean_dec(x_28);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
lean_dec(x_26);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_1);
x_30 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___rarg(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_unsigned_to_nat(2u);
x_36 = l_Lean_Syntax_getArg(x_15, x_35);
lean_dec(x_15);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_37 = l_Lean_Elab_Term_CollectPatternVars_collect(x_36, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; size_t x_53; size_t x_54; lean_object* x_55; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
lean_inc(x_10);
x_40 = l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___spec__2___rarg(x_10, x_11, x_39);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_st_ref_get(x_11, x_42);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_45 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_collect___spec__2___closed__3;
x_46 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_46, 0, x_41);
lean_ctor_set(x_46, 1, x_45);
x_47 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__28;
x_48 = lean_array_push(x_47, x_26);
x_49 = lean_array_push(x_48, x_46);
x_50 = lean_array_push(x_49, x_38);
x_51 = lean_box(2);
x_52 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_19);
lean_ctor_set(x_52, 2, x_50);
x_53 = 1;
x_54 = lean_usize_add(x_3, x_53);
x_55 = lean_array_uset(x_17, x_3, x_52);
x_3 = x_54;
x_4 = x_55;
x_12 = x_44;
goto _start;
}
else
{
uint8_t x_57; 
lean_dec(x_26);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_37);
if (x_57 == 0)
{
return x_37;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_37, 0);
x_59 = lean_ctor_get(x_37, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_37);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
}
}
}
static lean_object* _init_l_Array_anyMUnsafe_any___at_Lean_Elab_Term_CollectPatternVars_collect___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("structInst", 10);
return x_1;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Elab_Term_CollectPatternVars_collect___spec__3(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = l_Array_anyMUnsafe_any___at_Lean_Elab_Term_CollectPatternVars_collect___spec__3___closed__1;
lean_inc(x_1);
x_8 = lean_name_mk_string(x_1, x_7);
x_9 = l_Lean_Syntax_isOfKind(x_6, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
size_t x_10; size_t x_11; 
x_10 = 1;
x_11 = lean_usize_add(x_3, x_10);
x_3 = x_11;
goto _start;
}
else
{
uint8_t x_13; 
lean_dec(x_1);
x_13 = 1;
return x_13;
}
}
else
{
uint8_t x_14; 
lean_dec(x_1);
x_14 = 0;
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_CollectPatternVars_collect___spec__4(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; size_t x_11; size_t x_12; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = l_Array_anyMUnsafe_any___at_Lean_Elab_Term_CollectPatternVars_collect___spec__3___closed__1;
lean_inc(x_1);
x_9 = lean_name_mk_string(x_1, x_8);
lean_inc(x_7);
x_10 = l_Lean_Syntax_isOfKind(x_7, x_9);
lean_dec(x_9);
x_11 = 1;
x_12 = lean_usize_add(x_3, x_11);
if (x_10 == 0)
{
lean_dec(x_7);
x_3 = x_12;
goto _start;
}
else
{
lean_object* x_14; 
x_14 = lean_array_push(x_5, x_7);
x_3 = x_12;
x_5 = x_14;
goto _start;
}
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_0__Array_mapSepElemsMAux___at_Lean_Elab_Term_CollectPatternVars_collect___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
LEAN_EXPORT lean_object* l_Array_mapSepElemsM___at_Lean_Elab_Term_CollectPatternVars_collect___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_Elab_Term_CollectPatternVars_State_vars___default___closed__1;
x_13 = l___private_Init_Meta_0__Array_mapSepElemsMAux___at_Lean_Elab_Term_CollectPatternVars_collect___spec__6(x_1, x_2, x_11, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = lean_st_ref_get(x_8, x_9);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_st_ref_get(x_1, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_instInhabitedSyntax;
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_get(x_15, x_2, x_16);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_18 = l_Lean_Elab_Term_CollectPatternVars_collect(x_17, x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_14);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; size_t x_32; lean_object* x_33; size_t x_34; lean_object* x_35; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_st_ref_get(x_8, x_20);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_st_ref_get(x_1, x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__27;
x_27 = lean_array_push(x_26, x_19);
x_28 = lean_array_get_size(x_2);
x_29 = lean_unsigned_to_nat(1u);
x_30 = l_Array_toSubarray___rarg(x_2, x_29, x_28);
x_31 = lean_ctor_get(x_30, 2);
lean_inc(x_31);
x_32 = lean_usize_of_nat(x_31);
lean_dec(x_31);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
x_34 = lean_usize_of_nat(x_33);
lean_dec(x_33);
lean_inc(x_8);
lean_inc(x_1);
lean_inc(x_24);
x_35 = l_Subarray_forInUnsafe_loop___at_Lean_Elab_Term_CollectPatternVars_collect___spec__1(x_13, x_24, x_30, x_32, x_34, x_27, x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_25);
lean_dec(x_30);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_st_ref_get(x_8, x_37);
lean_dec(x_8);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_st_ref_set(x_1, x_24, x_39);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_40, 0);
lean_dec(x_42);
x_43 = lean_box(2);
x_44 = l_Lean_choiceKind;
x_45 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set(x_45, 2, x_36);
lean_ctor_set(x_40, 0, x_45);
return x_40;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_ctor_get(x_40, 1);
lean_inc(x_46);
lean_dec(x_40);
x_47 = lean_box(2);
x_48 = l_Lean_choiceKind;
x_49 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
lean_ctor_set(x_49, 2, x_36);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_46);
return x_50;
}
}
else
{
uint8_t x_51; 
lean_dec(x_24);
lean_dec(x_8);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_35);
if (x_51 == 0)
{
return x_35;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_35, 0);
x_53 = lean_ctor_get(x_35, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_35);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_18);
if (x_55 == 0)
{
return x_18;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_18, 0);
x_57 = lean_ctor_get(x_18, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_18);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("{", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(",", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("}", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(6u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___lambda__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_CollectPatternVars_State_vars___default___closed__1;
x_2 = l_Array_append___rarg(x_1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___lambda__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__23;
x_3 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__2___closed__5;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___lambda__2___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(":", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___lambda__2___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("with", 4);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_17 = l_Lean_Syntax_SepArray_getElems___rarg(x_1);
x_18 = lean_array_get_size(x_17);
x_19 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_20 = 0;
lean_inc(x_15);
lean_inc(x_14);
x_21 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_collect___spec__2(x_2, x_19, x_20, x_17, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___spec__2___rarg(x_14, x_15, x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_st_ref_get(x_15, x_26);
lean_dec(x_15);
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
x_30 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__2___closed__1;
lean_inc(x_25);
x_31 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_31, 0, x_25);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__2___closed__2;
x_33 = l_Lean_Syntax_SepArray_ofElems(x_32, x_22);
lean_dec(x_22);
x_34 = l_Lean_Elab_Term_CollectPatternVars_State_vars___default___closed__1;
x_35 = l_Array_append___rarg(x_34, x_33);
x_36 = lean_box(2);
x_37 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__23;
x_38 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set(x_38, 2, x_35);
x_39 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__2___closed__3;
lean_inc(x_25);
x_40 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_40, 0, x_25);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__2___closed__4;
x_42 = lean_array_push(x_41, x_31);
if (lean_obj_tag(x_7) == 0)
{
x_43 = x_34;
goto block_84;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_85 = lean_ctor_get(x_7, 0);
lean_inc(x_85);
lean_dec(x_7);
x_86 = l_Array_append___rarg(x_34, x_85);
x_87 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_87, 0, x_36);
lean_ctor_set(x_87, 1, x_37);
lean_ctor_set(x_87, 2, x_86);
x_88 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__2___closed__8;
lean_inc(x_25);
x_89 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_89, 0, x_25);
lean_ctor_set(x_89, 1, x_88);
x_90 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__12;
x_91 = lean_array_push(x_90, x_87);
x_92 = lean_array_push(x_91, x_89);
x_43 = x_92;
goto block_84;
}
block_84:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_44 = l_Array_append___rarg(x_34, x_43);
x_45 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_45, 0, x_36);
lean_ctor_set(x_45, 1, x_37);
lean_ctor_set(x_45, 2, x_44);
x_46 = lean_array_push(x_42, x_45);
x_47 = lean_array_push(x_46, x_38);
if (lean_obj_tag(x_6) == 0)
{
x_48 = x_34;
goto block_72;
}
else
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_6, 0);
x_74 = l_Lean_Syntax_getHeadInfo_x3f(x_73);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_75 = l_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___lambda__2___closed__2;
lean_inc(x_25);
x_76 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_76, 0, x_25);
lean_ctor_set(x_76, 1, x_75);
x_77 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__27;
x_78 = lean_array_push(x_77, x_76);
x_48 = x_78;
goto block_72;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_79 = lean_ctor_get(x_74, 0);
lean_inc(x_79);
lean_dec(x_74);
x_80 = l_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___lambda__2___closed__2;
x_81 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
x_82 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__27;
x_83 = lean_array_push(x_82, x_81);
x_48 = x_83;
goto block_72;
}
}
block_72:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_49 = l_Array_append___rarg(x_34, x_48);
x_50 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_50, 0, x_36);
lean_ctor_set(x_50, 1, x_37);
lean_ctor_set(x_50, 2, x_49);
x_51 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__27;
x_52 = lean_array_push(x_51, x_50);
x_53 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_53, 0, x_36);
lean_ctor_set(x_53, 1, x_3);
lean_ctor_set(x_53, 2, x_52);
x_54 = lean_array_push(x_47, x_53);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_25);
x_55 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__2___closed__6;
x_56 = lean_array_push(x_54, x_55);
x_57 = lean_array_push(x_56, x_40);
x_58 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_58, 0, x_36);
lean_ctor_set(x_58, 1, x_5);
lean_ctor_set(x_58, 2, x_57);
if (lean_is_scalar(x_29)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_29;
}
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_28);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_60 = lean_ctor_get(x_4, 0);
lean_inc(x_60);
lean_dec(x_4);
x_61 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__2___closed__7;
x_62 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_62, 0, x_25);
lean_ctor_set(x_62, 1, x_61);
x_63 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__12;
x_64 = lean_array_push(x_63, x_62);
x_65 = lean_array_push(x_64, x_60);
x_66 = l_Array_append___rarg(x_34, x_65);
x_67 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_67, 0, x_36);
lean_ctor_set(x_67, 1, x_37);
lean_ctor_set(x_67, 2, x_66);
x_68 = lean_array_push(x_54, x_67);
x_69 = lean_array_push(x_68, x_40);
x_70 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_70, 0, x_36);
lean_ctor_set(x_70, 1, x_5);
lean_ctor_set(x_70, 2, x_69);
if (lean_is_scalar(x_29)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_29;
}
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_28);
return x_71;
}
}
}
}
else
{
uint8_t x_93; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_93 = !lean_is_exclusive(x_21);
if (x_93 == 0)
{
return x_21;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_21, 0);
x_95 = lean_ctor_get(x_21, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_21);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("invalid struct instance pattern, 'with' is not allowed in patterns", 66);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
lean_dec(x_7);
x_17 = l_Lean_Syntax_getArgs(x_1);
lean_dec(x_1);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_box(0);
x_19 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__2(x_17, x_2, x_3, x_8, x_4, x_5, x_6, x_18, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_5);
lean_dec(x_17);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_20 = lean_ctor_get(x_6, 0);
lean_inc(x_20);
lean_dec(x_6);
x_21 = l_Lean_Syntax_SepArray_getElems___rarg(x_20);
lean_dec(x_20);
x_22 = lean_box(2);
x_23 = l_Lean_nullKind;
x_24 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_24, 2, x_21);
x_25 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__3___closed__2;
x_26 = l_Lean_throwErrorAt___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar___spec__2(x_24, x_25, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
lean_dec(x_7);
x_17 = lean_unsigned_to_nat(4u);
x_18 = l_Lean_Syntax_getArg(x_1, x_17);
lean_dec(x_1);
x_19 = l_Lean_Syntax_isNone(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = l_Lean_nullKind;
x_21 = lean_unsigned_to_nat(2u);
lean_inc(x_18);
x_22 = l_Lean_Syntax_isNodeOf(x_18, x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_23 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___rarg(x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_unsigned_to_nat(1u);
x_25 = l_Lean_Syntax_getArg(x_18, x_24);
lean_dec(x_18);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_box(0);
x_28 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__3(x_2, x_3, x_4, x_5, x_8, x_6, x_27, x_26, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_18);
x_29 = lean_box(0);
x_30 = lean_box(0);
x_31 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__3(x_2, x_3, x_4, x_5, x_8, x_6, x_30, x_29, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_31;
}
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___lambda__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("optEllipsis", 11);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_dec(x_4);
x_14 = lean_unsigned_to_nat(2u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
x_16 = lean_unsigned_to_nat(3u);
x_17 = l_Lean_Syntax_getArg(x_1, x_16);
x_18 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__5___closed__1;
lean_inc(x_2);
x_19 = lean_name_mk_string(x_2, x_18);
lean_inc(x_17);
x_20 = l_Lean_Syntax_isOfKind(x_17, x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_21 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___rarg(x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Lean_Syntax_getArg(x_17, x_22);
lean_dec(x_17);
x_24 = l_Lean_Syntax_isNone(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = l_Lean_nullKind;
x_26 = lean_unsigned_to_nat(1u);
lean_inc(x_23);
x_27 = l_Lean_Syntax_isNodeOf(x_23, x_25, x_26);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_23);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_28 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___rarg(x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = l_Lean_Syntax_getArg(x_23, x_22);
lean_dec(x_23);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_box(0);
x_32 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__4(x_1, x_15, x_2, x_19, x_3, x_5, x_31, x_30, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_23);
x_33 = lean_box(0);
x_34 = lean_box(0);
x_35 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__4(x_1, x_15, x_2, x_19, x_3, x_5, x_34, x_33, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_11 = l_Lean_Elab_Term_CollectPatternVars_collect(x_1, x_2, x_3, x_4, x_5, x_6, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_unsigned_to_nat(3u);
x_15 = l_Lean_Syntax_getArg(x_7, x_14);
x_16 = l_Lean_Elab_Term_CollectPatternVars_collect(x_15, x_2, x_3, x_4, x_5, x_6, x_8, x_9, x_13);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_unsigned_to_nat(2u);
x_20 = l_Lean_Syntax_setArg(x_7, x_19, x_12);
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
x_25 = l_Lean_Syntax_setArg(x_7, x_24, x_12);
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
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___lambda__8___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_root_.namedPattern", 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___lambda__8___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__8___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___lambda__8___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__8___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__8___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___lambda__8___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_root_", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___lambda__8___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__8___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___lambda__8___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("namedPattern", 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___lambda__8___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__8___closed__5;
x_2 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__8___closed__6;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___lambda__8___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__8___closed__6;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___lambda__8___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__8___closed__8;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___lambda__8___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__8___closed__9;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
lean_inc(x_4);
x_18 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
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
x_23 = lean_ctor_get(x_10, 10);
lean_inc(x_23);
lean_dec(x_10);
x_24 = lean_st_ref_get(x_11, x_22);
lean_dec(x_11);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_environment_main_module(x_27);
x_29 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__8___closed__7;
x_30 = l_Lean_addMacroScope(x_28, x_29, x_23);
x_31 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__8___closed__3;
x_32 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__8___closed__10;
x_33 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_33, 0, x_21);
lean_ctor_set(x_33, 1, x_31);
lean_ctor_set(x_33, 2, x_30);
lean_ctor_set(x_33, 3, x_32);
x_34 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__28;
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
lean_ctor_set(x_24, 0, x_44);
return x_24;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_45 = lean_ctor_get(x_24, 0);
x_46 = lean_ctor_get(x_24, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_24);
x_47 = lean_ctor_get(x_45, 0);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_environment_main_module(x_47);
x_49 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__8___closed__7;
x_50 = l_Lean_addMacroScope(x_48, x_49, x_23);
x_51 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__8___closed__3;
x_52 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__8___closed__10;
x_53 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_53, 0, x_21);
lean_ctor_set(x_53, 1, x_51);
lean_ctor_set(x_53, 2, x_50);
lean_ctor_set(x_53, 3, x_52);
x_54 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__28;
x_55 = lean_array_push(x_54, x_2);
x_56 = lean_array_push(x_55, x_16);
x_57 = lean_array_push(x_56, x_4);
x_58 = lean_box(2);
x_59 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__23;
x_60 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
lean_ctor_set(x_60, 2, x_57);
x_61 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__12;
x_62 = lean_array_push(x_61, x_53);
x_63 = lean_array_push(x_62, x_60);
x_64 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_64, 0, x_58);
lean_ctor_set(x_64, 1, x_3);
lean_ctor_set(x_64, 2, x_63);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_46);
return x_65;
}
}
else
{
uint8_t x_66; 
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_66 = !lean_is_exclusive(x_18);
if (x_66 == 0)
{
return x_18;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_18, 0);
x_68 = lean_ctor_get(x_18, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_18);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
else
{
uint8_t x_70; 
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
x_70 = !lean_is_exclusive(x_15);
if (x_70 == 0)
{
return x_15;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_15, 0);
x_72 = lean_ctor_get(x_15, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_15);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___lambda__9___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("h", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___lambda__9___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__9___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___lambda__9___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__9___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__9___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___lambda__9___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__9___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_12 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_processVar(x_1, x_2, x_3, x_4, x_5, x_6, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_unsigned_to_nat(2u);
x_15 = l_Lean_Syntax_getArg(x_7, x_14);
x_16 = l_Lean_Syntax_isNone(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_Lean_Syntax_getArg(x_15, x_17);
lean_dec(x_15);
x_19 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__8(x_7, x_1, x_8, x_18, x_2, x_3, x_4, x_5, x_6, x_9, x_10, x_13);
lean_dec(x_7);
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
x_23 = lean_ctor_get(x_9, 10);
lean_inc(x_23);
x_24 = lean_st_ref_get(x_10, x_22);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_environment_main_module(x_27);
x_29 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__9___closed__4;
x_30 = l_Lean_addMacroScope(x_28, x_29, x_23);
x_31 = lean_box(0);
x_32 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__9___closed__3;
x_33 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_33, 0, x_21);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_33, 2, x_30);
lean_ctor_set(x_33, 3, x_31);
x_34 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__8(x_7, x_1, x_8, x_33, x_2, x_3, x_4, x_5, x_6, x_9, x_10, x_26);
lean_dec(x_7);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Term_CollectPatternVars_collect(x_1, x_2, x_3, x_4, x_5, x_6, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Lean_Syntax_setArg(x_7, x_15, x_14);
x_17 = lean_unsigned_to_nat(1u);
x_18 = l_Lean_Syntax_setArg(x_8, x_17, x_16);
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
x_22 = l_Lean_Syntax_setArg(x_7, x_21, x_19);
x_23 = lean_unsigned_to_nat(1u);
x_24 = l_Lean_Syntax_setArg(x_8, x_23, x_22);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_20);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_8);
lean_dec(x_7);
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
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___lambda__11___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("inaccessible", 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___lambda__11___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(".(", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___lambda__11___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(")", 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___spec__2___rarg(x_3, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_st_ref_get(x_4, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_11 = lean_ctor_get(x_9, 0);
lean_dec(x_11);
x_12 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__11___closed__1;
x_13 = lean_name_mk_string(x_1, x_12);
x_14 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__11___closed__2;
lean_inc(x_7);
x_15 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__11___closed__3;
x_17 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_17, 0, x_7);
lean_ctor_set(x_17, 1, x_16);
x_18 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__28;
x_19 = lean_array_push(x_18, x_15);
x_20 = lean_array_push(x_19, x_2);
x_21 = lean_array_push(x_20, x_17);
x_22 = lean_box(2);
x_23 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_13);
lean_ctor_set(x_23, 2, x_21);
lean_ctor_set(x_9, 0, x_23);
return x_9;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_24 = lean_ctor_get(x_9, 1);
lean_inc(x_24);
lean_dec(x_9);
x_25 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__11___closed__1;
x_26 = lean_name_mk_string(x_1, x_25);
x_27 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__11___closed__2;
lean_inc(x_7);
x_28 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_28, 0, x_7);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__11___closed__3;
x_30 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_30, 0, x_7);
lean_ctor_set(x_30, 1, x_29);
x_31 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__28;
x_32 = lean_array_push(x_31, x_28);
x_33 = lean_array_push(x_32, x_2);
x_34 = lean_array_push(x_33, x_30);
x_35 = lean_box(2);
x_36 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_26);
lean_ctor_set(x_36, 2, x_34);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_24);
return x_37;
}
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___lambda__12___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__12___closed__1;
x_12 = l_Array_mapSepElemsM___at_Lean_Elab_Term_CollectPatternVars_collect___spec__5(x_1, x_11, x_2, x_3, x_4, x_5, x_6, x_8, x_9, x_10);
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
x_19 = l_Lean_Syntax_setArg(x_7, x_18, x_17);
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
x_26 = l_Lean_Syntax_setArg(x_7, x_25, x_24);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_21);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_7);
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
x_1 = lean_mk_string_from_bytes("anonymousCtor", 13);
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
x_1 = lean_mk_string_from_bytes("syntheticHole", 13);
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
x_1 = lean_mk_string_from_bytes("paren", 5);
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
x_1 = lean_mk_string_from_bytes("explicitUniv", 12);
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__8;
x_2 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__8___closed__6;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("binop", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__8;
x_2 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__10;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__8;
x_2 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__11___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("quotedName", 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__8;
x_2 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__13;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("doubleQuotedName", 16);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__8;
x_2 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__15;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__8;
x_2 = l_Array_anyMUnsafe_any___at_Lean_Elab_Term_CollectPatternVars_collect___spec__3___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_CollectPatternVars_collect___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("typeAscription", 14);
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
x_14 = lean_ctor_get(x_7, 5);
x_15 = l_Lean_replaceRef(x_1, x_14);
lean_dec(x_14);
lean_ctor_set(x_7, 5, x_15);
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
x_20 = l_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___closed__2;
x_21 = lean_name_eq(x_10, x_20);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__25;
x_23 = lean_name_eq(x_10, x_22);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__4;
x_25 = lean_name_eq(x_10, x_24);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__6;
x_27 = lean_name_eq(x_10, x_26);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__8;
x_29 = lean_name_eq(x_10, x_28);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__9;
x_31 = lean_name_eq(x_10, x_30);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__11;
x_33 = lean_name_eq(x_10, x_32);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__12;
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
x_44 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__14;
x_45 = lean_name_eq(x_10, x_44);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__16;
x_47 = lean_name_eq(x_10, x_46);
if (x_47 == 0)
{
lean_object* x_48; uint8_t x_49; 
x_48 = l_Lean_choiceKind;
x_49 = lean_name_eq(x_10, x_48);
lean_dec(x_10);
if (x_49 == 0)
{
lean_object* x_50; uint8_t x_51; 
x_50 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__17;
lean_inc(x_1);
x_51 = l_Lean_Syntax_isOfKind(x_1, x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_1);
x_52 = lean_alloc_closure((void*)(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___rarg), 8, 5);
lean_closure_set(x_52, 0, x_2);
lean_closure_set(x_52, 1, x_3);
lean_closure_set(x_52, 2, x_4);
lean_closure_set(x_52, 3, x_5);
lean_closure_set(x_52, 4, x_6);
x_53 = l_Lean_Core_withFreshMacroScope___rarg(x_52, x_7, x_8, x_9);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_54 = lean_unsigned_to_nat(1u);
x_55 = l_Lean_Syntax_getArg(x_1, x_54);
x_56 = l_Lean_Syntax_isNone(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_57 = l_Lean_nullKind;
x_58 = lean_unsigned_to_nat(2u);
lean_inc(x_55);
x_59 = l_Lean_Syntax_isNodeOf(x_55, x_57, x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
lean_dec(x_55);
lean_dec(x_1);
x_60 = lean_alloc_closure((void*)(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___rarg), 8, 5);
lean_closure_set(x_60, 0, x_2);
lean_closure_set(x_60, 1, x_3);
lean_closure_set(x_60, 2, x_4);
lean_closure_set(x_60, 3, x_5);
lean_closure_set(x_60, 4, x_6);
x_61 = l_Lean_Core_withFreshMacroScope___rarg(x_60, x_7, x_8, x_9);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_62 = lean_unsigned_to_nat(0u);
x_63 = l_Lean_Syntax_getArg(x_55, x_62);
lean_dec(x_55);
x_64 = l_Lean_Syntax_getArgs(x_63);
lean_dec(x_63);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_66 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__8;
x_67 = lean_box(0);
x_68 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__5), 13, 10);
lean_closure_set(x_68, 0, x_1);
lean_closure_set(x_68, 1, x_66);
lean_closure_set(x_68, 2, x_50);
lean_closure_set(x_68, 3, x_67);
lean_closure_set(x_68, 4, x_65);
lean_closure_set(x_68, 5, x_2);
lean_closure_set(x_68, 6, x_3);
lean_closure_set(x_68, 7, x_4);
lean_closure_set(x_68, 8, x_5);
lean_closure_set(x_68, 9, x_6);
x_69 = l_Lean_Core_withFreshMacroScope___rarg(x_68, x_7, x_8, x_9);
return x_69;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_55);
x_70 = lean_box(0);
x_71 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__8;
x_72 = lean_box(0);
x_73 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__5), 13, 10);
lean_closure_set(x_73, 0, x_1);
lean_closure_set(x_73, 1, x_71);
lean_closure_set(x_73, 2, x_50);
lean_closure_set(x_73, 3, x_72);
lean_closure_set(x_73, 4, x_70);
lean_closure_set(x_73, 5, x_2);
lean_closure_set(x_73, 6, x_3);
lean_closure_set(x_73, 7, x_4);
lean_closure_set(x_73, 8, x_5);
lean_closure_set(x_73, 9, x_6);
x_74 = l_Lean_Core_withFreshMacroScope___rarg(x_73, x_7, x_8, x_9);
return x_74;
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_75 = l_Lean_Syntax_getArgs(x_1);
lean_dec(x_1);
x_76 = lean_array_get_size(x_75);
x_77 = lean_unsigned_to_nat(0u);
x_78 = lean_nat_dec_lt(x_77, x_76);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; 
lean_dec(x_76);
x_79 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__1), 9, 6);
lean_closure_set(x_79, 0, x_2);
lean_closure_set(x_79, 1, x_75);
lean_closure_set(x_79, 2, x_3);
lean_closure_set(x_79, 3, x_4);
lean_closure_set(x_79, 4, x_5);
lean_closure_set(x_79, 5, x_6);
x_80 = l_Lean_Core_withFreshMacroScope___rarg(x_79, x_7, x_8, x_9);
return x_80;
}
else
{
uint8_t x_81; 
x_81 = lean_nat_dec_le(x_76, x_76);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; 
lean_dec(x_76);
x_82 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__1), 9, 6);
lean_closure_set(x_82, 0, x_2);
lean_closure_set(x_82, 1, x_75);
lean_closure_set(x_82, 2, x_3);
lean_closure_set(x_82, 3, x_4);
lean_closure_set(x_82, 4, x_5);
lean_closure_set(x_82, 5, x_6);
x_83 = l_Lean_Core_withFreshMacroScope___rarg(x_82, x_7, x_8, x_9);
return x_83;
}
else
{
size_t x_84; size_t x_85; lean_object* x_86; uint8_t x_87; 
x_84 = 0;
x_85 = lean_usize_of_nat(x_76);
lean_dec(x_76);
x_86 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__8;
x_87 = l_Array_anyMUnsafe_any___at_Lean_Elab_Term_CollectPatternVars_collect___spec__3(x_86, x_75, x_84, x_85);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__1), 9, 6);
lean_closure_set(x_88, 0, x_2);
lean_closure_set(x_88, 1, x_75);
lean_closure_set(x_88, 2, x_3);
lean_closure_set(x_88, 3, x_4);
lean_closure_set(x_88, 4, x_5);
lean_closure_set(x_88, 5, x_6);
x_89 = l_Lean_Core_withFreshMacroScope___rarg(x_88, x_7, x_8, x_9);
return x_89;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = l_Lean_Elab_Term_CollectPatternVars_State_vars___default___closed__1;
x_91 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_CollectPatternVars_collect___spec__4(x_86, x_75, x_84, x_85, x_90);
lean_dec(x_75);
x_92 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__1), 9, 6);
lean_closure_set(x_92, 0, x_2);
lean_closure_set(x_92, 1, x_91);
lean_closure_set(x_92, 2, x_3);
lean_closure_set(x_92, 3, x_4);
lean_closure_set(x_92, 4, x_5);
lean_closure_set(x_92, 5, x_6);
x_93 = l_Lean_Core_withFreshMacroScope___rarg(x_92, x_7, x_8, x_9);
return x_93;
}
}
}
}
}
else
{
lean_object* x_94; lean_object* x_95; 
lean_dec(x_10);
lean_dec(x_2);
x_94 = lean_alloc_closure((void*)(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___boxed), 8, 5);
lean_closure_set(x_94, 0, x_1);
lean_closure_set(x_94, 1, x_3);
lean_closure_set(x_94, 2, x_4);
lean_closure_set(x_94, 3, x_5);
lean_closure_set(x_94, 4, x_6);
x_95 = l_Lean_Core_withFreshMacroScope___rarg(x_94, x_7, x_8, x_9);
return x_95;
}
}
else
{
lean_object* x_96; lean_object* x_97; 
lean_dec(x_10);
lean_dec(x_2);
x_96 = lean_alloc_closure((void*)(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_quotedNameToPattern), 8, 5);
lean_closure_set(x_96, 0, x_1);
lean_closure_set(x_96, 1, x_3);
lean_closure_set(x_96, 2, x_4);
lean_closure_set(x_96, 3, x_5);
lean_closure_set(x_96, 4, x_6);
x_97 = l_Lean_Core_withFreshMacroScope___rarg(x_96, x_7, x_8, x_9);
return x_97;
}
}
else
{
lean_object* x_98; lean_object* x_99; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_98 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__6___boxed), 4, 1);
lean_closure_set(x_98, 0, x_1);
x_99 = l_Lean_Core_withFreshMacroScope___rarg(x_98, x_7, x_8, x_9);
return x_99;
}
}
else
{
lean_object* x_100; lean_object* x_101; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_100 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__6___boxed), 4, 1);
lean_closure_set(x_100, 0, x_1);
x_101 = l_Lean_Core_withFreshMacroScope___rarg(x_100, x_7, x_8, x_9);
return x_101;
}
}
else
{
lean_object* x_102; lean_object* x_103; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_102 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__6___boxed), 4, 1);
lean_closure_set(x_102, 0, x_1);
x_103 = l_Lean_Core_withFreshMacroScope___rarg(x_102, x_7, x_8, x_9);
return x_103;
}
}
else
{
lean_object* x_104; lean_object* x_105; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_104 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__6___boxed), 4, 1);
lean_closure_set(x_104, 0, x_1);
x_105 = l_Lean_Core_withFreshMacroScope___rarg(x_104, x_7, x_8, x_9);
return x_105;
}
}
else
{
lean_object* x_106; lean_object* x_107; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_106 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__6___boxed), 4, 1);
lean_closure_set(x_106, 0, x_1);
x_107 = l_Lean_Core_withFreshMacroScope___rarg(x_106, x_7, x_8, x_9);
return x_107;
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_10);
x_108 = lean_unsigned_to_nat(2u);
x_109 = l_Lean_Syntax_getArg(x_1, x_108);
x_110 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__7), 10, 7);
lean_closure_set(x_110, 0, x_109);
lean_closure_set(x_110, 1, x_2);
lean_closure_set(x_110, 2, x_3);
lean_closure_set(x_110, 3, x_4);
lean_closure_set(x_110, 4, x_5);
lean_closure_set(x_110, 5, x_6);
lean_closure_set(x_110, 6, x_1);
x_111 = l_Lean_Core_withFreshMacroScope___rarg(x_110, x_7, x_8, x_9);
return x_111;
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_10);
x_112 = lean_unsigned_to_nat(0u);
x_113 = l_Lean_Syntax_getArg(x_1, x_112);
x_114 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__9), 11, 8);
lean_closure_set(x_114, 0, x_113);
lean_closure_set(x_114, 1, x_2);
lean_closure_set(x_114, 2, x_3);
lean_closure_set(x_114, 3, x_4);
lean_closure_set(x_114, 4, x_5);
lean_closure_set(x_114, 5, x_6);
lean_closure_set(x_114, 6, x_1);
lean_closure_set(x_114, 7, x_16);
x_115 = l_Lean_Core_withFreshMacroScope___rarg(x_114, x_7, x_8, x_9);
return x_115;
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_10);
x_116 = lean_unsigned_to_nat(0u);
x_117 = l_Lean_Syntax_getArg(x_1, x_116);
lean_dec(x_1);
x_118 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect_processCtor), 9, 6);
lean_closure_set(x_118, 0, x_117);
lean_closure_set(x_118, 1, x_2);
lean_closure_set(x_118, 2, x_3);
lean_closure_set(x_118, 3, x_4);
lean_closure_set(x_118, 4, x_5);
lean_closure_set(x_118, 5, x_6);
x_119 = l_Lean_Core_withFreshMacroScope___rarg(x_118, x_7, x_8, x_9);
return x_119;
}
}
else
{
lean_object* x_120; lean_object* x_121; uint8_t x_122; 
lean_dec(x_10);
x_120 = lean_unsigned_to_nat(1u);
x_121 = l_Lean_Syntax_getArg(x_1, x_120);
x_122 = l_Lean_Syntax_isNone(x_121);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
x_123 = lean_unsigned_to_nat(0u);
x_124 = l_Lean_Syntax_getArg(x_121, x_123);
x_125 = l_Lean_Syntax_getArg(x_121, x_120);
x_126 = l_Lean_Syntax_isNone(x_125);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; 
x_127 = l_Lean_Syntax_getArg(x_125, x_123);
lean_dec(x_125);
x_128 = l_Lean_Syntax_getKind(x_127);
x_129 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__19;
x_130 = lean_name_eq(x_128, x_129);
lean_dec(x_128);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; 
lean_dec(x_124);
lean_dec(x_121);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_131 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__6___boxed), 4, 1);
lean_closure_set(x_131, 0, x_1);
x_132 = l_Lean_Core_withFreshMacroScope___rarg(x_131, x_7, x_8, x_9);
return x_132;
}
else
{
lean_object* x_133; lean_object* x_134; 
x_133 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__10), 11, 8);
lean_closure_set(x_133, 0, x_124);
lean_closure_set(x_133, 1, x_2);
lean_closure_set(x_133, 2, x_3);
lean_closure_set(x_133, 3, x_4);
lean_closure_set(x_133, 4, x_5);
lean_closure_set(x_133, 5, x_6);
lean_closure_set(x_133, 6, x_121);
lean_closure_set(x_133, 7, x_1);
x_134 = l_Lean_Core_withFreshMacroScope___rarg(x_133, x_7, x_8, x_9);
return x_134;
}
}
else
{
lean_object* x_135; lean_object* x_136; 
lean_dec(x_125);
x_135 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__10), 11, 8);
lean_closure_set(x_135, 0, x_124);
lean_closure_set(x_135, 1, x_2);
lean_closure_set(x_135, 2, x_3);
lean_closure_set(x_135, 3, x_4);
lean_closure_set(x_135, 4, x_5);
lean_closure_set(x_135, 5, x_6);
lean_closure_set(x_135, 6, x_121);
lean_closure_set(x_135, 7, x_1);
x_136 = l_Lean_Core_withFreshMacroScope___rarg(x_135, x_7, x_8, x_9);
return x_136;
}
}
else
{
lean_object* x_137; lean_object* x_138; 
lean_dec(x_121);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_137 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__6___boxed), 4, 1);
lean_closure_set(x_137, 0, x_1);
x_138 = l_Lean_Core_withFreshMacroScope___rarg(x_137, x_7, x_8, x_9);
return x_138;
}
}
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_139 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__8;
x_140 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__11___boxed), 5, 2);
lean_closure_set(x_140, 0, x_139);
lean_closure_set(x_140, 1, x_1);
x_141 = l_Lean_Core_withFreshMacroScope___rarg(x_140, x_7, x_8, x_9);
return x_141;
}
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_142 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__8;
x_143 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__11___boxed), 5, 2);
lean_closure_set(x_143, 0, x_142);
lean_closure_set(x_143, 1, x_1);
x_144 = l_Lean_Core_withFreshMacroScope___rarg(x_143, x_7, x_8, x_9);
return x_144;
}
}
else
{
lean_object* x_145; lean_object* x_146; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_145 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__6___boxed), 4, 1);
lean_closure_set(x_145, 0, x_1);
x_146 = l_Lean_Core_withFreshMacroScope___rarg(x_145, x_7, x_8, x_9);
return x_146;
}
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_dec(x_10);
x_147 = lean_unsigned_to_nat(1u);
x_148 = l_Lean_Syntax_getArg(x_1, x_147);
x_149 = l_Lean_Syntax_getArgs(x_148);
lean_dec(x_148);
x_150 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__12___boxed), 10, 7);
lean_closure_set(x_150, 0, x_149);
lean_closure_set(x_150, 1, x_2);
lean_closure_set(x_150, 2, x_3);
lean_closure_set(x_150, 3, x_4);
lean_closure_set(x_150, 4, x_5);
lean_closure_set(x_150, 5, x_6);
lean_closure_set(x_150, 6, x_1);
x_151 = l_Lean_Core_withFreshMacroScope___rarg(x_150, x_7, x_8, x_9);
return x_151;
}
}
else
{
lean_object* x_152; lean_object* x_153; 
lean_dec(x_10);
x_152 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp), 9, 6);
lean_closure_set(x_152, 0, x_1);
lean_closure_set(x_152, 1, x_2);
lean_closure_set(x_152, 2, x_3);
lean_closure_set(x_152, 3, x_4);
lean_closure_set(x_152, 4, x_5);
lean_closure_set(x_152, 5, x_6);
x_153 = l_Lean_Core_withFreshMacroScope___rarg(x_152, x_7, x_8, x_9);
return x_153;
}
}
else
{
lean_object* x_154; lean_object* x_155; 
lean_dec(x_10);
x_154 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect_processId), 9, 6);
lean_closure_set(x_154, 0, x_1);
lean_closure_set(x_154, 1, x_2);
lean_closure_set(x_154, 2, x_3);
lean_closure_set(x_154, 3, x_4);
lean_closure_set(x_154, 4, x_5);
lean_closure_set(x_154, 5, x_6);
x_155 = l_Lean_Core_withFreshMacroScope___rarg(x_154, x_7, x_8, x_9);
return x_155;
}
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_156 = lean_ctor_get(x_7, 0);
x_157 = lean_ctor_get(x_7, 1);
x_158 = lean_ctor_get(x_7, 2);
x_159 = lean_ctor_get(x_7, 3);
x_160 = lean_ctor_get(x_7, 4);
x_161 = lean_ctor_get(x_7, 5);
x_162 = lean_ctor_get(x_7, 6);
x_163 = lean_ctor_get(x_7, 7);
x_164 = lean_ctor_get(x_7, 8);
x_165 = lean_ctor_get(x_7, 9);
x_166 = lean_ctor_get(x_7, 10);
lean_inc(x_166);
lean_inc(x_165);
lean_inc(x_164);
lean_inc(x_163);
lean_inc(x_162);
lean_inc(x_161);
lean_inc(x_160);
lean_inc(x_159);
lean_inc(x_158);
lean_inc(x_157);
lean_inc(x_156);
lean_dec(x_7);
x_167 = l_Lean_replaceRef(x_1, x_161);
lean_dec(x_161);
x_168 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_168, 0, x_156);
lean_ctor_set(x_168, 1, x_157);
lean_ctor_set(x_168, 2, x_158);
lean_ctor_set(x_168, 3, x_159);
lean_ctor_set(x_168, 4, x_160);
lean_ctor_set(x_168, 5, x_167);
lean_ctor_set(x_168, 6, x_162);
lean_ctor_set(x_168, 7, x_163);
lean_ctor_set(x_168, 8, x_164);
lean_ctor_set(x_168, 9, x_165);
lean_ctor_set(x_168, 10, x_166);
if (x_12 == 0)
{
lean_object* x_169; uint8_t x_170; 
x_169 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__13;
x_170 = lean_name_eq(x_10, x_169);
if (x_170 == 0)
{
lean_object* x_171; uint8_t x_172; 
x_171 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__2;
x_172 = lean_name_eq(x_10, x_171);
if (x_172 == 0)
{
lean_object* x_173; uint8_t x_174; 
x_173 = l_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___closed__2;
x_174 = lean_name_eq(x_10, x_173);
if (x_174 == 0)
{
lean_object* x_175; uint8_t x_176; 
x_175 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__25;
x_176 = lean_name_eq(x_10, x_175);
if (x_176 == 0)
{
lean_object* x_177; uint8_t x_178; 
x_177 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__4;
x_178 = lean_name_eq(x_10, x_177);
if (x_178 == 0)
{
lean_object* x_179; uint8_t x_180; 
x_179 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__6;
x_180 = lean_name_eq(x_10, x_179);
if (x_180 == 0)
{
lean_object* x_181; uint8_t x_182; 
x_181 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__8;
x_182 = lean_name_eq(x_10, x_181);
if (x_182 == 0)
{
lean_object* x_183; uint8_t x_184; 
x_183 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__9;
x_184 = lean_name_eq(x_10, x_183);
if (x_184 == 0)
{
lean_object* x_185; uint8_t x_186; 
x_185 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__11;
x_186 = lean_name_eq(x_10, x_185);
if (x_186 == 0)
{
lean_object* x_187; uint8_t x_188; 
x_187 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__12;
x_188 = lean_name_eq(x_10, x_187);
if (x_188 == 0)
{
lean_object* x_189; uint8_t x_190; 
x_189 = l_Lean_strLitKind;
x_190 = lean_name_eq(x_10, x_189);
if (x_190 == 0)
{
lean_object* x_191; uint8_t x_192; 
x_191 = l_Lean_numLitKind;
x_192 = lean_name_eq(x_10, x_191);
if (x_192 == 0)
{
lean_object* x_193; uint8_t x_194; 
x_193 = l_Lean_scientificLitKind;
x_194 = lean_name_eq(x_10, x_193);
if (x_194 == 0)
{
lean_object* x_195; uint8_t x_196; 
x_195 = l_Lean_charLitKind;
x_196 = lean_name_eq(x_10, x_195);
if (x_196 == 0)
{
lean_object* x_197; uint8_t x_198; 
x_197 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__14;
x_198 = lean_name_eq(x_10, x_197);
if (x_198 == 0)
{
lean_object* x_199; uint8_t x_200; 
x_199 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__16;
x_200 = lean_name_eq(x_10, x_199);
if (x_200 == 0)
{
lean_object* x_201; uint8_t x_202; 
x_201 = l_Lean_choiceKind;
x_202 = lean_name_eq(x_10, x_201);
lean_dec(x_10);
if (x_202 == 0)
{
lean_object* x_203; uint8_t x_204; 
x_203 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__17;
lean_inc(x_1);
x_204 = l_Lean_Syntax_isOfKind(x_1, x_203);
if (x_204 == 0)
{
lean_object* x_205; lean_object* x_206; 
lean_dec(x_1);
x_205 = lean_alloc_closure((void*)(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___rarg), 8, 5);
lean_closure_set(x_205, 0, x_2);
lean_closure_set(x_205, 1, x_3);
lean_closure_set(x_205, 2, x_4);
lean_closure_set(x_205, 3, x_5);
lean_closure_set(x_205, 4, x_6);
x_206 = l_Lean_Core_withFreshMacroScope___rarg(x_205, x_168, x_8, x_9);
return x_206;
}
else
{
lean_object* x_207; lean_object* x_208; uint8_t x_209; 
x_207 = lean_unsigned_to_nat(1u);
x_208 = l_Lean_Syntax_getArg(x_1, x_207);
x_209 = l_Lean_Syntax_isNone(x_208);
if (x_209 == 0)
{
lean_object* x_210; lean_object* x_211; uint8_t x_212; 
x_210 = l_Lean_nullKind;
x_211 = lean_unsigned_to_nat(2u);
lean_inc(x_208);
x_212 = l_Lean_Syntax_isNodeOf(x_208, x_210, x_211);
if (x_212 == 0)
{
lean_object* x_213; lean_object* x_214; 
lean_dec(x_208);
lean_dec(x_1);
x_213 = lean_alloc_closure((void*)(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_throwInvalidPattern___rarg), 8, 5);
lean_closure_set(x_213, 0, x_2);
lean_closure_set(x_213, 1, x_3);
lean_closure_set(x_213, 2, x_4);
lean_closure_set(x_213, 3, x_5);
lean_closure_set(x_213, 4, x_6);
x_214 = l_Lean_Core_withFreshMacroScope___rarg(x_213, x_168, x_8, x_9);
return x_214;
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_215 = lean_unsigned_to_nat(0u);
x_216 = l_Lean_Syntax_getArg(x_208, x_215);
lean_dec(x_208);
x_217 = l_Lean_Syntax_getArgs(x_216);
lean_dec(x_216);
x_218 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_218, 0, x_217);
x_219 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__8;
x_220 = lean_box(0);
x_221 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__5), 13, 10);
lean_closure_set(x_221, 0, x_1);
lean_closure_set(x_221, 1, x_219);
lean_closure_set(x_221, 2, x_203);
lean_closure_set(x_221, 3, x_220);
lean_closure_set(x_221, 4, x_218);
lean_closure_set(x_221, 5, x_2);
lean_closure_set(x_221, 6, x_3);
lean_closure_set(x_221, 7, x_4);
lean_closure_set(x_221, 8, x_5);
lean_closure_set(x_221, 9, x_6);
x_222 = l_Lean_Core_withFreshMacroScope___rarg(x_221, x_168, x_8, x_9);
return x_222;
}
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
lean_dec(x_208);
x_223 = lean_box(0);
x_224 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__8;
x_225 = lean_box(0);
x_226 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__5), 13, 10);
lean_closure_set(x_226, 0, x_1);
lean_closure_set(x_226, 1, x_224);
lean_closure_set(x_226, 2, x_203);
lean_closure_set(x_226, 3, x_225);
lean_closure_set(x_226, 4, x_223);
lean_closure_set(x_226, 5, x_2);
lean_closure_set(x_226, 6, x_3);
lean_closure_set(x_226, 7, x_4);
lean_closure_set(x_226, 8, x_5);
lean_closure_set(x_226, 9, x_6);
x_227 = l_Lean_Core_withFreshMacroScope___rarg(x_226, x_168, x_8, x_9);
return x_227;
}
}
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; uint8_t x_231; 
x_228 = l_Lean_Syntax_getArgs(x_1);
lean_dec(x_1);
x_229 = lean_array_get_size(x_228);
x_230 = lean_unsigned_to_nat(0u);
x_231 = lean_nat_dec_lt(x_230, x_229);
if (x_231 == 0)
{
lean_object* x_232; lean_object* x_233; 
lean_dec(x_229);
x_232 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__1), 9, 6);
lean_closure_set(x_232, 0, x_2);
lean_closure_set(x_232, 1, x_228);
lean_closure_set(x_232, 2, x_3);
lean_closure_set(x_232, 3, x_4);
lean_closure_set(x_232, 4, x_5);
lean_closure_set(x_232, 5, x_6);
x_233 = l_Lean_Core_withFreshMacroScope___rarg(x_232, x_168, x_8, x_9);
return x_233;
}
else
{
uint8_t x_234; 
x_234 = lean_nat_dec_le(x_229, x_229);
if (x_234 == 0)
{
lean_object* x_235; lean_object* x_236; 
lean_dec(x_229);
x_235 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__1), 9, 6);
lean_closure_set(x_235, 0, x_2);
lean_closure_set(x_235, 1, x_228);
lean_closure_set(x_235, 2, x_3);
lean_closure_set(x_235, 3, x_4);
lean_closure_set(x_235, 4, x_5);
lean_closure_set(x_235, 5, x_6);
x_236 = l_Lean_Core_withFreshMacroScope___rarg(x_235, x_168, x_8, x_9);
return x_236;
}
else
{
size_t x_237; size_t x_238; lean_object* x_239; uint8_t x_240; 
x_237 = 0;
x_238 = lean_usize_of_nat(x_229);
lean_dec(x_229);
x_239 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__8;
x_240 = l_Array_anyMUnsafe_any___at_Lean_Elab_Term_CollectPatternVars_collect___spec__3(x_239, x_228, x_237, x_238);
if (x_240 == 0)
{
lean_object* x_241; lean_object* x_242; 
x_241 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__1), 9, 6);
lean_closure_set(x_241, 0, x_2);
lean_closure_set(x_241, 1, x_228);
lean_closure_set(x_241, 2, x_3);
lean_closure_set(x_241, 3, x_4);
lean_closure_set(x_241, 4, x_5);
lean_closure_set(x_241, 5, x_6);
x_242 = l_Lean_Core_withFreshMacroScope___rarg(x_241, x_168, x_8, x_9);
return x_242;
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_243 = l_Lean_Elab_Term_CollectPatternVars_State_vars___default___closed__1;
x_244 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_CollectPatternVars_collect___spec__4(x_239, x_228, x_237, x_238, x_243);
lean_dec(x_228);
x_245 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__1), 9, 6);
lean_closure_set(x_245, 0, x_2);
lean_closure_set(x_245, 1, x_244);
lean_closure_set(x_245, 2, x_3);
lean_closure_set(x_245, 3, x_4);
lean_closure_set(x_245, 4, x_5);
lean_closure_set(x_245, 5, x_6);
x_246 = l_Lean_Core_withFreshMacroScope___rarg(x_245, x_168, x_8, x_9);
return x_246;
}
}
}
}
}
else
{
lean_object* x_247; lean_object* x_248; 
lean_dec(x_10);
lean_dec(x_2);
x_247 = lean_alloc_closure((void*)(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___boxed), 8, 5);
lean_closure_set(x_247, 0, x_1);
lean_closure_set(x_247, 1, x_3);
lean_closure_set(x_247, 2, x_4);
lean_closure_set(x_247, 3, x_5);
lean_closure_set(x_247, 4, x_6);
x_248 = l_Lean_Core_withFreshMacroScope___rarg(x_247, x_168, x_8, x_9);
return x_248;
}
}
else
{
lean_object* x_249; lean_object* x_250; 
lean_dec(x_10);
lean_dec(x_2);
x_249 = lean_alloc_closure((void*)(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_quotedNameToPattern), 8, 5);
lean_closure_set(x_249, 0, x_1);
lean_closure_set(x_249, 1, x_3);
lean_closure_set(x_249, 2, x_4);
lean_closure_set(x_249, 3, x_5);
lean_closure_set(x_249, 4, x_6);
x_250 = l_Lean_Core_withFreshMacroScope___rarg(x_249, x_168, x_8, x_9);
return x_250;
}
}
else
{
lean_object* x_251; lean_object* x_252; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_251 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__6___boxed), 4, 1);
lean_closure_set(x_251, 0, x_1);
x_252 = l_Lean_Core_withFreshMacroScope___rarg(x_251, x_168, x_8, x_9);
return x_252;
}
}
else
{
lean_object* x_253; lean_object* x_254; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_253 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__6___boxed), 4, 1);
lean_closure_set(x_253, 0, x_1);
x_254 = l_Lean_Core_withFreshMacroScope___rarg(x_253, x_168, x_8, x_9);
return x_254;
}
}
else
{
lean_object* x_255; lean_object* x_256; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_255 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__6___boxed), 4, 1);
lean_closure_set(x_255, 0, x_1);
x_256 = l_Lean_Core_withFreshMacroScope___rarg(x_255, x_168, x_8, x_9);
return x_256;
}
}
else
{
lean_object* x_257; lean_object* x_258; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_257 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__6___boxed), 4, 1);
lean_closure_set(x_257, 0, x_1);
x_258 = l_Lean_Core_withFreshMacroScope___rarg(x_257, x_168, x_8, x_9);
return x_258;
}
}
else
{
lean_object* x_259; lean_object* x_260; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_259 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__6___boxed), 4, 1);
lean_closure_set(x_259, 0, x_1);
x_260 = l_Lean_Core_withFreshMacroScope___rarg(x_259, x_168, x_8, x_9);
return x_260;
}
}
else
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
lean_dec(x_10);
x_261 = lean_unsigned_to_nat(2u);
x_262 = l_Lean_Syntax_getArg(x_1, x_261);
x_263 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__7), 10, 7);
lean_closure_set(x_263, 0, x_262);
lean_closure_set(x_263, 1, x_2);
lean_closure_set(x_263, 2, x_3);
lean_closure_set(x_263, 3, x_4);
lean_closure_set(x_263, 4, x_5);
lean_closure_set(x_263, 5, x_6);
lean_closure_set(x_263, 6, x_1);
x_264 = l_Lean_Core_withFreshMacroScope___rarg(x_263, x_168, x_8, x_9);
return x_264;
}
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
lean_dec(x_10);
x_265 = lean_unsigned_to_nat(0u);
x_266 = l_Lean_Syntax_getArg(x_1, x_265);
x_267 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__9), 11, 8);
lean_closure_set(x_267, 0, x_266);
lean_closure_set(x_267, 1, x_2);
lean_closure_set(x_267, 2, x_3);
lean_closure_set(x_267, 3, x_4);
lean_closure_set(x_267, 4, x_5);
lean_closure_set(x_267, 5, x_6);
lean_closure_set(x_267, 6, x_1);
lean_closure_set(x_267, 7, x_169);
x_268 = l_Lean_Core_withFreshMacroScope___rarg(x_267, x_168, x_8, x_9);
return x_268;
}
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
lean_dec(x_10);
x_269 = lean_unsigned_to_nat(0u);
x_270 = l_Lean_Syntax_getArg(x_1, x_269);
lean_dec(x_1);
x_271 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect_processCtor), 9, 6);
lean_closure_set(x_271, 0, x_270);
lean_closure_set(x_271, 1, x_2);
lean_closure_set(x_271, 2, x_3);
lean_closure_set(x_271, 3, x_4);
lean_closure_set(x_271, 4, x_5);
lean_closure_set(x_271, 5, x_6);
x_272 = l_Lean_Core_withFreshMacroScope___rarg(x_271, x_168, x_8, x_9);
return x_272;
}
}
else
{
lean_object* x_273; lean_object* x_274; uint8_t x_275; 
lean_dec(x_10);
x_273 = lean_unsigned_to_nat(1u);
x_274 = l_Lean_Syntax_getArg(x_1, x_273);
x_275 = l_Lean_Syntax_isNone(x_274);
if (x_275 == 0)
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; uint8_t x_279; 
x_276 = lean_unsigned_to_nat(0u);
x_277 = l_Lean_Syntax_getArg(x_274, x_276);
x_278 = l_Lean_Syntax_getArg(x_274, x_273);
x_279 = l_Lean_Syntax_isNone(x_278);
if (x_279 == 0)
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; uint8_t x_283; 
x_280 = l_Lean_Syntax_getArg(x_278, x_276);
lean_dec(x_278);
x_281 = l_Lean_Syntax_getKind(x_280);
x_282 = l_Lean_Elab_Term_CollectPatternVars_collect___closed__19;
x_283 = lean_name_eq(x_281, x_282);
lean_dec(x_281);
if (x_283 == 0)
{
lean_object* x_284; lean_object* x_285; 
lean_dec(x_277);
lean_dec(x_274);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_284 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__6___boxed), 4, 1);
lean_closure_set(x_284, 0, x_1);
x_285 = l_Lean_Core_withFreshMacroScope___rarg(x_284, x_168, x_8, x_9);
return x_285;
}
else
{
lean_object* x_286; lean_object* x_287; 
x_286 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__10), 11, 8);
lean_closure_set(x_286, 0, x_277);
lean_closure_set(x_286, 1, x_2);
lean_closure_set(x_286, 2, x_3);
lean_closure_set(x_286, 3, x_4);
lean_closure_set(x_286, 4, x_5);
lean_closure_set(x_286, 5, x_6);
lean_closure_set(x_286, 6, x_274);
lean_closure_set(x_286, 7, x_1);
x_287 = l_Lean_Core_withFreshMacroScope___rarg(x_286, x_168, x_8, x_9);
return x_287;
}
}
else
{
lean_object* x_288; lean_object* x_289; 
lean_dec(x_278);
x_288 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__10), 11, 8);
lean_closure_set(x_288, 0, x_277);
lean_closure_set(x_288, 1, x_2);
lean_closure_set(x_288, 2, x_3);
lean_closure_set(x_288, 3, x_4);
lean_closure_set(x_288, 4, x_5);
lean_closure_set(x_288, 5, x_6);
lean_closure_set(x_288, 6, x_274);
lean_closure_set(x_288, 7, x_1);
x_289 = l_Lean_Core_withFreshMacroScope___rarg(x_288, x_168, x_8, x_9);
return x_289;
}
}
else
{
lean_object* x_290; lean_object* x_291; 
lean_dec(x_274);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_290 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__6___boxed), 4, 1);
lean_closure_set(x_290, 0, x_1);
x_291 = l_Lean_Core_withFreshMacroScope___rarg(x_290, x_168, x_8, x_9);
return x_291;
}
}
}
else
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_292 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__8;
x_293 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__11___boxed), 5, 2);
lean_closure_set(x_293, 0, x_292);
lean_closure_set(x_293, 1, x_1);
x_294 = l_Lean_Core_withFreshMacroScope___rarg(x_293, x_168, x_8, x_9);
return x_294;
}
}
else
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_295 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___closed__8;
x_296 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__11___boxed), 5, 2);
lean_closure_set(x_296, 0, x_295);
lean_closure_set(x_296, 1, x_1);
x_297 = l_Lean_Core_withFreshMacroScope___rarg(x_296, x_168, x_8, x_9);
return x_297;
}
}
else
{
lean_object* x_298; lean_object* x_299; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_298 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__6___boxed), 4, 1);
lean_closure_set(x_298, 0, x_1);
x_299 = l_Lean_Core_withFreshMacroScope___rarg(x_298, x_168, x_8, x_9);
return x_299;
}
}
else
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; 
lean_dec(x_10);
x_300 = lean_unsigned_to_nat(1u);
x_301 = l_Lean_Syntax_getArg(x_1, x_300);
x_302 = l_Lean_Syntax_getArgs(x_301);
lean_dec(x_301);
x_303 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__12___boxed), 10, 7);
lean_closure_set(x_303, 0, x_302);
lean_closure_set(x_303, 1, x_2);
lean_closure_set(x_303, 2, x_3);
lean_closure_set(x_303, 3, x_4);
lean_closure_set(x_303, 4, x_5);
lean_closure_set(x_303, 5, x_6);
lean_closure_set(x_303, 6, x_1);
x_304 = l_Lean_Core_withFreshMacroScope___rarg(x_303, x_168, x_8, x_9);
return x_304;
}
}
else
{
lean_object* x_305; lean_object* x_306; 
lean_dec(x_10);
x_305 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp), 9, 6);
lean_closure_set(x_305, 0, x_1);
lean_closure_set(x_305, 1, x_2);
lean_closure_set(x_305, 2, x_3);
lean_closure_set(x_305, 3, x_4);
lean_closure_set(x_305, 4, x_5);
lean_closure_set(x_305, 5, x_6);
x_306 = l_Lean_Core_withFreshMacroScope___rarg(x_305, x_168, x_8, x_9);
return x_306;
}
}
else
{
lean_object* x_307; lean_object* x_308; 
lean_dec(x_10);
x_307 = lean_alloc_closure((void*)(l_Lean_Elab_Term_CollectPatternVars_collect_processId), 9, 6);
lean_closure_set(x_307, 0, x_1);
lean_closure_set(x_307, 1, x_2);
lean_closure_set(x_307, 2, x_3);
lean_closure_set(x_307, 3, x_4);
lean_closure_set(x_307, 4, x_5);
lean_closure_set(x_307, 5, x_6);
x_308 = l_Lean_Core_withFreshMacroScope___rarg(x_307, x_168, x_8, x_9);
return x_308;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_processCtor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_10 = l_Lean_Elab_Term_CollectPatternVars_State_vars___default___closed__1;
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
x_11 = 0;
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_inc(x_8);
x_12 = l_Lean_MonadRef_mkInfoFromRefPos___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___spec__2___rarg(x_8, x_9, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_st_ref_get(x_9, x_14);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__26;
x_18 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_18, 0, x_13);
lean_ctor_set(x_18, 1, x_17);
x_19 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__27;
x_20 = lean_array_push(x_19, x_18);
x_21 = lean_box(2);
x_22 = l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__25;
x_23 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_23, 2, x_20);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = l_Lean_Elab_Term_CollectPatternVars_collect_pushNewArg(x_1, x_2, x_24, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_16);
return x_25;
}
else
{
lean_object* x_26; 
x_26 = l_Lean_Elab_Term_CollectPatternVars_collect_processExplicitArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___spec__2(x_12, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_3);
lean_dec(x_3);
x_16 = l_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___lambda__2(x_1, x_2, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
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
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Elab_Term_CollectPatternVars_collect___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_16 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_17 = l_Subarray_forInUnsafe_loop___at_Lean_Elab_Term_CollectPatternVars_collect___spec__1(x_1, x_2, x_3, x_15, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_3);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_collect___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_collect___spec__2(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_Term_CollectPatternVars_collect___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_Elab_Term_CollectPatternVars_collect___spec__3(x_1, x_2, x_5, x_6);
lean_dec(x_2);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_CollectPatternVars_collect___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_CollectPatternVars_collect___spec__4(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Meta_0__Array_mapSepElemsMAux___at_Lean_Elab_Term_CollectPatternVars_collect___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Init_Meta_0__Array_mapSepElemsMAux___at_Lean_Elab_Term_CollectPatternVars_collect___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_mapSepElemsM___at_Lean_Elab_Term_CollectPatternVars_collect___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_mapSepElemsM___at_Lean_Elab_Term_CollectPatternVars_collect___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__6(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__11(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_CollectPatternVars_collect___lambda__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Term_CollectPatternVars_collect___lambda__12(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
x_1 = lean_mk_string_from_bytes("_traceMsg", 9);
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
x_1 = lean_mk_string_from_bytes("[", 1);
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
x_1 = lean_mk_string_from_bytes("] ", 2);
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
x_11 = lean_ctor_get(x_8, 5);
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
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_65 = lean_ctor_get(x_17, 0);
x_66 = lean_ctor_get(x_17, 1);
x_67 = lean_ctor_get(x_17, 2);
x_68 = lean_ctor_get(x_17, 4);
x_69 = lean_ctor_get(x_17, 5);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_17);
x_70 = lean_ctor_get_uint8(x_18, sizeof(void*)*1);
x_71 = lean_ctor_get(x_18, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 x_72 = x_18;
} else {
 lean_dec_ref(x_18);
 x_72 = lean_box(0);
}
x_73 = l_Lean_addTrace___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__2;
x_74 = l_Lean_Name_append(x_1, x_73);
x_75 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_75, 0, x_1);
x_76 = l_Lean_addTrace___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__4;
x_77 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
x_78 = l_Lean_addTrace___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__6;
x_79 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
x_80 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_15);
x_81 = l_Lean_Elab_Term_CollectPatternVars_collect_processExplicitArg___closed__3;
x_82 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
x_83 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_83, 0, x_74);
lean_ctor_set(x_83, 1, x_82);
lean_inc(x_11);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_11);
lean_ctor_set(x_84, 1, x_83);
x_85 = l_Std_PersistentArray_push___rarg(x_71, x_84);
if (lean_is_scalar(x_72)) {
 x_86 = lean_alloc_ctor(0, 1, 1);
} else {
 x_86 = x_72;
}
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set_uint8(x_86, sizeof(void*)*1, x_70);
x_87 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_87, 0, x_65);
lean_ctor_set(x_87, 1, x_66);
lean_ctor_set(x_87, 2, x_67);
lean_ctor_set(x_87, 3, x_86);
lean_ctor_set(x_87, 4, x_68);
lean_ctor_set(x_87, 5, x_69);
x_88 = lean_st_ref_set(x_9, x_87, x_19);
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
x_91 = lean_box(0);
if (lean_is_scalar(x_90)) {
 x_92 = lean_alloc_ctor(0, 2, 0);
} else {
 x_92 = x_90;
}
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_89);
return x_92;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Elab_Term_CollectPatternVars_main___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_7, 2);
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
x_1 = lean_mk_string_from_bytes("Elab", 4);
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
x_1 = lean_mk_string_from_bytes("match", 5);
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
x_1 = lean_mk_string_from_bytes("collecting variables at pattern: ", 33);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_collectPatternVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_Elab_Term_CollectPatternVars_instInhabitedState___closed__1;
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
x_15 = l_Lean_Elab_Term_CollectPatternVars_instInhabitedState___closed__1;
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
x_11 = lean_ctor_get(x_8, 5);
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
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_65 = lean_ctor_get(x_17, 0);
x_66 = lean_ctor_get(x_17, 1);
x_67 = lean_ctor_get(x_17, 2);
x_68 = lean_ctor_get(x_17, 4);
x_69 = lean_ctor_get(x_17, 5);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_17);
x_70 = lean_ctor_get_uint8(x_18, sizeof(void*)*1);
x_71 = lean_ctor_get(x_18, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 x_72 = x_18;
} else {
 lean_dec_ref(x_18);
 x_72 = lean_box(0);
}
x_73 = l_Lean_addTrace___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__2;
x_74 = l_Lean_Name_append(x_1, x_73);
x_75 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_75, 0, x_1);
x_76 = l_Lean_addTrace___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__4;
x_77 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
x_78 = l_Lean_addTrace___at_Lean_Elab_Term_CollectPatternVars_main___spec__1___closed__6;
x_79 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
x_80 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_15);
x_81 = l_Lean_Elab_Term_CollectPatternVars_collect_processExplicitArg___closed__3;
x_82 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
x_83 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_83, 0, x_74);
lean_ctor_set(x_83, 1, x_82);
lean_inc(x_11);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_11);
lean_ctor_set(x_84, 1, x_83);
x_85 = l_Std_PersistentArray_push___rarg(x_71, x_84);
if (lean_is_scalar(x_72)) {
 x_86 = lean_alloc_ctor(0, 1, 1);
} else {
 x_86 = x_72;
}
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set_uint8(x_86, sizeof(void*)*1, x_70);
x_87 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_87, 0, x_65);
lean_ctor_set(x_87, 1, x_66);
lean_ctor_set(x_87, 2, x_67);
lean_ctor_set(x_87, 3, x_86);
lean_ctor_set(x_87, 4, x_68);
lean_ctor_set(x_87, 5, x_69);
x_88 = lean_st_ref_set(x_9, x_87, x_19);
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
x_91 = lean_box(0);
if (lean_is_scalar(x_90)) {
 x_92 = lean_alloc_ctor(0, 2, 0);
} else {
 x_92 = x_90;
}
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_89);
return x_92;
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
x_12 = lean_ctor_get(x_8, 5);
x_13 = l_Lean_replaceRef(x_1, x_12);
lean_dec(x_12);
lean_ctor_set(x_8, 5, x_13);
x_14 = l_Lean_throwError___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___spec__1(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_15 = lean_ctor_get(x_8, 0);
x_16 = lean_ctor_get(x_8, 1);
x_17 = lean_ctor_get(x_8, 2);
x_18 = lean_ctor_get(x_8, 3);
x_19 = lean_ctor_get(x_8, 4);
x_20 = lean_ctor_get(x_8, 5);
x_21 = lean_ctor_get(x_8, 6);
x_22 = lean_ctor_get(x_8, 7);
x_23 = lean_ctor_get(x_8, 8);
x_24 = lean_ctor_get(x_8, 9);
x_25 = lean_ctor_get(x_8, 10);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_8);
x_26 = l_Lean_replaceRef(x_1, x_20);
lean_dec(x_20);
x_27 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_27, 0, x_15);
lean_ctor_set(x_27, 1, x_16);
lean_ctor_set(x_27, 2, x_17);
lean_ctor_set(x_27, 3, x_18);
lean_ctor_set(x_27, 4, x_19);
lean_ctor_set(x_27, 5, x_26);
lean_ctor_set(x_27, 6, x_21);
lean_ctor_set(x_27, 7, x_22);
lean_ctor_set(x_27, 8, x_23);
lean_ctor_set(x_27, 9, x_24);
lean_ctor_set(x_27, 10, x_25);
x_28 = l_Lean_throwError___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_finalize___spec__1(x_2, x_3, x_4, x_5, x_6, x_7, x_27, x_9, x_10);
lean_dec(x_27);
return x_28;
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
lean_object* x_16; uint8_t x_17; 
lean_free_object(x_6);
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
lean_dec(x_5);
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = l_liftExcept___at_Lean_Elab_liftMacroM___spec__1(x_15, x_3, x_16);
lean_dec(x_15);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 0);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = l_liftExcept___at_Lean_Elab_liftMacroM___spec__1(x_20, x_3, x_16);
lean_dec(x_20);
return x_21;
}
}
else
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_5, 1);
lean_inc(x_22);
lean_dec(x_5);
x_23 = !lean_is_exclusive(x_15);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_15, 0);
lean_ctor_set(x_6, 0, x_24);
lean_ctor_set(x_15, 0, x_6);
x_25 = l_liftExcept___at_Lean_Elab_liftMacroM___spec__1(x_15, x_3, x_22);
lean_dec(x_15);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_15, 0);
lean_inc(x_26);
lean_dec(x_15);
lean_ctor_set(x_6, 0, x_26);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_6);
x_28 = l_liftExcept___at_Lean_Elab_liftMacroM___spec__1(x_27, x_3, x_22);
lean_dec(x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_6, 0);
lean_inc(x_29);
lean_dec(x_6);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_5, 1);
lean_inc(x_31);
lean_dec(x_5);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 x_33 = x_30;
} else {
 lean_dec_ref(x_30);
 x_33 = lean_box(0);
}
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(0, 1, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_32);
x_35 = l_liftExcept___at_Lean_Elab_liftMacroM___spec__1(x_34, x_3, x_31);
lean_dec(x_34);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_5, 1);
lean_inc(x_36);
lean_dec(x_5);
x_37 = lean_ctor_get(x_30, 0);
lean_inc(x_37);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 x_38 = x_30;
} else {
 lean_dec_ref(x_30);
 x_38 = lean_box(0);
}
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_37);
if (lean_is_scalar(x_38)) {
 x_40 = lean_alloc_ctor(1, 1, 0);
} else {
 x_40 = x_38;
}
lean_ctor_set(x_40, 0, x_39);
x_41 = l_liftExcept___at_Lean_Elab_liftMacroM___spec__1(x_40, x_3, x_36);
lean_dec(x_40);
return x_41;
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_10 = lean_st_ref_get(x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_7, 3);
lean_inc(x_14);
x_15 = lean_ctor_get(x_7, 4);
lean_inc(x_15);
x_16 = lean_ctor_get(x_7, 5);
lean_inc(x_16);
x_17 = lean_ctor_get(x_7, 6);
lean_inc(x_17);
x_18 = lean_ctor_get(x_7, 7);
lean_inc(x_18);
x_19 = lean_ctor_get(x_7, 10);
lean_inc(x_19);
lean_inc(x_13);
x_20 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_getPatternsVars___spec__1___lambda__1___boxed), 4, 1);
lean_closure_set(x_20, 0, x_13);
lean_inc(x_17);
x_21 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_Elab_liftMacroM___spec__2___rarg___boxed), 3, 1);
lean_closure_set(x_21, 0, x_17);
lean_inc(x_13);
x_22 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_getPatternsVars___spec__1___lambda__2___boxed), 4, 1);
lean_closure_set(x_22, 0, x_13);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_13);
x_23 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_getPatternsVars___spec__1___lambda__3___boxed), 6, 3);
lean_closure_set(x_23, 0, x_13);
lean_closure_set(x_23, 1, x_17);
lean_closure_set(x_23, 2, x_18);
lean_inc(x_13);
x_24 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_getPatternsVars___spec__1___lambda__4___boxed), 6, 3);
lean_closure_set(x_24, 0, x_13);
lean_closure_set(x_24, 1, x_17);
lean_closure_set(x_24, 2, x_18);
x_25 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_21);
lean_ctor_set(x_25, 2, x_22);
lean_ctor_set(x_25, 3, x_23);
lean_ctor_set(x_25, 4, x_24);
x_26 = lean_st_ref_get(x_8, x_12);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_environment_main_module(x_13);
x_31 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_31, 0, x_25);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_31, 2, x_19);
lean_ctor_set(x_31, 3, x_14);
lean_ctor_set(x_31, 4, x_15);
lean_ctor_set(x_31, 5, x_16);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_29);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_apply_2(x_1, x_31, x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_st_ref_take(x_8, x_28);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = !lean_is_exclusive(x_39);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_42 = lean_ctor_get(x_39, 1);
lean_dec(x_42);
lean_ctor_set(x_39, 1, x_37);
x_43 = lean_st_ref_set(x_8, x_39, x_40);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_45 = lean_ctor_get(x_36, 1);
lean_inc(x_45);
lean_dec(x_36);
x_46 = l_List_reverse___rarg(x_45);
x_47 = l_List_forM___at_Lean_Elab_Term_getPatternsVars___spec__3(x_46, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_44);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_47, 0);
lean_dec(x_49);
lean_ctor_set(x_47, 0, x_35);
return x_47;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_dec(x_47);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_35);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_52 = lean_ctor_get(x_39, 0);
x_53 = lean_ctor_get(x_39, 2);
x_54 = lean_ctor_get(x_39, 3);
x_55 = lean_ctor_get(x_39, 4);
x_56 = lean_ctor_get(x_39, 5);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_39);
x_57 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_57, 0, x_52);
lean_ctor_set(x_57, 1, x_37);
lean_ctor_set(x_57, 2, x_53);
lean_ctor_set(x_57, 3, x_54);
lean_ctor_set(x_57, 4, x_55);
lean_ctor_set(x_57, 5, x_56);
x_58 = lean_st_ref_set(x_8, x_57, x_40);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_60 = lean_ctor_get(x_36, 1);
lean_inc(x_60);
lean_dec(x_36);
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
lean_ctor_set(x_65, 0, x_35);
lean_ctor_set(x_65, 1, x_63);
return x_65;
}
}
else
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_34, 0);
lean_inc(x_66);
lean_dec(x_34);
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
x_73 = l_Lean_throwErrorAt___at_Lean_Elab_Term_getPatternsVars___spec__4(x_67, x_72, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_28);
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
x_74 = l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_getPatternsVars___spec__5(x_67, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_28);
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
x_75 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_getPatternsVars___spec__6___rarg(x_28);
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
x_14 = l_Lean_Elab_Term_CollectPatternVars_instInhabitedState___closed__1;
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_getPatternVarNames___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_8 = l_Lean_Syntax_getId(x_5);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_getPatternVarNames(lean_object* x_1) {
_start:
{
lean_object* x_2; size_t x_3; size_t x_4; lean_object* x_5; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_usize_of_nat(x_2);
lean_dec(x_2);
x_4 = 0;
x_5 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_getPatternVarNames___spec__1(x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_getPatternVarNames___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_getPatternVarNames___spec__1(x_4, x_5, x_3);
return x_6;
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
l_Lean_Elab_Term_CollectPatternVars_State_found___default = _init_l_Lean_Elab_Term_CollectPatternVars_State_found___default();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_State_found___default);
l_Lean_Elab_Term_CollectPatternVars_State_vars___default___closed__1 = _init_l_Lean_Elab_Term_CollectPatternVars_State_vars___default___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_State_vars___default___closed__1);
l_Lean_Elab_Term_CollectPatternVars_State_vars___default = _init_l_Lean_Elab_Term_CollectPatternVars_State_vars___default();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_State_vars___default);
l_Lean_Elab_Term_CollectPatternVars_instInhabitedState___closed__1 = _init_l_Lean_Elab_Term_CollectPatternVars_instInhabitedState___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_instInhabitedState___closed__1);
l_Lean_Elab_Term_CollectPatternVars_instInhabitedState = _init_l_Lean_Elab_Term_CollectPatternVars_instInhabitedState();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_instInhabitedState);
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
l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__36 = _init_l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__36();
lean_mark_persistent(l___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_nameToPattern___closed__36);
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
l_Lean_resolveGlobalConstNoOverload___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__2___closed__3 = _init_l_Lean_resolveGlobalConstNoOverload___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__2___closed__3();
lean_mark_persistent(l_Lean_resolveGlobalConstNoOverload___at___private_Lean_Elab_PatternVar_0__Lean_Elab_Term_CollectPatternVars_doubleQuotedNameToPattern___spec__2___closed__3);
l_panic___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___spec__1___closed__1 = _init_l_panic___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___spec__1___closed__1();
lean_mark_persistent(l_panic___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___spec__1___closed__1);
l_panic___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___spec__1___closed__2 = _init_l_panic___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___spec__1___closed__2();
lean_mark_persistent(l_panic___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___spec__1___closed__2);
l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___spec__2___closed__1 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___spec__2___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___spec__2___closed__1);
l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___spec__2___closed__2 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___spec__2___closed__2();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___spec__2___closed__2);
l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___spec__2___closed__3 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___spec__2___closed__3();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___spec__2___closed__3);
l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___spec__2___closed__4 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___spec__2___closed__4();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___spec__2___closed__4);
l_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___lambda__2___closed__1 = _init_l_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___lambda__2___closed__1);
l_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___lambda__2___closed__2 = _init_l_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___lambda__2___closed__2);
l_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___closed__1 = _init_l_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___closed__1);
l_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___closed__2 = _init_l_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___closed__2);
l_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___closed__3 = _init_l_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___closed__3);
l_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___closed__4 = _init_l_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect_processCtorApp___closed__4);
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
l_Lean_Elab_Term_CollectPatternVars_collect_pushNewArg___closed__1 = _init_l_Lean_Elab_Term_CollectPatternVars_collect_pushNewArg___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect_pushNewArg___closed__1);
l_Lean_Elab_Term_CollectPatternVars_collect_pushNewArg___closed__2 = _init_l_Lean_Elab_Term_CollectPatternVars_collect_pushNewArg___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect_pushNewArg___closed__2);
l_Subarray_forInUnsafe_loop___at_Lean_Elab_Term_CollectPatternVars_collect___spec__1___closed__1 = _init_l_Subarray_forInUnsafe_loop___at_Lean_Elab_Term_CollectPatternVars_collect___spec__1___closed__1();
lean_mark_persistent(l_Subarray_forInUnsafe_loop___at_Lean_Elab_Term_CollectPatternVars_collect___spec__1___closed__1);
l_Subarray_forInUnsafe_loop___at_Lean_Elab_Term_CollectPatternVars_collect___spec__1___closed__2 = _init_l_Subarray_forInUnsafe_loop___at_Lean_Elab_Term_CollectPatternVars_collect___spec__1___closed__2();
lean_mark_persistent(l_Subarray_forInUnsafe_loop___at_Lean_Elab_Term_CollectPatternVars_collect___spec__1___closed__2);
l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_collect___spec__2___closed__1 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_collect___spec__2___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_collect___spec__2___closed__1);
l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_collect___spec__2___closed__2 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_collect___spec__2___closed__2();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_collect___spec__2___closed__2);
l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_collect___spec__2___closed__3 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_collect___spec__2___closed__3();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Term_CollectPatternVars_collect___spec__2___closed__3);
l_Array_anyMUnsafe_any___at_Lean_Elab_Term_CollectPatternVars_collect___spec__3___closed__1 = _init_l_Array_anyMUnsafe_any___at_Lean_Elab_Term_CollectPatternVars_collect___spec__3___closed__1();
lean_mark_persistent(l_Array_anyMUnsafe_any___at_Lean_Elab_Term_CollectPatternVars_collect___spec__3___closed__1);
l_Lean_Elab_Term_CollectPatternVars_collect___lambda__2___closed__1 = _init_l_Lean_Elab_Term_CollectPatternVars_collect___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__2___closed__1);
l_Lean_Elab_Term_CollectPatternVars_collect___lambda__2___closed__2 = _init_l_Lean_Elab_Term_CollectPatternVars_collect___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__2___closed__2);
l_Lean_Elab_Term_CollectPatternVars_collect___lambda__2___closed__3 = _init_l_Lean_Elab_Term_CollectPatternVars_collect___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__2___closed__3);
l_Lean_Elab_Term_CollectPatternVars_collect___lambda__2___closed__4 = _init_l_Lean_Elab_Term_CollectPatternVars_collect___lambda__2___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__2___closed__4);
l_Lean_Elab_Term_CollectPatternVars_collect___lambda__2___closed__5 = _init_l_Lean_Elab_Term_CollectPatternVars_collect___lambda__2___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__2___closed__5);
l_Lean_Elab_Term_CollectPatternVars_collect___lambda__2___closed__6 = _init_l_Lean_Elab_Term_CollectPatternVars_collect___lambda__2___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__2___closed__6);
l_Lean_Elab_Term_CollectPatternVars_collect___lambda__2___closed__7 = _init_l_Lean_Elab_Term_CollectPatternVars_collect___lambda__2___closed__7();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__2___closed__7);
l_Lean_Elab_Term_CollectPatternVars_collect___lambda__2___closed__8 = _init_l_Lean_Elab_Term_CollectPatternVars_collect___lambda__2___closed__8();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__2___closed__8);
l_Lean_Elab_Term_CollectPatternVars_collect___lambda__3___closed__1 = _init_l_Lean_Elab_Term_CollectPatternVars_collect___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__3___closed__1);
l_Lean_Elab_Term_CollectPatternVars_collect___lambda__3___closed__2 = _init_l_Lean_Elab_Term_CollectPatternVars_collect___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__3___closed__2);
l_Lean_Elab_Term_CollectPatternVars_collect___lambda__5___closed__1 = _init_l_Lean_Elab_Term_CollectPatternVars_collect___lambda__5___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__5___closed__1);
l_Lean_Elab_Term_CollectPatternVars_collect___lambda__8___closed__1 = _init_l_Lean_Elab_Term_CollectPatternVars_collect___lambda__8___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__8___closed__1);
l_Lean_Elab_Term_CollectPatternVars_collect___lambda__8___closed__2 = _init_l_Lean_Elab_Term_CollectPatternVars_collect___lambda__8___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__8___closed__2);
l_Lean_Elab_Term_CollectPatternVars_collect___lambda__8___closed__3 = _init_l_Lean_Elab_Term_CollectPatternVars_collect___lambda__8___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__8___closed__3);
l_Lean_Elab_Term_CollectPatternVars_collect___lambda__8___closed__4 = _init_l_Lean_Elab_Term_CollectPatternVars_collect___lambda__8___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__8___closed__4);
l_Lean_Elab_Term_CollectPatternVars_collect___lambda__8___closed__5 = _init_l_Lean_Elab_Term_CollectPatternVars_collect___lambda__8___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__8___closed__5);
l_Lean_Elab_Term_CollectPatternVars_collect___lambda__8___closed__6 = _init_l_Lean_Elab_Term_CollectPatternVars_collect___lambda__8___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__8___closed__6);
l_Lean_Elab_Term_CollectPatternVars_collect___lambda__8___closed__7 = _init_l_Lean_Elab_Term_CollectPatternVars_collect___lambda__8___closed__7();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__8___closed__7);
l_Lean_Elab_Term_CollectPatternVars_collect___lambda__8___closed__8 = _init_l_Lean_Elab_Term_CollectPatternVars_collect___lambda__8___closed__8();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__8___closed__8);
l_Lean_Elab_Term_CollectPatternVars_collect___lambda__8___closed__9 = _init_l_Lean_Elab_Term_CollectPatternVars_collect___lambda__8___closed__9();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__8___closed__9);
l_Lean_Elab_Term_CollectPatternVars_collect___lambda__8___closed__10 = _init_l_Lean_Elab_Term_CollectPatternVars_collect___lambda__8___closed__10();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__8___closed__10);
l_Lean_Elab_Term_CollectPatternVars_collect___lambda__9___closed__1 = _init_l_Lean_Elab_Term_CollectPatternVars_collect___lambda__9___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__9___closed__1);
l_Lean_Elab_Term_CollectPatternVars_collect___lambda__9___closed__2 = _init_l_Lean_Elab_Term_CollectPatternVars_collect___lambda__9___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__9___closed__2);
l_Lean_Elab_Term_CollectPatternVars_collect___lambda__9___closed__3 = _init_l_Lean_Elab_Term_CollectPatternVars_collect___lambda__9___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__9___closed__3);
l_Lean_Elab_Term_CollectPatternVars_collect___lambda__9___closed__4 = _init_l_Lean_Elab_Term_CollectPatternVars_collect___lambda__9___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__9___closed__4);
l_Lean_Elab_Term_CollectPatternVars_collect___lambda__11___closed__1 = _init_l_Lean_Elab_Term_CollectPatternVars_collect___lambda__11___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__11___closed__1);
l_Lean_Elab_Term_CollectPatternVars_collect___lambda__11___closed__2 = _init_l_Lean_Elab_Term_CollectPatternVars_collect___lambda__11___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__11___closed__2);
l_Lean_Elab_Term_CollectPatternVars_collect___lambda__11___closed__3 = _init_l_Lean_Elab_Term_CollectPatternVars_collect___lambda__11___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__11___closed__3);
l_Lean_Elab_Term_CollectPatternVars_collect___lambda__12___closed__1 = _init_l_Lean_Elab_Term_CollectPatternVars_collect___lambda__12___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_CollectPatternVars_collect___lambda__12___closed__1);
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
