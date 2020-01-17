// Lean compiler output
// Module: Init.Lean.Elab.Tactic.Basic
// Imports: Init.Lean.Elab.Util Init.Lean.Elab.Term Init.Lean.Meta.Tactic.Assumption Init.Lean.Meta.Tactic.Intro
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
lean_object* l_Lean_SMap_find_x3f___at_Lean_Elab_Tactic_evalTactic___main___spec__1(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Tactic_Basic_2__regTraceClasses___closed__1;
lean_object* l_Lean_Elab_Tactic_withIncRecDepth___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTactic_Lean_Elab_Tactic_evalIntro(lean_object*);
lean_object* l_Lean_Elab_Tactic_monadLog;
extern lean_object* l_Lean_Name_toString___closed__1;
lean_object* l___private_Init_Lean_Elab_Tactic_Basic_1__evalTacticUsing___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getLocalInsts___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_declareLeadingBuiltinParser___closed__1;
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l___regBuiltinTactic_Lean_Elab_Tactic_evalSeq___closed__4;
lean_object* l_Lean_Elab_Tactic_withMVarContext___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_PersistentHashMap_contains___at_Lean_Elab_Tactic_addBuiltinTactic___spec__4(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTactic___main___closed__3;
extern lean_object* l_Lean_Parser_declareBuiltinParser___closed__8;
lean_object* l_PersistentHashMap_find_x3f___at_Lean_Elab_Tactic_evalTactic___main___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_monadLog___lambda__4(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_nameToExprAux___main___closed__1;
lean_object* l_Lean_Elab_Tactic_monadQuotation;
lean_object* l_unreachable_x21___rarg(lean_object*);
lean_object* l_Lean_Elab_Tactic_registerBuiltinTacticAttr(lean_object*);
extern lean_object* l_Lean_Elab_Term_elabTermAux___main___closed__6;
lean_object* l_Lean_Elab_Tactic_mkTacticAttribute(lean_object*);
lean_object* l_Lean_Elab_Tactic_getMCtx___rarg(lean_object*);
extern lean_object* l_Lean_MessageData_ofList___closed__3;
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Elab_Tactic_registerBuiltinTacticAttr___lambda__1___closed__2;
lean_object* l_Lean_Elab_Tactic_evalIntro___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_Elab_Tactic_evalTactic___main___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getEnv(lean_object*);
extern size_t l_PersistentHashMap_insertAux___main___rarg___closed__2;
lean_object* l_Lean_Elab_Tactic_trace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Tactic_Basic_1__evalTacticUsing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getLCtx___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_monadQuotation___closed__2;
lean_object* l_Lean_Elab_Tactic_evalIntro___lambda__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_liftMetaM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_declareBuiltinTactic(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_HashMapImp_find_x3f___at_Lean_Elab_Tactic_evalTactic___main___spec__5___boxed(lean_object*, lean_object*);
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_resettingSynthInstanceCacheWhen(lean_object*);
lean_object* l_Lean_Elab_Tactic_monadQuotation___closed__1;
lean_object* lean_dbg_trace(lean_object*, lean_object*);
lean_object* lean_io_mk_ref(lean_object*, lean_object*);
lean_object* l_Lean_Elab_ElabFnTable_insert___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_append___rarg(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_io_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTactic(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Tactic_Basic_2__regTraceClasses(lean_object*);
uint8_t l_PersistentHashMap_containsAtAux___main___at_Lean_Parser_mkFreshKindAux___main___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_resettingSynthInstanceCacheWhen___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalIntro(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTactic_Lean_Elab_Tactic_evalSeq___closed__1;
lean_object* l_PersistentHashMap_findAux___main___at_Lean_Elab_Tactic_evalTactic___main___spec__3(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Meta_assumption___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t l_Lean_SMap_contains___at_Lean_Elab_Tactic_addBuiltinTactic___spec__1(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMCtx___boxed(lean_object*);
lean_object* l_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_registerBuiltinTacticAttr___closed__2;
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* l_Lean_Elab_Term_logTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withFreshMacroScope(lean_object*);
extern lean_object* l_Lean_Meta_isLevelDefEqAux___main___closed__5;
lean_object* l_AssocList_find___main___at_Lean_Elab_Tactic_evalTactic___main___spec__6___boxed(lean_object*, lean_object*);
size_t l_USize_shiftRight(size_t, size_t);
lean_object* l_Lean_Elab_Tactic_resettingSynthInstanceCacheWhen___rarg(uint8_t, lean_object*, lean_object*, lean_object*);
uint8_t l_PersistentHashMap_containsAux___main___at_Lean_Elab_Tactic_addBuiltinTactic___spec__5(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Elab_Tactic_getLocalInsts(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_monadLog___closed__10;
lean_object* l_Lean_Elab_Tactic_mkTacticAttribute___closed__1;
lean_object* l_Lean_Elab_Tactic_registerBuiltinTacticAttr___closed__4;
extern lean_object* l_Lean_LocalContext_Inhabited___closed__1;
extern lean_object* l___private_Init_Lean_Elab_Util_8__regTraceClasses___closed__2;
lean_object* l_Lean_Elab_Term_trace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_tacticElabAttribute___closed__2;
extern lean_object* l_Lean_AttributeImpl_inhabited___closed__2;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_IO_ofExcept___at_Lean_registerClassAttr___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_registerBuiltinTacticAttr___closed__1;
lean_object* l_Lean_Elab_Tactic_monadLog___closed__3;
extern lean_object* l_Lean_Parser_Tactic_intro___elambda__1___closed__1;
extern lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg___closed__1;
lean_object* l_Lean_Meta_intro(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Exception_toMessageData___closed__45;
lean_object* l_Lean_Elab_Tactic_liftMetaTactic___closed__1;
lean_object* l_Array_isEqvAux___main___at_Lean_Elab_Tactic_withMVarContext___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_declareBuiltinTactic___closed__7;
extern lean_object* l_Lean_Meta_dbgTrace___rarg___closed__1;
lean_object* l_Lean_Elab_Tactic_evalTactic___main___closed__2;
extern lean_object* l_Lean_Elab_Term_withIncRecDepth___rarg___closed__2;
lean_object* l_Lean_SMap_find_x3f___at_Lean_Elab_Tactic_evalTactic___main___spec__1___boxed(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_declareBuiltinTactic___closed__5;
extern lean_object* l_Lean_Elab_Term_declareBuiltinTermElab___closed__3;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_termElabAttribute___closed__4;
lean_object* l_Lean_Elab_Term_addContext___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Elab_Tactic_monadLog___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_EnvExtension_Inhabited___rarg___closed__1;
lean_object* l_Lean_Elab_Tactic_declareBuiltinTactic___closed__3;
lean_object* l_Lean_Elab_Tactic_monadLog___closed__5;
lean_object* l_Lean_Name_append___main(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAux___main___at_Lean_Elab_Tactic_evalTactic___main___spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_dbgTrace___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_addContext(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalSeq___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_contains___at_Lean_Elab_Tactic_addBuiltinTactic___spec__4___boxed(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_liftTermElabM(lean_object*);
lean_object* l___regBuiltinTactic_Lean_Elab_Tactic_evalAssumption___closed__4;
lean_object* l_PersistentHashMap_find_x3f___at_Lean_Elab_Tactic_evalTactic___main___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_monadLog___lambda__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_resetSynthInstanceCache___closed__1;
lean_object* l___regBuiltinTactic_Lean_Elab_Tactic_evalAssumption___closed__2;
uint8_t l_Array_isEqvAux___main___at_Lean_Elab_Tactic_withMVarContext___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_Lean_Name_hash(lean_object*);
extern lean_object* l_Lean_Elab_Term_State_inhabited___closed__2;
extern lean_object* l_Char_HasRepr___closed__1;
lean_object* l___regBuiltinTactic_Lean_Elab_Tactic_evalAssumption___closed__1;
lean_object* l_Lean_Elab_Tactic_getMVarDecl___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_resetSynthInstanceCache(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_containsAux___main___at_Lean_Elab_Tactic_addBuiltinTactic___spec__5___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_monadLog___closed__7;
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_Syntax_prettyPrint(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_builtinTacticTable;
lean_object* l_Lean_Elab_Tactic_tacticElabAttribute___closed__4;
lean_object* l_Lean_Elab_Tactic_monadLog___lambda__4___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_State_inhabited___closed__1;
lean_object* l___regBuiltinTactic_Lean_Elab_Tactic_evalSeq___closed__2;
lean_object* l_Lean_Elab_Tactic_monadLog___lambda__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_throwUnsupportedSyntax___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_declareBuiltinParser___closed__7;
lean_object* l_Lean_Elab_Tactic_monadLog___closed__8;
extern lean_object* l_Lean_Options_empty;
lean_object* l___regBuiltinTactic_Lean_Elab_Tactic_evalSeq(lean_object*);
lean_object* l_Lean_Elab_Tactic_withLCtx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_coeDecidableEq(uint8_t);
lean_object* l_ReaderT_read___at_Lean_Elab_Tactic_monadLog___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_foldArgsAuxM___main___at_Lean_Elab_Tactic_evalSeq___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_modn(size_t, lean_object*);
lean_object* l_Lean_Elab_Tactic_tacticElabAttribute___closed__1;
lean_object* l_Lean_Elab_Tactic_registerBuiltinTacticAttr___lambda__1___closed__3;
lean_object* l_Lean_registerBuiltinAttribute(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_monadLog___closed__1;
lean_object* l_Lean_Elab_mkElabAttribute___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_registerBuiltinTacticAttr___closed__5;
lean_object* l_mkHashMapImp___rarg(lean_object*);
lean_object* l___regBuiltinTactic_Lean_Elab_Tactic_evalIntro___closed__3;
lean_object* l_Lean_Elab_Tactic_declareBuiltinTactic___closed__6;
extern lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg___closed__3;
lean_object* l_Lean_Elab_Tactic_liftMetaM(lean_object*);
lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
extern lean_object* l_Lean_Parser_Term_seq___elambda__1___closed__1;
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_Elab_Tactic_State_inhabited;
lean_object* l_HashMapImp_find_x3f___at_Lean_Elab_Tactic_evalTactic___main___spec__5(lean_object*, lean_object*);
size_t l_USize_land(size_t, size_t);
extern lean_object* l_Lean_nullKind___closed__2;
lean_object* l_Lean_Elab_Tactic_monadLog___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParametricAttribute_setParam___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalAssumption___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_liftMetaTactic___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTactic_Lean_Elab_Tactic_evalAssumption(lean_object*);
lean_object* l_Lean_Elab_Tactic_registerBuiltinTacticAttr___closed__3;
lean_object* l_Lean_Elab_Tactic_registerBuiltinTacticAttr___lambda__1___closed__5;
lean_object* l_Lean_Elab_Term_traceAtCmdPos___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_registerBuiltinTacticAttr___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_throwUnsupportedSyntax(lean_object*);
lean_object* l_Lean_Elab_Tactic_registerBuiltinTacticAttr___lambda__1___closed__1;
lean_object* l_Lean_Elab_Tactic_withLCtx(lean_object*);
lean_object* l_Lean_Elab_Term_liftMetaM___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTactic___main___closed__4;
lean_object* l_Lean_Elab_Tactic_registerBuiltinTacticAttr___lambda__1___closed__4;
lean_object* l_Lean_Elab_Tactic_evalAssumption___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_declareBuiltinTactic___closed__4;
extern lean_object* l_Lean_Elab_Exception_inhabited;
lean_object* l_Lean_Elab_Tactic_liftTermElabM___rarg___closed__1;
lean_object* l_Lean_Elab_Tactic_evalAssumption___closed__1;
extern lean_object* l_Lean_Meta_assumptionAux___closed__1;
lean_object* l_Lean_Elab_Tactic_liftMetaTactic(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTactic___main___closed__1;
lean_object* l_Lean_Elab_Tactic_evalTactic___main___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_empty___at_Lean_Elab_Tactic_mkBuiltinTacticTable___spec__3;
lean_object* l_ReaderT_bind___at_Lean_Elab_Tactic_monadLog___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_liftMetaTactic___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTactic___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_nameToExprAux___main(lean_object*);
lean_object* l_Lean_Elab_Tactic_declareBuiltinTactic___closed__1;
lean_object* l_Lean_Elab_Term_throwError___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Elab_Tactic_monadLog___closed__6;
lean_object* l_Lean_Elab_Tactic_evalSeq(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_addAndCompile(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Elab_Tactic_resettingSynthInstanceCache(lean_object*);
lean_object* l_Lean_Elab_Tactic_evalIntro___closed__1;
lean_object* l_Lean_Elab_Tactic_evalAssumption(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_monadLog___closed__2;
lean_object* l_Lean_Elab_Tactic_addBuiltinTactic(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getOptions___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_declareBuiltinTactic___closed__2;
lean_object* l_Lean_Elab_Tactic_withMVarContext___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_logTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_ref_reset(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withFreshMacroScope___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Init_Lean_Elab_Term_9__elabTermUsing___main___closed__3;
lean_object* l_Lean_SMap_empty___at_Lean_Elab_Tactic_mkBuiltinTacticTable___spec__1;
lean_object* l_Lean_Elab_Tactic_throwError(lean_object*);
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_Elab_Tactic_evalTactic___main___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos(lean_object*);
lean_object* l_Lean_Elab_Tactic_mkBuiltinTacticTable(lean_object*);
lean_object* l_Lean_Elab_Tactic_addBuiltinTactic___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_empty___at_Lean_Elab_Tactic_mkBuiltinTacticTable___spec__1___closed__1;
lean_object* l_Lean_Elab_Tactic_addBuiltinTactic___closed__1;
lean_object* l_Lean_Elab_Term_instantiateMVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_empty___at_Lean_Elab_Tactic_mkBuiltinTacticTable___spec__1___closed__2;
lean_object* lean_io_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_liftTermElabM___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getOptions(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_tacticElabAttribute___closed__5;
lean_object* l_Lean_Elab_Tactic_getEnv___rarg(lean_object*);
lean_object* l___regBuiltinTactic_Lean_Elab_Tactic_evalSeq___closed__3;
lean_object* l_Lean_Meta_intro1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withMacroExpansion___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_instantiateMVars(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_find___main___at_Lean_Elab_Tactic_evalTactic___main___spec__6(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_monadLog___lambda__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_registerBuiltinTacticAttr___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_tacticElabAttribute___closed__3;
lean_object* l_Lean_Elab_Tactic_evalIntro___lambda__2(lean_object*, lean_object*, lean_object*);
lean_object* l_HashMapImp_contains___at_Lean_Elab_Tactic_addBuiltinTactic___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_foldArgsAuxM___main___at_Lean_Elab_Tactic_evalSeq___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_regBuiltinTacticParserAttr___closed__3;
extern lean_object* l___private_Init_Lean_Parser_Parser_8__throwParserCategoryAlreadyDefined___rarg___closed__2;
extern lean_object* l___private_Init_Lean_Meta_Tactic_Util_1__regTraceClasses___closed__1;
lean_object* l_Lean_Elab_Tactic_throwUnsupportedSyntax___rarg(lean_object*, lean_object*);
uint8_t l_AssocList_contains___main___at_Lean_Elab_Tactic_addBuiltinTactic___spec__3(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMVarDecl(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTactic___main___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l___regBuiltinTactic_Lean_Elab_Tactic_evalIntro___closed__2;
lean_object* l_Lean_Elab_Tactic_monadLog___closed__11;
lean_object* l_Lean_SMap_contains___at_Lean_Elab_Tactic_addBuiltinTactic___spec__1___boxed(lean_object*, lean_object*);
uint8_t l_Lean_LocalInstance_beq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalIntro___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withMVarContext(lean_object*);
lean_object* l_Lean_Elab_Tactic_withMacroExpansion(lean_object*);
lean_object* l_Lean_MetavarContext_getDecl(lean_object*, lean_object*);
uint8_t l_HashMapImp_contains___at_Lean_Elab_Tactic_addBuiltinTactic___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_resetSynthInstanceCache___boxed(lean_object*);
lean_object* l_Lean_Elab_Tactic_monadLog___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_liftMetaTactic___closed__3;
extern lean_object* l_Lean_Parser_regBuiltinTacticParserAttr___closed__4;
lean_object* l___regBuiltinTactic_Lean_Elab_Tactic_evalAssumption___closed__3;
lean_object* l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_dbgTrace(lean_object*);
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
extern lean_object* l___private_Init_Lean_Elab_Util_8__regTraceClasses___closed__1;
lean_object* l_Lean_Elab_Tactic_monadLog___lambda__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_Elab_Tactic_getCurrMacroScope(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_resettingSynthInstanceCache___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_throwUnsupportedSyntax___rarg___closed__1;
lean_object* l_Lean_Elab_Tactic_monadQuotation___closed__3;
lean_object* l_IO_ofExcept___at___private_Init_Lean_Elab_Util_6__ElabAttribute_add___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getCurrMacroScope___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_liftMetaTactic___closed__2;
extern uint8_t l___private_Init_Lean_Elab_Term_4__hasCDot___main___closed__1;
extern lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg___closed__4;
lean_object* l_Lean_Elab_Tactic_traceAtCmdPos(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_initAttr;
lean_object* l_Lean_Elab_syntaxNodeKindOfAttrParam(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getLCtx(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getEnv___boxed(lean_object*);
lean_object* l___regBuiltinTactic_Lean_Elab_Tactic_evalIntro___closed__1;
lean_object* l_AssocList_contains___main___at_Lean_Elab_Tactic_addBuiltinTactic___spec__3___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_monadLog___closed__4;
lean_object* l_Lean_Elab_Tactic_getMCtx(lean_object*);
lean_object* l_Lean_Elab_Tactic_throwError___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Init_Lean_Parser_Parser_18__BuiltinParserAttribute_add___closed__2;
lean_object* l_mkHashMap___at_Lean_Elab_Tactic_mkBuiltinTacticTable___spec__2(lean_object*);
lean_object* l_Lean_Elab_Tactic_monadLog___closed__9;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_expandMacro(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withIncRecDepth(lean_object*);
lean_object* _init_l_Lean_Elab_Tactic_State_inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_State_inhabited___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Tactic_State_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Tactic_State_inhabited___closed__1;
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Tactic_liftTermElabM___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Exception_inhabited;
x_2 = l_Lean_Elab_Tactic_State_inhabited;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Tactic_liftTermElabM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_apply_2(x_1, x_4, x_6);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_8, 1);
lean_ctor_set(x_3, 0, x_10);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_8, 0);
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_8);
lean_ctor_set(x_3, 0, x_12);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_3);
return x_13;
}
}
else
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_8, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_8);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_8, 1);
x_17 = lean_ctor_get(x_8, 0);
lean_dec(x_17);
x_18 = lean_ctor_get(x_14, 0);
lean_inc(x_18);
lean_dec(x_14);
lean_ctor_set(x_3, 0, x_16);
lean_ctor_set(x_8, 1, x_3);
lean_ctor_set(x_8, 0, x_18);
return x_8;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_8, 1);
lean_inc(x_19);
lean_dec(x_8);
x_20 = lean_ctor_get(x_14, 0);
lean_inc(x_20);
lean_dec(x_14);
lean_ctor_set(x_3, 0, x_19);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_3);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_8);
lean_free_object(x_3);
lean_dec(x_7);
x_22 = l_Lean_Elab_Tactic_liftTermElabM___rarg___closed__1;
x_23 = l_unreachable_x21___rarg(x_22);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_3, 0);
x_25 = lean_ctor_get(x_3, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_3);
x_26 = lean_apply_2(x_1, x_4, x_24);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_29 = x_26;
} else {
 lean_dec_ref(x_26);
 x_29 = lean_box(0);
}
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_25);
if (lean_is_scalar(x_29)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_29;
}
lean_ctor_set(x_31, 0, x_27);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
else
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_26, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_26, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_34 = x_26;
} else {
 lean_dec_ref(x_26);
 x_34 = lean_box(0);
}
x_35 = lean_ctor_get(x_32, 0);
lean_inc(x_35);
lean_dec(x_32);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_25);
if (lean_is_scalar(x_34)) {
 x_37 = lean_alloc_ctor(1, 2, 0);
} else {
 x_37 = x_34;
}
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_26);
lean_dec(x_25);
x_38 = l_Lean_Elab_Tactic_liftTermElabM___rarg___closed__1;
x_39 = l_unreachable_x21___rarg(x_38);
return x_39;
}
}
}
}
}
lean_object* l_Lean_Elab_Tactic_liftTermElabM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftTermElabM___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_liftMetaM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Term_liftMetaM___rarg___boxed), 4, 2);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
x_6 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_5, x_3, x_4);
return x_6;
}
}
lean_object* l_Lean_Elab_Tactic_liftMetaM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaM___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_getEnv___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Tactic_getEnv(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_getEnv___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_getEnv___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_getEnv(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_getMCtx___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Tactic_getMCtx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_getMCtx___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_getMCtx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_getMCtx(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_getLCtx(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_2);
return x_6;
}
}
lean_object* l_Lean_Elab_Tactic_getLCtx___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Tactic_getLCtx(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Tactic_getLocalInsts(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_4, 2);
lean_inc(x_5);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_2);
return x_6;
}
}
lean_object* l_Lean_Elab_Tactic_getLocalInsts___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Tactic_getLocalInsts(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Tactic_getOptions(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_2);
return x_7;
}
}
lean_object* l_Lean_Elab_Tactic_getOptions___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Tactic_getOptions(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Tactic_getMVarDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Elab_Tactic_getMCtx___rarg(x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = l_Lean_MetavarContext_getDecl(x_6, x_1);
lean_ctor_set(x_4, 0, x_7);
return x_4;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_4);
x_10 = l_Lean_MetavarContext_getDecl(x_8, x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
}
lean_object* l_Lean_Elab_Tactic_getMVarDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Tactic_getMVarDecl(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_Tactic_instantiateMVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Term_instantiateMVars___boxed), 4, 2);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
x_6 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_5, x_3, x_4);
return x_6;
}
}
lean_object* l_Lean_Elab_Tactic_addContext(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_Lean_Elab_Term_addContext___boxed), 3, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_4, x_2, x_3);
return x_5;
}
}
lean_object* l_ReaderT_read___at_Lean_Elab_Tactic_monadLog___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_ReaderT_bind___at_Lean_Elab_Tactic_monadLog___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
x_5 = lean_apply_2(x_1, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_apply_3(x_2, x_6, x_3, x_7);
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_3);
lean_dec(x_2);
x_9 = !lean_is_exclusive(x_5);
if (x_9 == 0)
{
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_5);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
lean_object* l_ReaderT_bind___at_Lean_Elab_Tactic_monadLog___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_monadLog___spec__2___rarg), 4, 0);
return x_3;
}
}
lean_object* l_Lean_Elab_Tactic_monadLog___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_4, 2);
lean_inc(x_5);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
}
lean_object* l_Lean_Elab_Tactic_monadLog___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
}
lean_object* l_Lean_Elab_Tactic_monadLog___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_4, 3);
lean_inc(x_5);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
}
lean_object* l_Lean_Elab_Tactic_monadLog___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_5, 2);
x_8 = l_PersistentArray_push___rarg(x_7, x_1);
lean_ctor_set(x_5, 2, x_8);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = lean_ctor_get(x_5, 1);
x_13 = lean_ctor_get(x_5, 2);
x_14 = lean_ctor_get(x_5, 3);
x_15 = lean_ctor_get(x_5, 4);
x_16 = lean_ctor_get(x_5, 5);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_5);
x_17 = l_PersistentArray_push___rarg(x_13, x_1);
x_18 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_12);
lean_ctor_set(x_18, 2, x_17);
lean_ctor_set(x_18, 3, x_14);
lean_ctor_set(x_18, 4, x_15);
lean_ctor_set(x_18, 5, x_16);
lean_ctor_set(x_3, 0, x_18);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_3);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_21 = lean_ctor_get(x_3, 0);
x_22 = lean_ctor_get(x_3, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_3);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_21, 2);
lean_inc(x_25);
x_26 = lean_ctor_get(x_21, 3);
lean_inc(x_26);
x_27 = lean_ctor_get(x_21, 4);
lean_inc(x_27);
x_28 = lean_ctor_get(x_21, 5);
lean_inc(x_28);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 lean_ctor_release(x_21, 2);
 lean_ctor_release(x_21, 3);
 lean_ctor_release(x_21, 4);
 lean_ctor_release(x_21, 5);
 x_29 = x_21;
} else {
 lean_dec_ref(x_21);
 x_29 = lean_box(0);
}
x_30 = l_PersistentArray_push___rarg(x_25, x_1);
if (lean_is_scalar(x_29)) {
 x_31 = lean_alloc_ctor(0, 6, 0);
} else {
 x_31 = x_29;
}
lean_ctor_set(x_31, 0, x_23);
lean_ctor_set(x_31, 1, x_24);
lean_ctor_set(x_31, 2, x_30);
lean_ctor_set(x_31, 3, x_26);
lean_ctor_set(x_31, 4, x_27);
lean_ctor_set(x_31, 5, x_28);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_22);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
}
lean_object* _init_l_Lean_Elab_Tactic_monadLog___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_ReaderT_read___at_Lean_Elab_Tactic_monadLog___spec__1), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Tactic_monadLog___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_monadLog___lambda__1___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Tactic_monadLog___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_monadLog___closed__1;
x_2 = l_Lean_Elab_Tactic_monadLog___closed__2;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_monadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Tactic_monadLog___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_monadLog___lambda__2___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Tactic_monadLog___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_monadLog___closed__1;
x_2 = l_Lean_Elab_Tactic_monadLog___closed__4;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_monadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Tactic_monadLog___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_monadLog___lambda__3___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Tactic_monadLog___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_monadLog___closed__1;
x_2 = l_Lean_Elab_Tactic_monadLog___closed__6;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_monadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Tactic_monadLog___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_addContext), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Tactic_monadLog___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_monadLog___closed__3;
x_2 = l_Lean_Elab_Tactic_monadLog___closed__5;
x_3 = l_Lean_Elab_Tactic_monadLog___closed__7;
x_4 = l_Lean_Elab_Tactic_monadLog___closed__8;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
lean_object* _init_l_Lean_Elab_Tactic_monadLog___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_monadLog___lambda__4___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Tactic_monadLog___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_monadLog___closed__9;
x_2 = l_Lean_Elab_Tactic_monadLog___closed__10;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Tactic_monadLog() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Tactic_monadLog___closed__11;
return x_1;
}
}
lean_object* l_Lean_Elab_Tactic_monadLog___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Tactic_monadLog___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_Tactic_monadLog___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Tactic_monadLog___lambda__2(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_Tactic_monadLog___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Tactic_monadLog___lambda__3(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_Tactic_monadLog___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Tactic_monadLog___lambda__4(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Elab_Tactic_throwError___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Syntax_getPos(x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_1);
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
x_7 = lean_alloc_closure((void*)(l_Lean_Elab_Term_throwError___rarg___boxed), 4, 2);
lean_closure_set(x_7, 0, x_6);
lean_closure_set(x_7, 1, x_2);
x_8 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_7, x_3, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_Term_throwError___rarg___boxed), 4, 2);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_2);
x_10 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_9, x_3, x_4);
return x_10;
}
}
}
lean_object* l_Lean_Elab_Tactic_throwError(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_throwError___rarg), 4, 0);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Tactic_throwUnsupportedSyntax___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_throwUnsupportedSyntax___boxed), 2, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
lean_object* l_Lean_Elab_Tactic_throwUnsupportedSyntax___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Elab_Tactic_throwUnsupportedSyntax___rarg___closed__1;
x_4 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_3, x_1, x_2);
return x_4;
}
}
lean_object* l_Lean_Elab_Tactic_throwUnsupportedSyntax(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_throwUnsupportedSyntax___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_withIncRecDepth___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_73 = lean_ctor_get(x_3, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
lean_dec(x_73);
x_75 = lean_ctor_get(x_74, 3);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 4);
lean_inc(x_76);
lean_dec(x_74);
x_77 = lean_nat_dec_eq(x_75, x_76);
lean_dec(x_76);
lean_dec(x_75);
if (x_77 == 0)
{
lean_dec(x_1);
x_5 = x_4;
goto block_72;
}
else
{
lean_object* x_78; lean_object* x_79; 
x_78 = l_Lean_Elab_Term_withIncRecDepth___rarg___closed__2;
lean_inc(x_3);
x_79 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_78, x_3, x_4);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; 
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
lean_dec(x_79);
x_5 = x_80;
goto block_72;
}
else
{
uint8_t x_81; 
lean_dec(x_3);
lean_dec(x_2);
x_81 = !lean_is_exclusive(x_79);
if (x_81 == 0)
{
return x_79;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_79, 0);
x_83 = lean_ctor_get(x_79, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_79);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
block_72:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = !lean_is_exclusive(x_3);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_3, 0);
lean_dec(x_9);
x_10 = !lean_is_exclusive(x_6);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_6, 0);
lean_dec(x_11);
x_12 = !lean_is_exclusive(x_7);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_7, 3);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_13, x_14);
lean_dec(x_13);
lean_ctor_set(x_7, 3, x_15);
x_16 = lean_apply_2(x_2, x_3, x_5);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_17 = lean_ctor_get(x_7, 0);
x_18 = lean_ctor_get(x_7, 1);
x_19 = lean_ctor_get(x_7, 2);
x_20 = lean_ctor_get(x_7, 3);
x_21 = lean_ctor_get(x_7, 4);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_7);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_20, x_22);
lean_dec(x_20);
x_24 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_24, 0, x_17);
lean_ctor_set(x_24, 1, x_18);
lean_ctor_set(x_24, 2, x_19);
lean_ctor_set(x_24, 3, x_23);
lean_ctor_set(x_24, 4, x_21);
lean_ctor_set(x_6, 0, x_24);
x_25 = lean_apply_2(x_2, x_3, x_5);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_26 = lean_ctor_get(x_6, 1);
x_27 = lean_ctor_get(x_6, 2);
x_28 = lean_ctor_get(x_6, 3);
x_29 = lean_ctor_get(x_6, 4);
x_30 = lean_ctor_get(x_6, 5);
x_31 = lean_ctor_get(x_6, 6);
x_32 = lean_ctor_get(x_6, 7);
x_33 = lean_ctor_get(x_6, 8);
x_34 = lean_ctor_get(x_6, 9);
x_35 = lean_ctor_get_uint8(x_6, sizeof(void*)*10);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_6);
x_36 = lean_ctor_get(x_7, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_7, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_7, 2);
lean_inc(x_38);
x_39 = lean_ctor_get(x_7, 3);
lean_inc(x_39);
x_40 = lean_ctor_get(x_7, 4);
lean_inc(x_40);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 lean_ctor_release(x_7, 2);
 lean_ctor_release(x_7, 3);
 lean_ctor_release(x_7, 4);
 x_41 = x_7;
} else {
 lean_dec_ref(x_7);
 x_41 = lean_box(0);
}
x_42 = lean_unsigned_to_nat(1u);
x_43 = lean_nat_add(x_39, x_42);
lean_dec(x_39);
if (lean_is_scalar(x_41)) {
 x_44 = lean_alloc_ctor(0, 5, 0);
} else {
 x_44 = x_41;
}
lean_ctor_set(x_44, 0, x_36);
lean_ctor_set(x_44, 1, x_37);
lean_ctor_set(x_44, 2, x_38);
lean_ctor_set(x_44, 3, x_43);
lean_ctor_set(x_44, 4, x_40);
x_45 = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_26);
lean_ctor_set(x_45, 2, x_27);
lean_ctor_set(x_45, 3, x_28);
lean_ctor_set(x_45, 4, x_29);
lean_ctor_set(x_45, 5, x_30);
lean_ctor_set(x_45, 6, x_31);
lean_ctor_set(x_45, 7, x_32);
lean_ctor_set(x_45, 8, x_33);
lean_ctor_set(x_45, 9, x_34);
lean_ctor_set_uint8(x_45, sizeof(void*)*10, x_35);
lean_ctor_set(x_3, 0, x_45);
x_46 = lean_apply_2(x_2, x_3, x_5);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_47 = lean_ctor_get(x_3, 1);
x_48 = lean_ctor_get(x_3, 2);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_3);
x_49 = lean_ctor_get(x_6, 1);
lean_inc(x_49);
x_50 = lean_ctor_get(x_6, 2);
lean_inc(x_50);
x_51 = lean_ctor_get(x_6, 3);
lean_inc(x_51);
x_52 = lean_ctor_get(x_6, 4);
lean_inc(x_52);
x_53 = lean_ctor_get(x_6, 5);
lean_inc(x_53);
x_54 = lean_ctor_get(x_6, 6);
lean_inc(x_54);
x_55 = lean_ctor_get(x_6, 7);
lean_inc(x_55);
x_56 = lean_ctor_get(x_6, 8);
lean_inc(x_56);
x_57 = lean_ctor_get(x_6, 9);
lean_inc(x_57);
x_58 = lean_ctor_get_uint8(x_6, sizeof(void*)*10);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 lean_ctor_release(x_6, 4);
 lean_ctor_release(x_6, 5);
 lean_ctor_release(x_6, 6);
 lean_ctor_release(x_6, 7);
 lean_ctor_release(x_6, 8);
 lean_ctor_release(x_6, 9);
 x_59 = x_6;
} else {
 lean_dec_ref(x_6);
 x_59 = lean_box(0);
}
x_60 = lean_ctor_get(x_7, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_7, 1);
lean_inc(x_61);
x_62 = lean_ctor_get(x_7, 2);
lean_inc(x_62);
x_63 = lean_ctor_get(x_7, 3);
lean_inc(x_63);
x_64 = lean_ctor_get(x_7, 4);
lean_inc(x_64);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 lean_ctor_release(x_7, 2);
 lean_ctor_release(x_7, 3);
 lean_ctor_release(x_7, 4);
 x_65 = x_7;
} else {
 lean_dec_ref(x_7);
 x_65 = lean_box(0);
}
x_66 = lean_unsigned_to_nat(1u);
x_67 = lean_nat_add(x_63, x_66);
lean_dec(x_63);
if (lean_is_scalar(x_65)) {
 x_68 = lean_alloc_ctor(0, 5, 0);
} else {
 x_68 = x_65;
}
lean_ctor_set(x_68, 0, x_60);
lean_ctor_set(x_68, 1, x_61);
lean_ctor_set(x_68, 2, x_62);
lean_ctor_set(x_68, 3, x_67);
lean_ctor_set(x_68, 4, x_64);
if (lean_is_scalar(x_59)) {
 x_69 = lean_alloc_ctor(0, 10, 1);
} else {
 x_69 = x_59;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_49);
lean_ctor_set(x_69, 2, x_50);
lean_ctor_set(x_69, 3, x_51);
lean_ctor_set(x_69, 4, x_52);
lean_ctor_set(x_69, 5, x_53);
lean_ctor_set(x_69, 6, x_54);
lean_ctor_set(x_69, 7, x_55);
lean_ctor_set(x_69, 8, x_56);
lean_ctor_set(x_69, 9, x_57);
lean_ctor_set_uint8(x_69, sizeof(void*)*10, x_58);
x_70 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_47);
lean_ctor_set(x_70, 2, x_48);
x_71 = lean_apply_2(x_2, x_70, x_5);
return x_71;
}
}
}
}
lean_object* l_Lean_Elab_Tactic_withIncRecDepth(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withIncRecDepth___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_getCurrMacroScope(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_3, 9);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
}
lean_object* l_Lean_Elab_Tactic_getCurrMacroScope___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Tactic_getCurrMacroScope(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Tactic_withFreshMacroScope___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_5, 5);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_7, x_8);
lean_ctor_set(x_5, 5, x_9);
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 9);
lean_dec(x_13);
lean_ctor_set(x_11, 9, x_7);
x_14 = lean_apply_2(x_1, x_2, x_3);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = lean_ctor_get(x_11, 1);
x_17 = lean_ctor_get(x_11, 2);
x_18 = lean_ctor_get(x_11, 3);
x_19 = lean_ctor_get(x_11, 4);
x_20 = lean_ctor_get(x_11, 5);
x_21 = lean_ctor_get(x_11, 6);
x_22 = lean_ctor_get(x_11, 7);
x_23 = lean_ctor_get(x_11, 8);
x_24 = lean_ctor_get_uint8(x_11, sizeof(void*)*10);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_11);
x_25 = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(x_25, 0, x_15);
lean_ctor_set(x_25, 1, x_16);
lean_ctor_set(x_25, 2, x_17);
lean_ctor_set(x_25, 3, x_18);
lean_ctor_set(x_25, 4, x_19);
lean_ctor_set(x_25, 5, x_20);
lean_ctor_set(x_25, 6, x_21);
lean_ctor_set(x_25, 7, x_22);
lean_ctor_set(x_25, 8, x_23);
lean_ctor_set(x_25, 9, x_7);
lean_ctor_set_uint8(x_25, sizeof(void*)*10, x_24);
lean_ctor_set(x_2, 0, x_25);
x_26 = lean_apply_2(x_1, x_2, x_3);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_27 = lean_ctor_get(x_2, 0);
x_28 = lean_ctor_get(x_2, 1);
x_29 = lean_ctor_get(x_2, 2);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_2);
x_30 = lean_ctor_get(x_27, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_27, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_27, 2);
lean_inc(x_32);
x_33 = lean_ctor_get(x_27, 3);
lean_inc(x_33);
x_34 = lean_ctor_get(x_27, 4);
lean_inc(x_34);
x_35 = lean_ctor_get(x_27, 5);
lean_inc(x_35);
x_36 = lean_ctor_get(x_27, 6);
lean_inc(x_36);
x_37 = lean_ctor_get(x_27, 7);
lean_inc(x_37);
x_38 = lean_ctor_get(x_27, 8);
lean_inc(x_38);
x_39 = lean_ctor_get_uint8(x_27, sizeof(void*)*10);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 lean_ctor_release(x_27, 2);
 lean_ctor_release(x_27, 3);
 lean_ctor_release(x_27, 4);
 lean_ctor_release(x_27, 5);
 lean_ctor_release(x_27, 6);
 lean_ctor_release(x_27, 7);
 lean_ctor_release(x_27, 8);
 lean_ctor_release(x_27, 9);
 x_40 = x_27;
} else {
 lean_dec_ref(x_27);
 x_40 = lean_box(0);
}
if (lean_is_scalar(x_40)) {
 x_41 = lean_alloc_ctor(0, 10, 1);
} else {
 x_41 = x_40;
}
lean_ctor_set(x_41, 0, x_30);
lean_ctor_set(x_41, 1, x_31);
lean_ctor_set(x_41, 2, x_32);
lean_ctor_set(x_41, 3, x_33);
lean_ctor_set(x_41, 4, x_34);
lean_ctor_set(x_41, 5, x_35);
lean_ctor_set(x_41, 6, x_36);
lean_ctor_set(x_41, 7, x_37);
lean_ctor_set(x_41, 8, x_38);
lean_ctor_set(x_41, 9, x_7);
lean_ctor_set_uint8(x_41, sizeof(void*)*10, x_39);
x_42 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_28);
lean_ctor_set(x_42, 2, x_29);
x_43 = lean_apply_2(x_1, x_42, x_3);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_44 = lean_ctor_get(x_5, 0);
x_45 = lean_ctor_get(x_5, 1);
x_46 = lean_ctor_get(x_5, 2);
x_47 = lean_ctor_get(x_5, 3);
x_48 = lean_ctor_get(x_5, 4);
x_49 = lean_ctor_get(x_5, 5);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_5);
x_50 = lean_unsigned_to_nat(1u);
x_51 = lean_nat_add(x_49, x_50);
x_52 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_52, 0, x_44);
lean_ctor_set(x_52, 1, x_45);
lean_ctor_set(x_52, 2, x_46);
lean_ctor_set(x_52, 3, x_47);
lean_ctor_set(x_52, 4, x_48);
lean_ctor_set(x_52, 5, x_51);
lean_ctor_set(x_3, 0, x_52);
x_53 = lean_ctor_get(x_2, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_2, 1);
lean_inc(x_54);
x_55 = lean_ctor_get(x_2, 2);
lean_inc(x_55);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 x_56 = x_2;
} else {
 lean_dec_ref(x_2);
 x_56 = lean_box(0);
}
x_57 = lean_ctor_get(x_53, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_53, 1);
lean_inc(x_58);
x_59 = lean_ctor_get(x_53, 2);
lean_inc(x_59);
x_60 = lean_ctor_get(x_53, 3);
lean_inc(x_60);
x_61 = lean_ctor_get(x_53, 4);
lean_inc(x_61);
x_62 = lean_ctor_get(x_53, 5);
lean_inc(x_62);
x_63 = lean_ctor_get(x_53, 6);
lean_inc(x_63);
x_64 = lean_ctor_get(x_53, 7);
lean_inc(x_64);
x_65 = lean_ctor_get(x_53, 8);
lean_inc(x_65);
x_66 = lean_ctor_get_uint8(x_53, sizeof(void*)*10);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 lean_ctor_release(x_53, 2);
 lean_ctor_release(x_53, 3);
 lean_ctor_release(x_53, 4);
 lean_ctor_release(x_53, 5);
 lean_ctor_release(x_53, 6);
 lean_ctor_release(x_53, 7);
 lean_ctor_release(x_53, 8);
 lean_ctor_release(x_53, 9);
 x_67 = x_53;
} else {
 lean_dec_ref(x_53);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(0, 10, 1);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_57);
lean_ctor_set(x_68, 1, x_58);
lean_ctor_set(x_68, 2, x_59);
lean_ctor_set(x_68, 3, x_60);
lean_ctor_set(x_68, 4, x_61);
lean_ctor_set(x_68, 5, x_62);
lean_ctor_set(x_68, 6, x_63);
lean_ctor_set(x_68, 7, x_64);
lean_ctor_set(x_68, 8, x_65);
lean_ctor_set(x_68, 9, x_49);
lean_ctor_set_uint8(x_68, sizeof(void*)*10, x_66);
if (lean_is_scalar(x_56)) {
 x_69 = lean_alloc_ctor(0, 3, 0);
} else {
 x_69 = x_56;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_54);
lean_ctor_set(x_69, 2, x_55);
x_70 = lean_apply_2(x_1, x_69, x_3);
return x_70;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_71 = lean_ctor_get(x_3, 0);
x_72 = lean_ctor_get(x_3, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_3);
x_73 = lean_ctor_get(x_71, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_71, 1);
lean_inc(x_74);
x_75 = lean_ctor_get(x_71, 2);
lean_inc(x_75);
x_76 = lean_ctor_get(x_71, 3);
lean_inc(x_76);
x_77 = lean_ctor_get(x_71, 4);
lean_inc(x_77);
x_78 = lean_ctor_get(x_71, 5);
lean_inc(x_78);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 lean_ctor_release(x_71, 2);
 lean_ctor_release(x_71, 3);
 lean_ctor_release(x_71, 4);
 lean_ctor_release(x_71, 5);
 x_79 = x_71;
} else {
 lean_dec_ref(x_71);
 x_79 = lean_box(0);
}
x_80 = lean_unsigned_to_nat(1u);
x_81 = lean_nat_add(x_78, x_80);
if (lean_is_scalar(x_79)) {
 x_82 = lean_alloc_ctor(0, 6, 0);
} else {
 x_82 = x_79;
}
lean_ctor_set(x_82, 0, x_73);
lean_ctor_set(x_82, 1, x_74);
lean_ctor_set(x_82, 2, x_75);
lean_ctor_set(x_82, 3, x_76);
lean_ctor_set(x_82, 4, x_77);
lean_ctor_set(x_82, 5, x_81);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_72);
x_84 = lean_ctor_get(x_2, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_2, 1);
lean_inc(x_85);
x_86 = lean_ctor_get(x_2, 2);
lean_inc(x_86);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 x_87 = x_2;
} else {
 lean_dec_ref(x_2);
 x_87 = lean_box(0);
}
x_88 = lean_ctor_get(x_84, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_84, 1);
lean_inc(x_89);
x_90 = lean_ctor_get(x_84, 2);
lean_inc(x_90);
x_91 = lean_ctor_get(x_84, 3);
lean_inc(x_91);
x_92 = lean_ctor_get(x_84, 4);
lean_inc(x_92);
x_93 = lean_ctor_get(x_84, 5);
lean_inc(x_93);
x_94 = lean_ctor_get(x_84, 6);
lean_inc(x_94);
x_95 = lean_ctor_get(x_84, 7);
lean_inc(x_95);
x_96 = lean_ctor_get(x_84, 8);
lean_inc(x_96);
x_97 = lean_ctor_get_uint8(x_84, sizeof(void*)*10);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 lean_ctor_release(x_84, 2);
 lean_ctor_release(x_84, 3);
 lean_ctor_release(x_84, 4);
 lean_ctor_release(x_84, 5);
 lean_ctor_release(x_84, 6);
 lean_ctor_release(x_84, 7);
 lean_ctor_release(x_84, 8);
 lean_ctor_release(x_84, 9);
 x_98 = x_84;
} else {
 lean_dec_ref(x_84);
 x_98 = lean_box(0);
}
if (lean_is_scalar(x_98)) {
 x_99 = lean_alloc_ctor(0, 10, 1);
} else {
 x_99 = x_98;
}
lean_ctor_set(x_99, 0, x_88);
lean_ctor_set(x_99, 1, x_89);
lean_ctor_set(x_99, 2, x_90);
lean_ctor_set(x_99, 3, x_91);
lean_ctor_set(x_99, 4, x_92);
lean_ctor_set(x_99, 5, x_93);
lean_ctor_set(x_99, 6, x_94);
lean_ctor_set(x_99, 7, x_95);
lean_ctor_set(x_99, 8, x_96);
lean_ctor_set(x_99, 9, x_78);
lean_ctor_set_uint8(x_99, sizeof(void*)*10, x_97);
if (lean_is_scalar(x_87)) {
 x_100 = lean_alloc_ctor(0, 3, 0);
} else {
 x_100 = x_87;
}
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_85);
lean_ctor_set(x_100, 2, x_86);
x_101 = lean_apply_2(x_1, x_100, x_83);
return x_101;
}
}
}
lean_object* l_Lean_Elab_Tactic_withFreshMacroScope(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withFreshMacroScope___rarg), 3, 0);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Tactic_monadQuotation___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_getCurrMacroScope___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Tactic_monadQuotation___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withFreshMacroScope), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Tactic_monadQuotation___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_monadQuotation___closed__1;
x_2 = l_Lean_Elab_Tactic_monadQuotation___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Tactic_monadQuotation() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Tactic_monadQuotation___closed__3;
return x_1;
}
}
lean_object* l_mkHashMap___at_Lean_Elab_Tactic_mkBuiltinTacticTable___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_PersistentHashMap_empty___at_Lean_Elab_Tactic_mkBuiltinTacticTable___spec__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_LocalContext_Inhabited___closed__1;
return x_1;
}
}
lean_object* _init_l_Lean_SMap_empty___at_Lean_Elab_Tactic_mkBuiltinTacticTable___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_SMap_empty___at_Lean_Elab_Tactic_mkBuiltinTacticTable___spec__1___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = l_Lean_SMap_empty___at_Lean_Elab_Tactic_mkBuiltinTacticTable___spec__1___closed__1;
x_3 = l_PersistentHashMap_empty___at_Lean_Elab_Tactic_mkBuiltinTacticTable___spec__3;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
lean_object* _init_l_Lean_SMap_empty___at_Lean_Elab_Tactic_mkBuiltinTacticTable___spec__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_SMap_empty___at_Lean_Elab_Tactic_mkBuiltinTacticTable___spec__1___closed__2;
return x_1;
}
}
lean_object* l_Lean_Elab_Tactic_mkBuiltinTacticTable(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_SMap_empty___at_Lean_Elab_Tactic_mkBuiltinTacticTable___spec__1;
x_3 = lean_io_mk_ref(x_2, x_1);
return x_3;
}
}
uint8_t l_AssocList_contains___main___at_Lean_Elab_Tactic_addBuiltinTactic___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_name_eq(x_4, x_1);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
}
}
uint8_t l_HashMapImp_contains___at_Lean_Elab_Tactic_addBuiltinTactic___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Name_hash(x_2);
x_6 = lean_usize_modn(x_5, x_4);
lean_dec(x_4);
x_7 = lean_array_uget(x_3, x_6);
x_8 = l_AssocList_contains___main___at_Lean_Elab_Tactic_addBuiltinTactic___spec__3(x_2, x_7);
lean_dec(x_7);
return x_8;
}
}
uint8_t l_PersistentHashMap_containsAux___main___at_Lean_Elab_Tactic_addBuiltinTactic___spec__5(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = 5;
x_6 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_7 = x_2 & x_6;
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_box(2);
x_10 = lean_array_get(x_9, x_4, x_8);
lean_dec(x_8);
lean_dec(x_4);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_name_eq(x_3, x_11);
lean_dec(x_11);
return x_12;
}
case 1:
{
lean_object* x_13; size_t x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
x_14 = x_2 >> x_5;
x_1 = x_13;
x_2 = x_14;
goto _start;
}
default: 
{
uint8_t x_16; 
x_16 = 0;
return x_16;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec(x_1);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_PersistentHashMap_containsAtAux___main___at_Lean_Parser_mkFreshKindAux___main___spec__3(x_17, x_18, x_3);
lean_dec(x_17);
return x_19;
}
}
}
uint8_t l_PersistentHashMap_contains___at_Lean_Elab_Tactic_addBuiltinTactic___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Name_hash(x_2);
x_5 = l_PersistentHashMap_containsAux___main___at_Lean_Elab_Tactic_addBuiltinTactic___spec__5(x_3, x_4, x_2);
return x_5;
}
}
uint8_t l_Lean_SMap_contains___at_Lean_Elab_Tactic_addBuiltinTactic___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_HashMapImp_contains___at_Lean_Elab_Tactic_addBuiltinTactic___spec__2(x_4, x_2);
lean_dec(x_4);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = l_PersistentHashMap_contains___at_Lean_Elab_Tactic_addBuiltinTactic___spec__4(x_5, x_2);
return x_7;
}
else
{
uint8_t x_8; 
lean_dec(x_5);
x_8 = 1;
return x_8;
}
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = l_HashMapImp_contains___at_Lean_Elab_Tactic_addBuiltinTactic___spec__2(x_9, x_2);
lean_dec(x_9);
return x_10;
}
}
}
lean_object* _init_l_Lean_Elab_Tactic_addBuiltinTactic___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid builtin tactic elaborator, elaborator for '");
return x_1;
}
}
lean_object* l_Lean_Elab_Tactic_addBuiltinTactic(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Elab_Tactic_builtinTacticTable;
x_6 = lean_io_ref_get(x_5, x_4);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = l_Lean_SMap_contains___at_Lean_Elab_Tactic_addBuiltinTactic___spec__1(x_8, x_1);
if (x_10 == 0)
{
lean_object* x_11; 
lean_free_object(x_6);
x_11 = lean_io_ref_get(x_5, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_io_ref_reset(x_5, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Lean_Elab_ElabFnTable_insert___rarg(x_12, x_1, x_3);
x_17 = lean_io_ref_set(x_5, x_16, x_15);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_14, 0);
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_14);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
else
{
uint8_t x_22; 
lean_dec(x_3);
lean_dec(x_1);
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
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_3);
x_26 = l_Lean_Name_toString___closed__1;
x_27 = l_Lean_Name_toStringWithSep___main(x_26, x_1);
x_28 = l_Lean_Elab_Tactic_addBuiltinTactic___closed__1;
x_29 = lean_string_append(x_28, x_27);
lean_dec(x_27);
x_30 = l___private_Init_Lean_Parser_Parser_8__throwParserCategoryAlreadyDefined___rarg___closed__2;
x_31 = lean_string_append(x_29, x_30);
x_32 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_32);
return x_6;
}
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = lean_ctor_get(x_6, 0);
x_34 = lean_ctor_get(x_6, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_6);
x_35 = l_Lean_SMap_contains___at_Lean_Elab_Tactic_addBuiltinTactic___spec__1(x_33, x_1);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = lean_io_ref_get(x_5, x_34);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_io_ref_reset(x_5, x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
x_41 = l_Lean_Elab_ElabFnTable_insert___rarg(x_37, x_1, x_3);
x_42 = lean_io_ref_set(x_5, x_41, x_40);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_37);
lean_dec(x_3);
lean_dec(x_1);
x_43 = lean_ctor_get(x_39, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_39, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_45 = x_39;
} else {
 lean_dec_ref(x_39);
 x_45 = lean_box(0);
}
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(1, 2, 0);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_3);
lean_dec(x_1);
x_47 = lean_ctor_get(x_36, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_36, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_49 = x_36;
} else {
 lean_dec_ref(x_36);
 x_49 = lean_box(0);
}
if (lean_is_scalar(x_49)) {
 x_50 = lean_alloc_ctor(1, 2, 0);
} else {
 x_50 = x_49;
}
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_3);
x_51 = l_Lean_Name_toString___closed__1;
x_52 = l_Lean_Name_toStringWithSep___main(x_51, x_1);
x_53 = l_Lean_Elab_Tactic_addBuiltinTactic___closed__1;
x_54 = lean_string_append(x_53, x_52);
lean_dec(x_52);
x_55 = l___private_Init_Lean_Parser_Parser_8__throwParserCategoryAlreadyDefined___rarg___closed__2;
x_56 = lean_string_append(x_54, x_55);
x_57 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_57, 0, x_56);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_34);
return x_58;
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_3);
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_6);
if (x_59 == 0)
{
return x_6;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_6, 0);
x_61 = lean_ctor_get(x_6, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_6);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
}
lean_object* l_AssocList_contains___main___at_Lean_Elab_Tactic_addBuiltinTactic___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_AssocList_contains___main___at_Lean_Elab_Tactic_addBuiltinTactic___spec__3(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_HashMapImp_contains___at_Lean_Elab_Tactic_addBuiltinTactic___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_HashMapImp_contains___at_Lean_Elab_Tactic_addBuiltinTactic___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_PersistentHashMap_containsAux___main___at_Lean_Elab_Tactic_addBuiltinTactic___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_PersistentHashMap_containsAux___main___at_Lean_Elab_Tactic_addBuiltinTactic___spec__5(x_1, x_4, x_3);
lean_dec(x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_PersistentHashMap_contains___at_Lean_Elab_Tactic_addBuiltinTactic___spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_PersistentHashMap_contains___at_Lean_Elab_Tactic_addBuiltinTactic___spec__4(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_SMap_contains___at_Lean_Elab_Tactic_addBuiltinTactic___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_SMap_contains___at_Lean_Elab_Tactic_addBuiltinTactic___spec__1(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_Elab_Tactic_addBuiltinTactic___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Tactic_addBuiltinTactic(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* _init_l_Lean_Elab_Tactic_declareBuiltinTactic___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_regBuiltinTactic");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Tactic_declareBuiltinTactic___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_declareBuiltinTactic___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Tactic_declareBuiltinTactic___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_declareBuiltinTermElab___closed__3;
x_2 = l___private_Init_Lean_Meta_Tactic_Util_1__regTraceClasses___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Tactic_declareBuiltinTactic___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("addBuiltinTactic");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Tactic_declareBuiltinTactic___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_declareBuiltinTactic___closed__3;
x_2 = l_Lean_Elab_Tactic_declareBuiltinTactic___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Tactic_declareBuiltinTactic___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_declareBuiltinTactic___closed__5;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Tactic_declareBuiltinTactic___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to emit registration code for builtin tactic elaborator '");
return x_1;
}
}
lean_object* l_Lean_Elab_Tactic_declareBuiltinTactic(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_5 = l_Lean_Elab_Tactic_declareBuiltinTactic___closed__2;
lean_inc(x_3);
x_6 = l_Lean_Name_append___main(x_5, x_3);
x_7 = lean_box(0);
x_8 = l_Lean_nameToExprAux___main(x_2);
lean_inc(x_3);
x_9 = l_Lean_nameToExprAux___main(x_3);
lean_inc(x_3);
x_10 = l_Lean_mkConst(x_3, x_7);
x_11 = l_Lean_Parser_declareBuiltinParser___closed__8;
x_12 = lean_array_push(x_11, x_8);
x_13 = lean_array_push(x_12, x_9);
x_14 = lean_array_push(x_13, x_10);
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Lean_Elab_Tactic_declareBuiltinTactic___closed__6;
x_17 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_14, x_14, x_15, x_16);
lean_dec(x_14);
x_18 = l_Lean_Parser_declareBuiltinParser___closed__7;
lean_inc(x_6);
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_6);
lean_ctor_set(x_19, 1, x_7);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_box(0);
x_21 = 0;
x_22 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_17);
lean_ctor_set(x_22, 2, x_20);
lean_ctor_set_uint8(x_22, sizeof(void*)*3, x_21);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = l_Lean_Options_empty;
x_25 = l_Lean_Environment_addAndCompile(x_1, x_24, x_23);
lean_dec(x_23);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_25);
lean_dec(x_6);
x_26 = l_Lean_Name_toString___closed__1;
x_27 = l_Lean_Name_toStringWithSep___main(x_26, x_3);
x_28 = l_Lean_Elab_Tactic_declareBuiltinTactic___closed__7;
x_29 = lean_string_append(x_28, x_27);
lean_dec(x_27);
x_30 = l_Char_HasRepr___closed__1;
x_31 = lean_string_append(x_29, x_30);
x_32 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_4);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_3);
x_34 = lean_ctor_get(x_25, 0);
lean_inc(x_34);
lean_dec(x_25);
x_35 = l_Lean_initAttr;
x_36 = lean_box(0);
x_37 = l_Lean_ParametricAttribute_setParam___rarg(x_35, x_34, x_6, x_36);
x_38 = l_IO_ofExcept___at_Lean_registerClassAttr___spec__1(x_37, x_4);
lean_dec(x_37);
return x_38;
}
}
}
lean_object* _init_l_Lean_Elab_Tactic_registerBuiltinTacticAttr___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid attribute 'builtinTactic', must be persistent");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Tactic_registerBuiltinTacticAttr___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_registerBuiltinTacticAttr___lambda__1___closed__1;
x_2 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Tactic_registerBuiltinTacticAttr___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_declareLeadingBuiltinParser___closed__1;
x_2 = l___private_Init_Lean_Meta_Tactic_Util_1__regTraceClasses___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Tactic_registerBuiltinTacticAttr___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected tactic elaborator type at '");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Tactic_registerBuiltinTacticAttr___lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' `Tactic` expected");
return x_1;
}
}
lean_object* l_Lean_Elab_Tactic_registerBuiltinTacticAttr___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5) {
_start:
{
if (x_4 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = l_Lean_Elab_Tactic_registerBuiltinTacticAttr___lambda__1___closed__2;
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lean_Elab_Tactic_registerBuiltinTacticAttr___lambda__1___closed__3;
lean_inc(x_1);
x_9 = l_Lean_Elab_syntaxNodeKindOfAttrParam(x_1, x_8, x_3);
x_10 = l_IO_ofExcept___at___private_Init_Lean_Elab_Util_6__ElabAttribute_add___spec__1(x_9, x_5);
lean_dec(x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_24; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_13 = x_10;
} else {
 lean_dec_ref(x_10);
 x_13 = lean_box(0);
}
lean_inc(x_2);
lean_inc(x_1);
x_24 = lean_environment_find(x_1, x_2);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_2);
lean_dec(x_1);
x_25 = l___private_Init_Lean_Parser_Parser_18__BuiltinParserAttribute_add___closed__2;
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_12);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 0);
lean_inc(x_27);
lean_dec(x_24);
x_28 = l_Lean_ConstantInfo_type(x_27);
lean_dec(x_27);
if (lean_obj_tag(x_28) == 4)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec(x_28);
if (lean_obj_tag(x_29) == 1)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 1)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 1)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 1)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_34 = lean_ctor_get(x_29, 1);
lean_inc(x_34);
lean_dec(x_29);
x_35 = lean_ctor_get(x_30, 1);
lean_inc(x_35);
lean_dec(x_30);
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
lean_dec(x_31);
x_37 = lean_ctor_get(x_32, 1);
lean_inc(x_37);
lean_dec(x_32);
x_38 = l_Lean_nameToExprAux___main___closed__1;
x_39 = lean_string_dec_eq(x_37, x_38);
lean_dec(x_37);
if (x_39 == 0)
{
lean_object* x_40; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_11);
lean_dec(x_1);
x_40 = lean_box(0);
x_14 = x_40;
goto block_23;
}
else
{
lean_object* x_41; uint8_t x_42; 
x_41 = l___private_Init_Lean_Elab_Util_8__regTraceClasses___closed__1;
x_42 = lean_string_dec_eq(x_36, x_41);
lean_dec(x_36);
if (x_42 == 0)
{
lean_object* x_43; 
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_11);
lean_dec(x_1);
x_43 = lean_box(0);
x_14 = x_43;
goto block_23;
}
else
{
lean_object* x_44; uint8_t x_45; 
x_44 = l___private_Init_Lean_Meta_Tactic_Util_1__regTraceClasses___closed__1;
x_45 = lean_string_dec_eq(x_35, x_44);
lean_dec(x_35);
if (x_45 == 0)
{
lean_object* x_46; 
lean_dec(x_34);
lean_dec(x_11);
lean_dec(x_1);
x_46 = lean_box(0);
x_14 = x_46;
goto block_23;
}
else
{
uint8_t x_47; 
x_47 = lean_string_dec_eq(x_34, x_44);
lean_dec(x_34);
if (x_47 == 0)
{
lean_object* x_48; 
lean_dec(x_11);
lean_dec(x_1);
x_48 = lean_box(0);
x_14 = x_48;
goto block_23;
}
else
{
lean_object* x_49; 
lean_dec(x_13);
x_49 = l_Lean_Elab_Tactic_declareBuiltinTactic(x_1, x_11, x_2, x_12);
return x_49;
}
}
}
}
}
else
{
lean_object* x_50; 
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_11);
lean_dec(x_1);
x_50 = lean_box(0);
x_14 = x_50;
goto block_23;
}
}
else
{
lean_object* x_51; 
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_11);
lean_dec(x_1);
x_51 = lean_box(0);
x_14 = x_51;
goto block_23;
}
}
else
{
lean_object* x_52; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_11);
lean_dec(x_1);
x_52 = lean_box(0);
x_14 = x_52;
goto block_23;
}
}
else
{
lean_object* x_53; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_11);
lean_dec(x_1);
x_53 = lean_box(0);
x_14 = x_53;
goto block_23;
}
}
else
{
lean_object* x_54; 
lean_dec(x_29);
lean_dec(x_11);
lean_dec(x_1);
x_54 = lean_box(0);
x_14 = x_54;
goto block_23;
}
}
else
{
lean_object* x_55; 
lean_dec(x_28);
lean_dec(x_11);
lean_dec(x_1);
x_55 = lean_box(0);
x_14 = x_55;
goto block_23;
}
}
block_23:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_14);
x_15 = l_Lean_Name_toString___closed__1;
x_16 = l_Lean_Name_toStringWithSep___main(x_15, x_2);
x_17 = l_Lean_Elab_Tactic_registerBuiltinTacticAttr___lambda__1___closed__4;
x_18 = lean_string_append(x_17, x_16);
lean_dec(x_16);
x_19 = l_Lean_Elab_Tactic_registerBuiltinTacticAttr___lambda__1___closed__5;
x_20 = lean_string_append(x_18, x_19);
x_21 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_21, 0, x_20);
if (lean_is_scalar(x_13)) {
 x_22 = lean_alloc_ctor(1, 2, 0);
} else {
 x_22 = x_13;
 lean_ctor_set_tag(x_22, 1);
}
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_12);
return x_22;
}
}
else
{
uint8_t x_56; 
lean_dec(x_2);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_10);
if (x_56 == 0)
{
return x_10;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_10, 0);
x_58 = lean_ctor_get(x_10, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_10);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
}
}
lean_object* _init_l_Lean_Elab_Tactic_registerBuiltinTacticAttr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("builtinTactic");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Tactic_registerBuiltinTacticAttr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Tactic_registerBuiltinTacticAttr___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Tactic_registerBuiltinTacticAttr___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Builtin tactic elaborator");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Tactic_registerBuiltinTacticAttr___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_registerBuiltinTacticAttr___lambda__1___boxed), 5, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Tactic_registerBuiltinTacticAttr___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_registerBuiltinTacticAttr___closed__2;
x_2 = l_Lean_Elab_Tactic_registerBuiltinTacticAttr___closed__3;
x_3 = l_Lean_Elab_Tactic_registerBuiltinTacticAttr___closed__4;
x_4 = 1;
x_5 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*3, x_4);
return x_5;
}
}
lean_object* l_Lean_Elab_Tactic_registerBuiltinTacticAttr(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Tactic_registerBuiltinTacticAttr___closed__5;
x_3 = l_Lean_registerBuiltinAttribute(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Tactic_registerBuiltinTacticAttr___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_4);
lean_dec(x_4);
x_7 = l_Lean_Elab_Tactic_registerBuiltinTacticAttr___lambda__1(x_1, x_2, x_3, x_6, x_5);
lean_dec(x_3);
return x_7;
}
}
lean_object* _init_l_Lean_Elab_Tactic_mkTacticAttribute___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_declareBuiltinTactic___closed__3;
x_2 = l___private_Init_Lean_Meta_Tactic_Util_1__regTraceClasses___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Tactic_mkTacticAttribute(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = l_Lean_Parser_regBuiltinTacticParserAttr___closed__4;
x_3 = l_Lean_Elab_Tactic_registerBuiltinTacticAttr___lambda__1___closed__3;
x_4 = l_Lean_Elab_Tactic_mkTacticAttribute___closed__1;
x_5 = l_Lean_Parser_regBuiltinTacticParserAttr___closed__3;
x_6 = l_Lean_Elab_Tactic_builtinTacticTable;
x_7 = l_Lean_Elab_mkElabAttribute___rarg(x_2, x_3, x_4, x_5, x_6, x_1);
return x_7;
}
}
lean_object* _init_l_Lean_Elab_Tactic_tacticElabAttribute___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_SMap_empty___at_Lean_Elab_Tactic_mkBuiltinTacticTable___spec__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Tactic_tacticElabAttribute___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Tactic_tacticElabAttribute___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_EnvExtension_Inhabited___rarg___closed__1;
x_3 = l_Lean_Elab_Tactic_tacticElabAttribute___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Elab_Tactic_tacticElabAttribute___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_Lean_Elab_Tactic_tacticElabAttribute___closed__3;
x_2 = lean_box(0);
x_3 = l_Lean_PersistentEnvExtension_inhabited___rarg___closed__1;
x_4 = l_Lean_Elab_Term_termElabAttribute___closed__4;
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
lean_object* _init_l_Lean_Elab_Tactic_tacticElabAttribute___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_AttributeImpl_inhabited___closed__2;
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute___closed__4;
x_3 = l_String_splitAux___main___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* l_Lean_Elab_Tactic_logTrace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_Lean_Elab_Term_logTrace___boxed), 5, 3);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_2);
lean_closure_set(x_6, 2, x_3);
x_7 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_6, x_4, x_5);
return x_7;
}
}
lean_object* l_Lean_Elab_Tactic_trace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_Lean_Elab_Term_trace___boxed), 5, 3);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_2);
lean_closure_set(x_6, 2, x_3);
x_7 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_6, x_4, x_5);
return x_7;
}
}
lean_object* l_Lean_Elab_Tactic_traceAtCmdPos(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Term_traceAtCmdPos___boxed), 4, 2);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
x_6 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_5, x_3, x_4);
return x_6;
}
}
lean_object* l_Lean_Elab_Tactic_dbgTrace___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_apply_1(x_1, x_2);
x_6 = l_Lean_Meta_dbgTrace___rarg___closed__1;
x_7 = lean_dbg_trace(x_5, x_6);
x_8 = lean_apply_2(x_7, x_3, x_4);
return x_8;
}
}
lean_object* l_Lean_Elab_Tactic_dbgTrace(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_dbgTrace___rarg), 4, 0);
return x_2;
}
}
lean_object* l___private_Init_Lean_Elab_Tactic_Basic_1__evalTacticUsing___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_1);
lean_inc(x_2);
x_6 = l_Lean_Syntax_prettyPrint(x_2);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = l_Lean_MessageData_ofList___closed__3;
x_9 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
x_10 = lean_unsigned_to_nat(2u);
x_11 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = l___private_Init_Lean_Elab_Term_9__elabTermUsing___main___closed__3;
x_13 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l_Lean_Elab_Tactic_throwError___rarg(x_2, x_13, x_4, x_5);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_3, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_3, 1);
lean_inc(x_16);
lean_dec(x_3);
lean_inc(x_4);
lean_inc(x_2);
x_17 = lean_apply_3(x_15, x_2, x_4, x_5);
if (lean_obj_tag(x_17) == 0)
{
lean_dec(x_16);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_17;
}
else
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
lean_dec(x_16);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_17, 0);
lean_dec(x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_18);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
lean_dec(x_17);
lean_inc(x_1);
{
lean_object* _tmp_2 = x_16;
lean_object* _tmp_4 = x_1;
x_3 = _tmp_2;
x_5 = _tmp_4;
}
goto _start;
}
}
}
}
}
lean_object* l___private_Init_Lean_Elab_Tactic_Basic_1__evalTacticUsing(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Lean_Elab_Tactic_Basic_1__evalTacticUsing___main(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_Elab_Tactic_withMacroExpansion___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_6, 8);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_6, 8, x_9);
x_10 = lean_apply_2(x_2, x_3, x_4);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_11 = lean_ctor_get(x_6, 0);
x_12 = lean_ctor_get(x_6, 1);
x_13 = lean_ctor_get(x_6, 2);
x_14 = lean_ctor_get(x_6, 3);
x_15 = lean_ctor_get(x_6, 4);
x_16 = lean_ctor_get(x_6, 5);
x_17 = lean_ctor_get(x_6, 6);
x_18 = lean_ctor_get(x_6, 7);
x_19 = lean_ctor_get(x_6, 8);
x_20 = lean_ctor_get(x_6, 9);
x_21 = lean_ctor_get_uint8(x_6, sizeof(void*)*10);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_6);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_19);
x_23 = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(x_23, 0, x_11);
lean_ctor_set(x_23, 1, x_12);
lean_ctor_set(x_23, 2, x_13);
lean_ctor_set(x_23, 3, x_14);
lean_ctor_set(x_23, 4, x_15);
lean_ctor_set(x_23, 5, x_16);
lean_ctor_set(x_23, 6, x_17);
lean_ctor_set(x_23, 7, x_18);
lean_ctor_set(x_23, 8, x_22);
lean_ctor_set(x_23, 9, x_20);
lean_ctor_set_uint8(x_23, sizeof(void*)*10, x_21);
lean_ctor_set(x_3, 0, x_23);
x_24 = lean_apply_2(x_2, x_3, x_4);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_25 = lean_ctor_get(x_3, 0);
x_26 = lean_ctor_get(x_3, 1);
x_27 = lean_ctor_get(x_3, 2);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_3);
x_28 = lean_ctor_get(x_25, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_25, 2);
lean_inc(x_30);
x_31 = lean_ctor_get(x_25, 3);
lean_inc(x_31);
x_32 = lean_ctor_get(x_25, 4);
lean_inc(x_32);
x_33 = lean_ctor_get(x_25, 5);
lean_inc(x_33);
x_34 = lean_ctor_get(x_25, 6);
lean_inc(x_34);
x_35 = lean_ctor_get(x_25, 7);
lean_inc(x_35);
x_36 = lean_ctor_get(x_25, 8);
lean_inc(x_36);
x_37 = lean_ctor_get(x_25, 9);
lean_inc(x_37);
x_38 = lean_ctor_get_uint8(x_25, sizeof(void*)*10);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 lean_ctor_release(x_25, 2);
 lean_ctor_release(x_25, 3);
 lean_ctor_release(x_25, 4);
 lean_ctor_release(x_25, 5);
 lean_ctor_release(x_25, 6);
 lean_ctor_release(x_25, 7);
 lean_ctor_release(x_25, 8);
 lean_ctor_release(x_25, 9);
 x_39 = x_25;
} else {
 lean_dec_ref(x_25);
 x_39 = lean_box(0);
}
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_1);
lean_ctor_set(x_40, 1, x_36);
if (lean_is_scalar(x_39)) {
 x_41 = lean_alloc_ctor(0, 10, 1);
} else {
 x_41 = x_39;
}
lean_ctor_set(x_41, 0, x_28);
lean_ctor_set(x_41, 1, x_29);
lean_ctor_set(x_41, 2, x_30);
lean_ctor_set(x_41, 3, x_31);
lean_ctor_set(x_41, 4, x_32);
lean_ctor_set(x_41, 5, x_33);
lean_ctor_set(x_41, 6, x_34);
lean_ctor_set(x_41, 7, x_35);
lean_ctor_set(x_41, 8, x_40);
lean_ctor_set(x_41, 9, x_37);
lean_ctor_set_uint8(x_41, sizeof(void*)*10, x_38);
x_42 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_26);
lean_ctor_set(x_42, 2, x_27);
x_43 = lean_apply_2(x_2, x_42, x_4);
return x_43;
}
}
}
lean_object* l_Lean_Elab_Tactic_withMacroExpansion(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withMacroExpansion___rarg), 4, 0);
return x_2;
}
}
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_Elab_Tactic_evalTactic___main___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_fget(x_1, x_4);
x_10 = lean_name_eq(x_5, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
x_3 = lean_box(0);
x_4 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_fget(x_2, x_4);
lean_dec(x_4);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
}
lean_object* l_PersistentHashMap_findAux___main___at_Lean_Elab_Tactic_evalTactic___main___spec__3(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = 5;
x_6 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_7 = x_2 & x_6;
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_box(2);
x_10 = lean_array_get(x_9, x_4, x_8);
lean_dec(x_8);
lean_dec(x_4);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_name_eq(x_3, x_11);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_12);
x_14 = lean_box(0);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_12);
return x_15;
}
}
case 1:
{
lean_object* x_16; size_t x_17; 
x_16 = lean_ctor_get(x_10, 0);
lean_inc(x_16);
lean_dec(x_10);
x_17 = x_2 >> x_5;
x_1 = x_16;
x_2 = x_17;
goto _start;
}
default: 
{
lean_object* x_19; 
x_19 = lean_box(0);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_PersistentHashMap_findAtAux___main___at_Lean_Elab_Tactic_evalTactic___main___spec__4(x_20, x_21, lean_box(0), x_22, x_3);
lean_dec(x_21);
lean_dec(x_20);
return x_23;
}
}
}
lean_object* l_PersistentHashMap_find_x3f___at_Lean_Elab_Tactic_evalTactic___main___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Name_hash(x_2);
x_5 = l_PersistentHashMap_findAux___main___at_Lean_Elab_Tactic_evalTactic___main___spec__3(x_3, x_4, x_2);
return x_5;
}
}
lean_object* l_AssocList_find___main___at_Lean_Elab_Tactic_evalTactic___main___spec__6(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_name_eq(x_4, x_1);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_9; 
lean_inc(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
}
}
}
lean_object* l_HashMapImp_find_x3f___at_Lean_Elab_Tactic_evalTactic___main___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Name_hash(x_2);
x_6 = lean_usize_modn(x_5, x_4);
lean_dec(x_4);
x_7 = lean_array_uget(x_3, x_6);
x_8 = l_AssocList_find___main___at_Lean_Elab_Tactic_evalTactic___main___spec__6(x_2, x_7);
lean_dec(x_7);
return x_8;
}
}
lean_object* l_Lean_SMap_find_x3f___at_Lean_Elab_Tactic_evalTactic___main___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_PersistentHashMap_find_x3f___at_Lean_Elab_Tactic_evalTactic___main___spec__2(x_5, x_2);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = l_HashMapImp_find_x3f___at_Lean_Elab_Tactic_evalTactic___main___spec__5(x_4, x_2);
lean_dec(x_4);
return x_7;
}
else
{
lean_dec(x_4);
return x_6;
}
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = l_HashMapImp_find_x3f___at_Lean_Elab_Tactic_evalTactic___main___spec__5(x_8, x_2);
lean_dec(x_8);
return x_9;
}
}
}
lean_object* l_Lean_Elab_Tactic_evalTactic___main___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Tactic_evalTactic___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected command");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Tactic_evalTactic___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalTactic___main___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Tactic_evalTactic___main___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalTactic___main___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Tactic_evalTactic___main___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Lean_Elab_Util_8__regTraceClasses___closed__2;
x_2 = l_Lean_Meta_isLevelDefEqAux___main___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Tactic_evalTactic___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; uint8_t x_404; 
x_400 = lean_ctor_get(x_2, 0);
lean_inc(x_400);
x_401 = lean_ctor_get(x_400, 0);
lean_inc(x_401);
lean_dec(x_400);
x_402 = lean_ctor_get(x_401, 3);
lean_inc(x_402);
x_403 = lean_ctor_get(x_401, 4);
lean_inc(x_403);
lean_dec(x_401);
x_404 = lean_nat_dec_eq(x_402, x_403);
lean_dec(x_403);
lean_dec(x_402);
if (x_404 == 0)
{
x_4 = x_3;
goto block_399;
}
else
{
lean_object* x_405; lean_object* x_406; 
x_405 = l_Lean_Elab_Term_withIncRecDepth___rarg___closed__2;
lean_inc(x_2);
lean_inc(x_1);
x_406 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_405, x_2, x_3);
if (lean_obj_tag(x_406) == 0)
{
lean_object* x_407; 
x_407 = lean_ctor_get(x_406, 1);
lean_inc(x_407);
lean_dec(x_406);
x_4 = x_407;
goto block_399;
}
else
{
uint8_t x_408; 
lean_dec(x_2);
lean_dec(x_1);
x_408 = !lean_is_exclusive(x_406);
if (x_408 == 0)
{
return x_406;
}
else
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; 
x_409 = lean_ctor_get(x_406, 0);
x_410 = lean_ctor_get(x_406, 1);
lean_inc(x_410);
lean_inc(x_409);
lean_dec(x_406);
x_411 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_411, 0, x_409);
lean_ctor_set(x_411, 1, x_410);
return x_411;
}
}
}
block_399:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = !lean_is_exclusive(x_2);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_ctor_get(x_2, 2);
x_10 = lean_ctor_get(x_2, 0);
lean_dec(x_10);
x_11 = !lean_is_exclusive(x_5);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_12 = lean_ctor_get(x_5, 1);
x_13 = lean_ctor_get(x_5, 2);
x_14 = lean_ctor_get(x_5, 3);
x_15 = lean_ctor_get(x_5, 4);
x_16 = lean_ctor_get(x_5, 5);
x_17 = lean_ctor_get(x_5, 6);
x_18 = lean_ctor_get(x_5, 7);
x_19 = lean_ctor_get(x_5, 8);
x_20 = lean_ctor_get_uint8(x_5, sizeof(void*)*10);
x_21 = lean_ctor_get(x_5, 9);
lean_dec(x_21);
x_22 = lean_ctor_get(x_5, 0);
lean_dec(x_22);
x_23 = !lean_is_exclusive(x_6);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_6, 3);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_24, x_25);
lean_dec(x_24);
lean_ctor_set(x_6, 3, x_26);
x_27 = !lean_is_exclusive(x_4);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_4, 0);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_28, 5);
x_31 = lean_nat_add(x_30, x_25);
lean_ctor_set(x_28, 5, x_31);
lean_inc(x_30);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_6);
lean_ctor_set(x_5, 9, x_30);
lean_inc(x_9);
lean_inc(x_8);
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_inc(x_1);
x_32 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___main___lambda__1___boxed), 2, 1);
lean_closure_set(x_32, 0, x_1);
x_33 = l_Lean_Elab_Tactic_evalTactic___main___closed__4;
lean_inc(x_1);
x_34 = lean_alloc_closure((void*)(l_Lean_Elab_Term_trace___boxed), 5, 3);
lean_closure_set(x_34, 0, x_33);
lean_closure_set(x_34, 1, x_1);
lean_closure_set(x_34, 2, x_32);
lean_inc(x_2);
x_35 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_34, x_2, x_4);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_36, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec(x_39);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec(x_40);
x_42 = l_Lean_PersistentEnvExtension_getState___rarg(x_38, x_41);
lean_dec(x_41);
lean_dec(x_38);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
lean_inc(x_1);
x_44 = l_Lean_Syntax_getKind(x_1);
x_45 = l_Lean_SMap_find_x3f___at_Lean_Elab_Tactic_evalTactic___main___spec__1(x_43, x_44);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_46 = l_Lean_Elab_Tactic_getCurrMacroScope(x_2, x_36);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = l_Lean_Elab_Tactic_getEnv___rarg(x_48);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
lean_inc(x_1);
x_52 = l_Lean_Elab_expandMacro(x_50, x_1, x_47);
lean_dec(x_50);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_30);
lean_dec(x_6);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
x_53 = l_Lean_Name_toString___closed__1;
x_54 = l_Lean_Name_toStringWithSep___main(x_53, x_44);
x_55 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_55, 0, x_54);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_55);
x_57 = l_Lean_Meta_Exception_toMessageData___closed__45;
x_58 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_56);
x_59 = l_Lean_Elab_Term_elabTermAux___main___closed__6;
x_60 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_60, x_2, x_51);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_44);
lean_dec(x_2);
x_62 = lean_ctor_get(x_52, 0);
lean_inc(x_62);
lean_dec(x_52);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_1);
lean_ctor_set(x_63, 1, x_19);
x_64 = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(x_64, 0, x_6);
lean_ctor_set(x_64, 1, x_12);
lean_ctor_set(x_64, 2, x_13);
lean_ctor_set(x_64, 3, x_14);
lean_ctor_set(x_64, 4, x_15);
lean_ctor_set(x_64, 5, x_16);
lean_ctor_set(x_64, 6, x_17);
lean_ctor_set(x_64, 7, x_18);
lean_ctor_set(x_64, 8, x_63);
lean_ctor_set(x_64, 9, x_30);
lean_ctor_set_uint8(x_64, sizeof(void*)*10, x_20);
x_65 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_8);
lean_ctor_set(x_65, 2, x_9);
x_1 = x_62;
x_2 = x_65;
x_3 = x_51;
goto _start;
}
}
else
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_44);
lean_dec(x_30);
lean_dec(x_6);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
x_67 = lean_ctor_get(x_45, 0);
lean_inc(x_67);
lean_dec(x_45);
lean_inc(x_36);
x_68 = l___private_Init_Lean_Elab_Tactic_Basic_1__evalTacticUsing___main(x_36, x_1, x_67, x_2, x_36);
return x_68;
}
}
else
{
uint8_t x_69; 
lean_dec(x_2);
lean_dec(x_30);
lean_dec(x_6);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_69 = !lean_is_exclusive(x_35);
if (x_69 == 0)
{
return x_35;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_35, 0);
x_71 = lean_ctor_get(x_35, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_35);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
else
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_30);
lean_dec(x_6);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
x_73 = l_Lean_Elab_Tactic_evalTactic___main___closed__3;
x_74 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_73, x_2, x_4);
return x_74;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_75 = lean_ctor_get(x_28, 0);
x_76 = lean_ctor_get(x_28, 1);
x_77 = lean_ctor_get(x_28, 2);
x_78 = lean_ctor_get(x_28, 3);
x_79 = lean_ctor_get(x_28, 4);
x_80 = lean_ctor_get(x_28, 5);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_28);
x_81 = lean_nat_add(x_80, x_25);
x_82 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_82, 0, x_75);
lean_ctor_set(x_82, 1, x_76);
lean_ctor_set(x_82, 2, x_77);
lean_ctor_set(x_82, 3, x_78);
lean_ctor_set(x_82, 4, x_79);
lean_ctor_set(x_82, 5, x_81);
lean_ctor_set(x_4, 0, x_82);
lean_inc(x_80);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_6);
lean_ctor_set(x_5, 9, x_80);
lean_inc(x_9);
lean_inc(x_8);
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_inc(x_1);
x_83 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___main___lambda__1___boxed), 2, 1);
lean_closure_set(x_83, 0, x_1);
x_84 = l_Lean_Elab_Tactic_evalTactic___main___closed__4;
lean_inc(x_1);
x_85 = lean_alloc_closure((void*)(l_Lean_Elab_Term_trace___boxed), 5, 3);
lean_closure_set(x_85, 0, x_84);
lean_closure_set(x_85, 1, x_1);
lean_closure_set(x_85, 2, x_83);
lean_inc(x_2);
x_86 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_85, x_2, x_4);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
lean_dec(x_86);
x_88 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
x_90 = lean_ctor_get(x_87, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
lean_dec(x_90);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
lean_dec(x_91);
x_93 = l_Lean_PersistentEnvExtension_getState___rarg(x_89, x_92);
lean_dec(x_92);
lean_dec(x_89);
x_94 = lean_ctor_get(x_93, 1);
lean_inc(x_94);
lean_dec(x_93);
lean_inc(x_1);
x_95 = l_Lean_Syntax_getKind(x_1);
x_96 = l_Lean_SMap_find_x3f___at_Lean_Elab_Tactic_evalTactic___main___spec__1(x_94, x_95);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_97 = l_Lean_Elab_Tactic_getCurrMacroScope(x_2, x_87);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec(x_97);
x_100 = l_Lean_Elab_Tactic_getEnv___rarg(x_99);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
lean_inc(x_1);
x_103 = l_Lean_Elab_expandMacro(x_101, x_1, x_98);
lean_dec(x_101);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_80);
lean_dec(x_6);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
x_104 = l_Lean_Name_toString___closed__1;
x_105 = l_Lean_Name_toStringWithSep___main(x_104, x_95);
x_106 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_106, 0, x_105);
x_107 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_107, 0, x_106);
x_108 = l_Lean_Meta_Exception_toMessageData___closed__45;
x_109 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_107);
x_110 = l_Lean_Elab_Term_elabTermAux___main___closed__6;
x_111 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
x_112 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_111, x_2, x_102);
return x_112;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_95);
lean_dec(x_2);
x_113 = lean_ctor_get(x_103, 0);
lean_inc(x_113);
lean_dec(x_103);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_1);
lean_ctor_set(x_114, 1, x_19);
x_115 = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(x_115, 0, x_6);
lean_ctor_set(x_115, 1, x_12);
lean_ctor_set(x_115, 2, x_13);
lean_ctor_set(x_115, 3, x_14);
lean_ctor_set(x_115, 4, x_15);
lean_ctor_set(x_115, 5, x_16);
lean_ctor_set(x_115, 6, x_17);
lean_ctor_set(x_115, 7, x_18);
lean_ctor_set(x_115, 8, x_114);
lean_ctor_set(x_115, 9, x_80);
lean_ctor_set_uint8(x_115, sizeof(void*)*10, x_20);
x_116 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_8);
lean_ctor_set(x_116, 2, x_9);
x_1 = x_113;
x_2 = x_116;
x_3 = x_102;
goto _start;
}
}
else
{
lean_object* x_118; lean_object* x_119; 
lean_dec(x_95);
lean_dec(x_80);
lean_dec(x_6);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
x_118 = lean_ctor_get(x_96, 0);
lean_inc(x_118);
lean_dec(x_96);
lean_inc(x_87);
x_119 = l___private_Init_Lean_Elab_Tactic_Basic_1__evalTacticUsing___main(x_87, x_1, x_118, x_2, x_87);
return x_119;
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_2);
lean_dec(x_80);
lean_dec(x_6);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_120 = lean_ctor_get(x_86, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_86, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_122 = x_86;
} else {
 lean_dec_ref(x_86);
 x_122 = lean_box(0);
}
if (lean_is_scalar(x_122)) {
 x_123 = lean_alloc_ctor(1, 2, 0);
} else {
 x_123 = x_122;
}
lean_ctor_set(x_123, 0, x_120);
lean_ctor_set(x_123, 1, x_121);
return x_123;
}
}
else
{
lean_object* x_124; lean_object* x_125; 
lean_dec(x_80);
lean_dec(x_6);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
x_124 = l_Lean_Elab_Tactic_evalTactic___main___closed__3;
x_125 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_124, x_2, x_4);
return x_125;
}
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_126 = lean_ctor_get(x_4, 0);
x_127 = lean_ctor_get(x_4, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_4);
x_128 = lean_ctor_get(x_126, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_126, 1);
lean_inc(x_129);
x_130 = lean_ctor_get(x_126, 2);
lean_inc(x_130);
x_131 = lean_ctor_get(x_126, 3);
lean_inc(x_131);
x_132 = lean_ctor_get(x_126, 4);
lean_inc(x_132);
x_133 = lean_ctor_get(x_126, 5);
lean_inc(x_133);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 lean_ctor_release(x_126, 2);
 lean_ctor_release(x_126, 3);
 lean_ctor_release(x_126, 4);
 lean_ctor_release(x_126, 5);
 x_134 = x_126;
} else {
 lean_dec_ref(x_126);
 x_134 = lean_box(0);
}
x_135 = lean_nat_add(x_133, x_25);
if (lean_is_scalar(x_134)) {
 x_136 = lean_alloc_ctor(0, 6, 0);
} else {
 x_136 = x_134;
}
lean_ctor_set(x_136, 0, x_128);
lean_ctor_set(x_136, 1, x_129);
lean_ctor_set(x_136, 2, x_130);
lean_ctor_set(x_136, 3, x_131);
lean_ctor_set(x_136, 4, x_132);
lean_ctor_set(x_136, 5, x_135);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_127);
lean_inc(x_133);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_6);
lean_ctor_set(x_5, 9, x_133);
lean_inc(x_9);
lean_inc(x_8);
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_inc(x_1);
x_138 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___main___lambda__1___boxed), 2, 1);
lean_closure_set(x_138, 0, x_1);
x_139 = l_Lean_Elab_Tactic_evalTactic___main___closed__4;
lean_inc(x_1);
x_140 = lean_alloc_closure((void*)(l_Lean_Elab_Term_trace___boxed), 5, 3);
lean_closure_set(x_140, 0, x_139);
lean_closure_set(x_140, 1, x_1);
lean_closure_set(x_140, 2, x_138);
lean_inc(x_2);
x_141 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_140, x_2, x_137);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_142 = lean_ctor_get(x_141, 1);
lean_inc(x_142);
lean_dec(x_141);
x_143 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_144 = lean_ctor_get(x_143, 1);
lean_inc(x_144);
x_145 = lean_ctor_get(x_142, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
lean_dec(x_145);
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
lean_dec(x_146);
x_148 = l_Lean_PersistentEnvExtension_getState___rarg(x_144, x_147);
lean_dec(x_147);
lean_dec(x_144);
x_149 = lean_ctor_get(x_148, 1);
lean_inc(x_149);
lean_dec(x_148);
lean_inc(x_1);
x_150 = l_Lean_Syntax_getKind(x_1);
x_151 = l_Lean_SMap_find_x3f___at_Lean_Elab_Tactic_evalTactic___main___spec__1(x_149, x_150);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_152 = l_Lean_Elab_Tactic_getCurrMacroScope(x_2, x_142);
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_152, 1);
lean_inc(x_154);
lean_dec(x_152);
x_155 = l_Lean_Elab_Tactic_getEnv___rarg(x_154);
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_155, 1);
lean_inc(x_157);
lean_dec(x_155);
lean_inc(x_1);
x_158 = l_Lean_Elab_expandMacro(x_156, x_1, x_153);
lean_dec(x_156);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
lean_dec(x_133);
lean_dec(x_6);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
x_159 = l_Lean_Name_toString___closed__1;
x_160 = l_Lean_Name_toStringWithSep___main(x_159, x_150);
x_161 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_161, 0, x_160);
x_162 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_162, 0, x_161);
x_163 = l_Lean_Meta_Exception_toMessageData___closed__45;
x_164 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_162);
x_165 = l_Lean_Elab_Term_elabTermAux___main___closed__6;
x_166 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_166, 0, x_164);
lean_ctor_set(x_166, 1, x_165);
x_167 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_166, x_2, x_157);
return x_167;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
lean_dec(x_150);
lean_dec(x_2);
x_168 = lean_ctor_get(x_158, 0);
lean_inc(x_168);
lean_dec(x_158);
x_169 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_169, 0, x_1);
lean_ctor_set(x_169, 1, x_19);
x_170 = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(x_170, 0, x_6);
lean_ctor_set(x_170, 1, x_12);
lean_ctor_set(x_170, 2, x_13);
lean_ctor_set(x_170, 3, x_14);
lean_ctor_set(x_170, 4, x_15);
lean_ctor_set(x_170, 5, x_16);
lean_ctor_set(x_170, 6, x_17);
lean_ctor_set(x_170, 7, x_18);
lean_ctor_set(x_170, 8, x_169);
lean_ctor_set(x_170, 9, x_133);
lean_ctor_set_uint8(x_170, sizeof(void*)*10, x_20);
x_171 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_8);
lean_ctor_set(x_171, 2, x_9);
x_1 = x_168;
x_2 = x_171;
x_3 = x_157;
goto _start;
}
}
else
{
lean_object* x_173; lean_object* x_174; 
lean_dec(x_150);
lean_dec(x_133);
lean_dec(x_6);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
x_173 = lean_ctor_get(x_151, 0);
lean_inc(x_173);
lean_dec(x_151);
lean_inc(x_142);
x_174 = l___private_Init_Lean_Elab_Tactic_Basic_1__evalTacticUsing___main(x_142, x_1, x_173, x_2, x_142);
return x_174;
}
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
lean_dec(x_2);
lean_dec(x_133);
lean_dec(x_6);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_175 = lean_ctor_get(x_141, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_141, 1);
lean_inc(x_176);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_177 = x_141;
} else {
 lean_dec_ref(x_141);
 x_177 = lean_box(0);
}
if (lean_is_scalar(x_177)) {
 x_178 = lean_alloc_ctor(1, 2, 0);
} else {
 x_178 = x_177;
}
lean_ctor_set(x_178, 0, x_175);
lean_ctor_set(x_178, 1, x_176);
return x_178;
}
}
else
{
lean_object* x_179; lean_object* x_180; 
lean_dec(x_133);
lean_dec(x_6);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
x_179 = l_Lean_Elab_Tactic_evalTactic___main___closed__3;
x_180 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_179, x_2, x_137);
return x_180;
}
}
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_181 = lean_ctor_get(x_6, 0);
x_182 = lean_ctor_get(x_6, 1);
x_183 = lean_ctor_get(x_6, 2);
x_184 = lean_ctor_get(x_6, 3);
x_185 = lean_ctor_get(x_6, 4);
lean_inc(x_185);
lean_inc(x_184);
lean_inc(x_183);
lean_inc(x_182);
lean_inc(x_181);
lean_dec(x_6);
x_186 = lean_unsigned_to_nat(1u);
x_187 = lean_nat_add(x_184, x_186);
lean_dec(x_184);
x_188 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_188, 0, x_181);
lean_ctor_set(x_188, 1, x_182);
lean_ctor_set(x_188, 2, x_183);
lean_ctor_set(x_188, 3, x_187);
lean_ctor_set(x_188, 4, x_185);
x_189 = lean_ctor_get(x_4, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_4, 1);
lean_inc(x_190);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_191 = x_4;
} else {
 lean_dec_ref(x_4);
 x_191 = lean_box(0);
}
x_192 = lean_ctor_get(x_189, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_189, 1);
lean_inc(x_193);
x_194 = lean_ctor_get(x_189, 2);
lean_inc(x_194);
x_195 = lean_ctor_get(x_189, 3);
lean_inc(x_195);
x_196 = lean_ctor_get(x_189, 4);
lean_inc(x_196);
x_197 = lean_ctor_get(x_189, 5);
lean_inc(x_197);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 lean_ctor_release(x_189, 2);
 lean_ctor_release(x_189, 3);
 lean_ctor_release(x_189, 4);
 lean_ctor_release(x_189, 5);
 x_198 = x_189;
} else {
 lean_dec_ref(x_189);
 x_198 = lean_box(0);
}
x_199 = lean_nat_add(x_197, x_186);
if (lean_is_scalar(x_198)) {
 x_200 = lean_alloc_ctor(0, 6, 0);
} else {
 x_200 = x_198;
}
lean_ctor_set(x_200, 0, x_192);
lean_ctor_set(x_200, 1, x_193);
lean_ctor_set(x_200, 2, x_194);
lean_ctor_set(x_200, 3, x_195);
lean_ctor_set(x_200, 4, x_196);
lean_ctor_set(x_200, 5, x_199);
if (lean_is_scalar(x_191)) {
 x_201 = lean_alloc_ctor(0, 2, 0);
} else {
 x_201 = x_191;
}
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_190);
lean_inc(x_197);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_188);
lean_ctor_set(x_5, 9, x_197);
lean_ctor_set(x_5, 0, x_188);
lean_inc(x_9);
lean_inc(x_8);
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
lean_inc(x_1);
x_202 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___main___lambda__1___boxed), 2, 1);
lean_closure_set(x_202, 0, x_1);
x_203 = l_Lean_Elab_Tactic_evalTactic___main___closed__4;
lean_inc(x_1);
x_204 = lean_alloc_closure((void*)(l_Lean_Elab_Term_trace___boxed), 5, 3);
lean_closure_set(x_204, 0, x_203);
lean_closure_set(x_204, 1, x_1);
lean_closure_set(x_204, 2, x_202);
lean_inc(x_2);
x_205 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_204, x_2, x_201);
if (lean_obj_tag(x_205) == 0)
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_206 = lean_ctor_get(x_205, 1);
lean_inc(x_206);
lean_dec(x_205);
x_207 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_208 = lean_ctor_get(x_207, 1);
lean_inc(x_208);
x_209 = lean_ctor_get(x_206, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
lean_dec(x_209);
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
lean_dec(x_210);
x_212 = l_Lean_PersistentEnvExtension_getState___rarg(x_208, x_211);
lean_dec(x_211);
lean_dec(x_208);
x_213 = lean_ctor_get(x_212, 1);
lean_inc(x_213);
lean_dec(x_212);
lean_inc(x_1);
x_214 = l_Lean_Syntax_getKind(x_1);
x_215 = l_Lean_SMap_find_x3f___at_Lean_Elab_Tactic_evalTactic___main___spec__1(x_213, x_214);
if (lean_obj_tag(x_215) == 0)
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_216 = l_Lean_Elab_Tactic_getCurrMacroScope(x_2, x_206);
x_217 = lean_ctor_get(x_216, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_216, 1);
lean_inc(x_218);
lean_dec(x_216);
x_219 = l_Lean_Elab_Tactic_getEnv___rarg(x_218);
x_220 = lean_ctor_get(x_219, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_219, 1);
lean_inc(x_221);
lean_dec(x_219);
lean_inc(x_1);
x_222 = l_Lean_Elab_expandMacro(x_220, x_1, x_217);
lean_dec(x_220);
if (lean_obj_tag(x_222) == 0)
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
lean_dec(x_197);
lean_dec(x_188);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
x_223 = l_Lean_Name_toString___closed__1;
x_224 = l_Lean_Name_toStringWithSep___main(x_223, x_214);
x_225 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_225, 0, x_224);
x_226 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_226, 0, x_225);
x_227 = l_Lean_Meta_Exception_toMessageData___closed__45;
x_228 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_228, 0, x_227);
lean_ctor_set(x_228, 1, x_226);
x_229 = l_Lean_Elab_Term_elabTermAux___main___closed__6;
x_230 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_230, 0, x_228);
lean_ctor_set(x_230, 1, x_229);
x_231 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_230, x_2, x_221);
return x_231;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
lean_dec(x_214);
lean_dec(x_2);
x_232 = lean_ctor_get(x_222, 0);
lean_inc(x_232);
lean_dec(x_222);
x_233 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_233, 0, x_1);
lean_ctor_set(x_233, 1, x_19);
x_234 = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(x_234, 0, x_188);
lean_ctor_set(x_234, 1, x_12);
lean_ctor_set(x_234, 2, x_13);
lean_ctor_set(x_234, 3, x_14);
lean_ctor_set(x_234, 4, x_15);
lean_ctor_set(x_234, 5, x_16);
lean_ctor_set(x_234, 6, x_17);
lean_ctor_set(x_234, 7, x_18);
lean_ctor_set(x_234, 8, x_233);
lean_ctor_set(x_234, 9, x_197);
lean_ctor_set_uint8(x_234, sizeof(void*)*10, x_20);
x_235 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_235, 0, x_234);
lean_ctor_set(x_235, 1, x_8);
lean_ctor_set(x_235, 2, x_9);
x_1 = x_232;
x_2 = x_235;
x_3 = x_221;
goto _start;
}
}
else
{
lean_object* x_237; lean_object* x_238; 
lean_dec(x_214);
lean_dec(x_197);
lean_dec(x_188);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
x_237 = lean_ctor_get(x_215, 0);
lean_inc(x_237);
lean_dec(x_215);
lean_inc(x_206);
x_238 = l___private_Init_Lean_Elab_Tactic_Basic_1__evalTacticUsing___main(x_206, x_1, x_237, x_2, x_206);
return x_238;
}
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
lean_dec(x_2);
lean_dec(x_197);
lean_dec(x_188);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_239 = lean_ctor_get(x_205, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_205, 1);
lean_inc(x_240);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 x_241 = x_205;
} else {
 lean_dec_ref(x_205);
 x_241 = lean_box(0);
}
if (lean_is_scalar(x_241)) {
 x_242 = lean_alloc_ctor(1, 2, 0);
} else {
 x_242 = x_241;
}
lean_ctor_set(x_242, 0, x_239);
lean_ctor_set(x_242, 1, x_240);
return x_242;
}
}
else
{
lean_object* x_243; lean_object* x_244; 
lean_dec(x_197);
lean_dec(x_188);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
x_243 = l_Lean_Elab_Tactic_evalTactic___main___closed__3;
x_244 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_243, x_2, x_201);
return x_244;
}
}
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; uint8_t x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; 
x_245 = lean_ctor_get(x_5, 1);
x_246 = lean_ctor_get(x_5, 2);
x_247 = lean_ctor_get(x_5, 3);
x_248 = lean_ctor_get(x_5, 4);
x_249 = lean_ctor_get(x_5, 5);
x_250 = lean_ctor_get(x_5, 6);
x_251 = lean_ctor_get(x_5, 7);
x_252 = lean_ctor_get(x_5, 8);
x_253 = lean_ctor_get_uint8(x_5, sizeof(void*)*10);
lean_inc(x_252);
lean_inc(x_251);
lean_inc(x_250);
lean_inc(x_249);
lean_inc(x_248);
lean_inc(x_247);
lean_inc(x_246);
lean_inc(x_245);
lean_dec(x_5);
x_254 = lean_ctor_get(x_6, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_6, 1);
lean_inc(x_255);
x_256 = lean_ctor_get(x_6, 2);
lean_inc(x_256);
x_257 = lean_ctor_get(x_6, 3);
lean_inc(x_257);
x_258 = lean_ctor_get(x_6, 4);
lean_inc(x_258);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 lean_ctor_release(x_6, 4);
 x_259 = x_6;
} else {
 lean_dec_ref(x_6);
 x_259 = lean_box(0);
}
x_260 = lean_unsigned_to_nat(1u);
x_261 = lean_nat_add(x_257, x_260);
lean_dec(x_257);
if (lean_is_scalar(x_259)) {
 x_262 = lean_alloc_ctor(0, 5, 0);
} else {
 x_262 = x_259;
}
lean_ctor_set(x_262, 0, x_254);
lean_ctor_set(x_262, 1, x_255);
lean_ctor_set(x_262, 2, x_256);
lean_ctor_set(x_262, 3, x_261);
lean_ctor_set(x_262, 4, x_258);
x_263 = lean_ctor_get(x_4, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_4, 1);
lean_inc(x_264);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_265 = x_4;
} else {
 lean_dec_ref(x_4);
 x_265 = lean_box(0);
}
x_266 = lean_ctor_get(x_263, 0);
lean_inc(x_266);
x_267 = lean_ctor_get(x_263, 1);
lean_inc(x_267);
x_268 = lean_ctor_get(x_263, 2);
lean_inc(x_268);
x_269 = lean_ctor_get(x_263, 3);
lean_inc(x_269);
x_270 = lean_ctor_get(x_263, 4);
lean_inc(x_270);
x_271 = lean_ctor_get(x_263, 5);
lean_inc(x_271);
if (lean_is_exclusive(x_263)) {
 lean_ctor_release(x_263, 0);
 lean_ctor_release(x_263, 1);
 lean_ctor_release(x_263, 2);
 lean_ctor_release(x_263, 3);
 lean_ctor_release(x_263, 4);
 lean_ctor_release(x_263, 5);
 x_272 = x_263;
} else {
 lean_dec_ref(x_263);
 x_272 = lean_box(0);
}
x_273 = lean_nat_add(x_271, x_260);
if (lean_is_scalar(x_272)) {
 x_274 = lean_alloc_ctor(0, 6, 0);
} else {
 x_274 = x_272;
}
lean_ctor_set(x_274, 0, x_266);
lean_ctor_set(x_274, 1, x_267);
lean_ctor_set(x_274, 2, x_268);
lean_ctor_set(x_274, 3, x_269);
lean_ctor_set(x_274, 4, x_270);
lean_ctor_set(x_274, 5, x_273);
if (lean_is_scalar(x_265)) {
 x_275 = lean_alloc_ctor(0, 2, 0);
} else {
 x_275 = x_265;
}
lean_ctor_set(x_275, 0, x_274);
lean_ctor_set(x_275, 1, x_264);
lean_inc(x_271);
lean_inc(x_252);
lean_inc(x_251);
lean_inc(x_250);
lean_inc(x_249);
lean_inc(x_248);
lean_inc(x_247);
lean_inc(x_246);
lean_inc(x_245);
lean_inc(x_262);
x_276 = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(x_276, 0, x_262);
lean_ctor_set(x_276, 1, x_245);
lean_ctor_set(x_276, 2, x_246);
lean_ctor_set(x_276, 3, x_247);
lean_ctor_set(x_276, 4, x_248);
lean_ctor_set(x_276, 5, x_249);
lean_ctor_set(x_276, 6, x_250);
lean_ctor_set(x_276, 7, x_251);
lean_ctor_set(x_276, 8, x_252);
lean_ctor_set(x_276, 9, x_271);
lean_ctor_set_uint8(x_276, sizeof(void*)*10, x_253);
lean_inc(x_9);
lean_inc(x_8);
lean_ctor_set(x_2, 0, x_276);
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; 
lean_inc(x_1);
x_277 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___main___lambda__1___boxed), 2, 1);
lean_closure_set(x_277, 0, x_1);
x_278 = l_Lean_Elab_Tactic_evalTactic___main___closed__4;
lean_inc(x_1);
x_279 = lean_alloc_closure((void*)(l_Lean_Elab_Term_trace___boxed), 5, 3);
lean_closure_set(x_279, 0, x_278);
lean_closure_set(x_279, 1, x_1);
lean_closure_set(x_279, 2, x_277);
lean_inc(x_2);
x_280 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_279, x_2, x_275);
if (lean_obj_tag(x_280) == 0)
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; 
x_281 = lean_ctor_get(x_280, 1);
lean_inc(x_281);
lean_dec(x_280);
x_282 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_283 = lean_ctor_get(x_282, 1);
lean_inc(x_283);
x_284 = lean_ctor_get(x_281, 0);
lean_inc(x_284);
x_285 = lean_ctor_get(x_284, 0);
lean_inc(x_285);
lean_dec(x_284);
x_286 = lean_ctor_get(x_285, 0);
lean_inc(x_286);
lean_dec(x_285);
x_287 = l_Lean_PersistentEnvExtension_getState___rarg(x_283, x_286);
lean_dec(x_286);
lean_dec(x_283);
x_288 = lean_ctor_get(x_287, 1);
lean_inc(x_288);
lean_dec(x_287);
lean_inc(x_1);
x_289 = l_Lean_Syntax_getKind(x_1);
x_290 = l_Lean_SMap_find_x3f___at_Lean_Elab_Tactic_evalTactic___main___spec__1(x_288, x_289);
if (lean_obj_tag(x_290) == 0)
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; 
x_291 = l_Lean_Elab_Tactic_getCurrMacroScope(x_2, x_281);
x_292 = lean_ctor_get(x_291, 0);
lean_inc(x_292);
x_293 = lean_ctor_get(x_291, 1);
lean_inc(x_293);
lean_dec(x_291);
x_294 = l_Lean_Elab_Tactic_getEnv___rarg(x_293);
x_295 = lean_ctor_get(x_294, 0);
lean_inc(x_295);
x_296 = lean_ctor_get(x_294, 1);
lean_inc(x_296);
lean_dec(x_294);
lean_inc(x_1);
x_297 = l_Lean_Elab_expandMacro(x_295, x_1, x_292);
lean_dec(x_295);
if (lean_obj_tag(x_297) == 0)
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; 
lean_dec(x_271);
lean_dec(x_262);
lean_dec(x_252);
lean_dec(x_251);
lean_dec(x_250);
lean_dec(x_249);
lean_dec(x_248);
lean_dec(x_247);
lean_dec(x_246);
lean_dec(x_245);
lean_dec(x_9);
lean_dec(x_8);
x_298 = l_Lean_Name_toString___closed__1;
x_299 = l_Lean_Name_toStringWithSep___main(x_298, x_289);
x_300 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_300, 0, x_299);
x_301 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_301, 0, x_300);
x_302 = l_Lean_Meta_Exception_toMessageData___closed__45;
x_303 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_303, 0, x_302);
lean_ctor_set(x_303, 1, x_301);
x_304 = l_Lean_Elab_Term_elabTermAux___main___closed__6;
x_305 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_305, 0, x_303);
lean_ctor_set(x_305, 1, x_304);
x_306 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_305, x_2, x_296);
return x_306;
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; 
lean_dec(x_289);
lean_dec(x_2);
x_307 = lean_ctor_get(x_297, 0);
lean_inc(x_307);
lean_dec(x_297);
x_308 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_308, 0, x_1);
lean_ctor_set(x_308, 1, x_252);
x_309 = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(x_309, 0, x_262);
lean_ctor_set(x_309, 1, x_245);
lean_ctor_set(x_309, 2, x_246);
lean_ctor_set(x_309, 3, x_247);
lean_ctor_set(x_309, 4, x_248);
lean_ctor_set(x_309, 5, x_249);
lean_ctor_set(x_309, 6, x_250);
lean_ctor_set(x_309, 7, x_251);
lean_ctor_set(x_309, 8, x_308);
lean_ctor_set(x_309, 9, x_271);
lean_ctor_set_uint8(x_309, sizeof(void*)*10, x_253);
x_310 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_310, 0, x_309);
lean_ctor_set(x_310, 1, x_8);
lean_ctor_set(x_310, 2, x_9);
x_1 = x_307;
x_2 = x_310;
x_3 = x_296;
goto _start;
}
}
else
{
lean_object* x_312; lean_object* x_313; 
lean_dec(x_289);
lean_dec(x_271);
lean_dec(x_262);
lean_dec(x_252);
lean_dec(x_251);
lean_dec(x_250);
lean_dec(x_249);
lean_dec(x_248);
lean_dec(x_247);
lean_dec(x_246);
lean_dec(x_245);
lean_dec(x_9);
lean_dec(x_8);
x_312 = lean_ctor_get(x_290, 0);
lean_inc(x_312);
lean_dec(x_290);
lean_inc(x_281);
x_313 = l___private_Init_Lean_Elab_Tactic_Basic_1__evalTacticUsing___main(x_281, x_1, x_312, x_2, x_281);
return x_313;
}
}
else
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; 
lean_dec(x_2);
lean_dec(x_271);
lean_dec(x_262);
lean_dec(x_252);
lean_dec(x_251);
lean_dec(x_250);
lean_dec(x_249);
lean_dec(x_248);
lean_dec(x_247);
lean_dec(x_246);
lean_dec(x_245);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_314 = lean_ctor_get(x_280, 0);
lean_inc(x_314);
x_315 = lean_ctor_get(x_280, 1);
lean_inc(x_315);
if (lean_is_exclusive(x_280)) {
 lean_ctor_release(x_280, 0);
 lean_ctor_release(x_280, 1);
 x_316 = x_280;
} else {
 lean_dec_ref(x_280);
 x_316 = lean_box(0);
}
if (lean_is_scalar(x_316)) {
 x_317 = lean_alloc_ctor(1, 2, 0);
} else {
 x_317 = x_316;
}
lean_ctor_set(x_317, 0, x_314);
lean_ctor_set(x_317, 1, x_315);
return x_317;
}
}
else
{
lean_object* x_318; lean_object* x_319; 
lean_dec(x_271);
lean_dec(x_262);
lean_dec(x_252);
lean_dec(x_251);
lean_dec(x_250);
lean_dec(x_249);
lean_dec(x_248);
lean_dec(x_247);
lean_dec(x_246);
lean_dec(x_245);
lean_dec(x_9);
lean_dec(x_8);
x_318 = l_Lean_Elab_Tactic_evalTactic___main___closed__3;
x_319 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_318, x_2, x_275);
return x_319;
}
}
}
else
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; uint8_t x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; 
x_320 = lean_ctor_get(x_2, 1);
x_321 = lean_ctor_get(x_2, 2);
lean_inc(x_321);
lean_inc(x_320);
lean_dec(x_2);
x_322 = lean_ctor_get(x_5, 1);
lean_inc(x_322);
x_323 = lean_ctor_get(x_5, 2);
lean_inc(x_323);
x_324 = lean_ctor_get(x_5, 3);
lean_inc(x_324);
x_325 = lean_ctor_get(x_5, 4);
lean_inc(x_325);
x_326 = lean_ctor_get(x_5, 5);
lean_inc(x_326);
x_327 = lean_ctor_get(x_5, 6);
lean_inc(x_327);
x_328 = lean_ctor_get(x_5, 7);
lean_inc(x_328);
x_329 = lean_ctor_get(x_5, 8);
lean_inc(x_329);
x_330 = lean_ctor_get_uint8(x_5, sizeof(void*)*10);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 lean_ctor_release(x_5, 3);
 lean_ctor_release(x_5, 4);
 lean_ctor_release(x_5, 5);
 lean_ctor_release(x_5, 6);
 lean_ctor_release(x_5, 7);
 lean_ctor_release(x_5, 8);
 lean_ctor_release(x_5, 9);
 x_331 = x_5;
} else {
 lean_dec_ref(x_5);
 x_331 = lean_box(0);
}
x_332 = lean_ctor_get(x_6, 0);
lean_inc(x_332);
x_333 = lean_ctor_get(x_6, 1);
lean_inc(x_333);
x_334 = lean_ctor_get(x_6, 2);
lean_inc(x_334);
x_335 = lean_ctor_get(x_6, 3);
lean_inc(x_335);
x_336 = lean_ctor_get(x_6, 4);
lean_inc(x_336);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 lean_ctor_release(x_6, 4);
 x_337 = x_6;
} else {
 lean_dec_ref(x_6);
 x_337 = lean_box(0);
}
x_338 = lean_unsigned_to_nat(1u);
x_339 = lean_nat_add(x_335, x_338);
lean_dec(x_335);
if (lean_is_scalar(x_337)) {
 x_340 = lean_alloc_ctor(0, 5, 0);
} else {
 x_340 = x_337;
}
lean_ctor_set(x_340, 0, x_332);
lean_ctor_set(x_340, 1, x_333);
lean_ctor_set(x_340, 2, x_334);
lean_ctor_set(x_340, 3, x_339);
lean_ctor_set(x_340, 4, x_336);
x_341 = lean_ctor_get(x_4, 0);
lean_inc(x_341);
x_342 = lean_ctor_get(x_4, 1);
lean_inc(x_342);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_343 = x_4;
} else {
 lean_dec_ref(x_4);
 x_343 = lean_box(0);
}
x_344 = lean_ctor_get(x_341, 0);
lean_inc(x_344);
x_345 = lean_ctor_get(x_341, 1);
lean_inc(x_345);
x_346 = lean_ctor_get(x_341, 2);
lean_inc(x_346);
x_347 = lean_ctor_get(x_341, 3);
lean_inc(x_347);
x_348 = lean_ctor_get(x_341, 4);
lean_inc(x_348);
x_349 = lean_ctor_get(x_341, 5);
lean_inc(x_349);
if (lean_is_exclusive(x_341)) {
 lean_ctor_release(x_341, 0);
 lean_ctor_release(x_341, 1);
 lean_ctor_release(x_341, 2);
 lean_ctor_release(x_341, 3);
 lean_ctor_release(x_341, 4);
 lean_ctor_release(x_341, 5);
 x_350 = x_341;
} else {
 lean_dec_ref(x_341);
 x_350 = lean_box(0);
}
x_351 = lean_nat_add(x_349, x_338);
if (lean_is_scalar(x_350)) {
 x_352 = lean_alloc_ctor(0, 6, 0);
} else {
 x_352 = x_350;
}
lean_ctor_set(x_352, 0, x_344);
lean_ctor_set(x_352, 1, x_345);
lean_ctor_set(x_352, 2, x_346);
lean_ctor_set(x_352, 3, x_347);
lean_ctor_set(x_352, 4, x_348);
lean_ctor_set(x_352, 5, x_351);
if (lean_is_scalar(x_343)) {
 x_353 = lean_alloc_ctor(0, 2, 0);
} else {
 x_353 = x_343;
}
lean_ctor_set(x_353, 0, x_352);
lean_ctor_set(x_353, 1, x_342);
lean_inc(x_349);
lean_inc(x_329);
lean_inc(x_328);
lean_inc(x_327);
lean_inc(x_326);
lean_inc(x_325);
lean_inc(x_324);
lean_inc(x_323);
lean_inc(x_322);
lean_inc(x_340);
if (lean_is_scalar(x_331)) {
 x_354 = lean_alloc_ctor(0, 10, 1);
} else {
 x_354 = x_331;
}
lean_ctor_set(x_354, 0, x_340);
lean_ctor_set(x_354, 1, x_322);
lean_ctor_set(x_354, 2, x_323);
lean_ctor_set(x_354, 3, x_324);
lean_ctor_set(x_354, 4, x_325);
lean_ctor_set(x_354, 5, x_326);
lean_ctor_set(x_354, 6, x_327);
lean_ctor_set(x_354, 7, x_328);
lean_ctor_set(x_354, 8, x_329);
lean_ctor_set(x_354, 9, x_349);
lean_ctor_set_uint8(x_354, sizeof(void*)*10, x_330);
lean_inc(x_321);
lean_inc(x_320);
x_355 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_355, 0, x_354);
lean_ctor_set(x_355, 1, x_320);
lean_ctor_set(x_355, 2, x_321);
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; 
lean_inc(x_1);
x_356 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___main___lambda__1___boxed), 2, 1);
lean_closure_set(x_356, 0, x_1);
x_357 = l_Lean_Elab_Tactic_evalTactic___main___closed__4;
lean_inc(x_1);
x_358 = lean_alloc_closure((void*)(l_Lean_Elab_Term_trace___boxed), 5, 3);
lean_closure_set(x_358, 0, x_357);
lean_closure_set(x_358, 1, x_1);
lean_closure_set(x_358, 2, x_356);
lean_inc(x_355);
x_359 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_358, x_355, x_353);
if (lean_obj_tag(x_359) == 0)
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; 
x_360 = lean_ctor_get(x_359, 1);
lean_inc(x_360);
lean_dec(x_359);
x_361 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_362 = lean_ctor_get(x_361, 1);
lean_inc(x_362);
x_363 = lean_ctor_get(x_360, 0);
lean_inc(x_363);
x_364 = lean_ctor_get(x_363, 0);
lean_inc(x_364);
lean_dec(x_363);
x_365 = lean_ctor_get(x_364, 0);
lean_inc(x_365);
lean_dec(x_364);
x_366 = l_Lean_PersistentEnvExtension_getState___rarg(x_362, x_365);
lean_dec(x_365);
lean_dec(x_362);
x_367 = lean_ctor_get(x_366, 1);
lean_inc(x_367);
lean_dec(x_366);
lean_inc(x_1);
x_368 = l_Lean_Syntax_getKind(x_1);
x_369 = l_Lean_SMap_find_x3f___at_Lean_Elab_Tactic_evalTactic___main___spec__1(x_367, x_368);
if (lean_obj_tag(x_369) == 0)
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; 
x_370 = l_Lean_Elab_Tactic_getCurrMacroScope(x_355, x_360);
x_371 = lean_ctor_get(x_370, 0);
lean_inc(x_371);
x_372 = lean_ctor_get(x_370, 1);
lean_inc(x_372);
lean_dec(x_370);
x_373 = l_Lean_Elab_Tactic_getEnv___rarg(x_372);
x_374 = lean_ctor_get(x_373, 0);
lean_inc(x_374);
x_375 = lean_ctor_get(x_373, 1);
lean_inc(x_375);
lean_dec(x_373);
lean_inc(x_1);
x_376 = l_Lean_Elab_expandMacro(x_374, x_1, x_371);
lean_dec(x_374);
if (lean_obj_tag(x_376) == 0)
{
lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; 
lean_dec(x_349);
lean_dec(x_340);
lean_dec(x_329);
lean_dec(x_328);
lean_dec(x_327);
lean_dec(x_326);
lean_dec(x_325);
lean_dec(x_324);
lean_dec(x_323);
lean_dec(x_322);
lean_dec(x_321);
lean_dec(x_320);
x_377 = l_Lean_Name_toString___closed__1;
x_378 = l_Lean_Name_toStringWithSep___main(x_377, x_368);
x_379 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_379, 0, x_378);
x_380 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_380, 0, x_379);
x_381 = l_Lean_Meta_Exception_toMessageData___closed__45;
x_382 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_382, 0, x_381);
lean_ctor_set(x_382, 1, x_380);
x_383 = l_Lean_Elab_Term_elabTermAux___main___closed__6;
x_384 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_384, 0, x_382);
lean_ctor_set(x_384, 1, x_383);
x_385 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_384, x_355, x_375);
return x_385;
}
else
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; 
lean_dec(x_368);
lean_dec(x_355);
x_386 = lean_ctor_get(x_376, 0);
lean_inc(x_386);
lean_dec(x_376);
x_387 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_387, 0, x_1);
lean_ctor_set(x_387, 1, x_329);
x_388 = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(x_388, 0, x_340);
lean_ctor_set(x_388, 1, x_322);
lean_ctor_set(x_388, 2, x_323);
lean_ctor_set(x_388, 3, x_324);
lean_ctor_set(x_388, 4, x_325);
lean_ctor_set(x_388, 5, x_326);
lean_ctor_set(x_388, 6, x_327);
lean_ctor_set(x_388, 7, x_328);
lean_ctor_set(x_388, 8, x_387);
lean_ctor_set(x_388, 9, x_349);
lean_ctor_set_uint8(x_388, sizeof(void*)*10, x_330);
x_389 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_389, 0, x_388);
lean_ctor_set(x_389, 1, x_320);
lean_ctor_set(x_389, 2, x_321);
x_1 = x_386;
x_2 = x_389;
x_3 = x_375;
goto _start;
}
}
else
{
lean_object* x_391; lean_object* x_392; 
lean_dec(x_368);
lean_dec(x_349);
lean_dec(x_340);
lean_dec(x_329);
lean_dec(x_328);
lean_dec(x_327);
lean_dec(x_326);
lean_dec(x_325);
lean_dec(x_324);
lean_dec(x_323);
lean_dec(x_322);
lean_dec(x_321);
lean_dec(x_320);
x_391 = lean_ctor_get(x_369, 0);
lean_inc(x_391);
lean_dec(x_369);
lean_inc(x_360);
x_392 = l___private_Init_Lean_Elab_Tactic_Basic_1__evalTacticUsing___main(x_360, x_1, x_391, x_355, x_360);
return x_392;
}
}
else
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; 
lean_dec(x_355);
lean_dec(x_349);
lean_dec(x_340);
lean_dec(x_329);
lean_dec(x_328);
lean_dec(x_327);
lean_dec(x_326);
lean_dec(x_325);
lean_dec(x_324);
lean_dec(x_323);
lean_dec(x_322);
lean_dec(x_321);
lean_dec(x_320);
lean_dec(x_1);
x_393 = lean_ctor_get(x_359, 0);
lean_inc(x_393);
x_394 = lean_ctor_get(x_359, 1);
lean_inc(x_394);
if (lean_is_exclusive(x_359)) {
 lean_ctor_release(x_359, 0);
 lean_ctor_release(x_359, 1);
 x_395 = x_359;
} else {
 lean_dec_ref(x_359);
 x_395 = lean_box(0);
}
if (lean_is_scalar(x_395)) {
 x_396 = lean_alloc_ctor(1, 2, 0);
} else {
 x_396 = x_395;
}
lean_ctor_set(x_396, 0, x_393);
lean_ctor_set(x_396, 1, x_394);
return x_396;
}
}
else
{
lean_object* x_397; lean_object* x_398; 
lean_dec(x_349);
lean_dec(x_340);
lean_dec(x_329);
lean_dec(x_328);
lean_dec(x_327);
lean_dec(x_326);
lean_dec(x_325);
lean_dec(x_324);
lean_dec(x_323);
lean_dec(x_322);
lean_dec(x_321);
lean_dec(x_320);
x_397 = l_Lean_Elab_Tactic_evalTactic___main___closed__3;
x_398 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_397, x_355, x_353);
return x_398;
}
}
}
}
}
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_Elab_Tactic_evalTactic___main___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_PersistentHashMap_findAtAux___main___at_Lean_Elab_Tactic_evalTactic___main___spec__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_PersistentHashMap_findAux___main___at_Lean_Elab_Tactic_evalTactic___main___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_PersistentHashMap_findAux___main___at_Lean_Elab_Tactic_evalTactic___main___spec__3(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_PersistentHashMap_find_x3f___at_Lean_Elab_Tactic_evalTactic___main___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PersistentHashMap_find_x3f___at_Lean_Elab_Tactic_evalTactic___main___spec__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_AssocList_find___main___at_Lean_Elab_Tactic_evalTactic___main___spec__6___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_AssocList_find___main___at_Lean_Elab_Tactic_evalTactic___main___spec__6(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_HashMapImp_find_x3f___at_Lean_Elab_Tactic_evalTactic___main___spec__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_HashMapImp_find_x3f___at_Lean_Elab_Tactic_evalTactic___main___spec__5(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_SMap_find_x3f___at_Lean_Elab_Tactic_evalTactic___main___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_SMap_find_x3f___at_Lean_Elab_Tactic_evalTactic___main___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Tactic_evalTactic___main___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Tactic_evalTactic___main___lambda__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Tactic_evalTactic(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Tactic_evalTactic___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Elab_Tactic_withLCtx___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_4, 0);
lean_dec(x_9);
x_10 = !lean_is_exclusive(x_6);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_6, 0);
lean_dec(x_11);
x_12 = !lean_is_exclusive(x_7);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_7, 2);
lean_dec(x_13);
x_14 = lean_ctor_get(x_7, 1);
lean_dec(x_14);
lean_ctor_set(x_7, 2, x_2);
lean_ctor_set(x_7, 1, x_1);
x_15 = lean_apply_2(x_3, x_4, x_5);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_7, 0);
x_17 = lean_ctor_get(x_7, 3);
x_18 = lean_ctor_get(x_7, 4);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_7);
x_19 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_1);
lean_ctor_set(x_19, 2, x_2);
lean_ctor_set(x_19, 3, x_17);
lean_ctor_set(x_19, 4, x_18);
lean_ctor_set(x_6, 0, x_19);
x_20 = lean_apply_2(x_3, x_4, x_5);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_21 = lean_ctor_get(x_6, 1);
x_22 = lean_ctor_get(x_6, 2);
x_23 = lean_ctor_get(x_6, 3);
x_24 = lean_ctor_get(x_6, 4);
x_25 = lean_ctor_get(x_6, 5);
x_26 = lean_ctor_get(x_6, 6);
x_27 = lean_ctor_get(x_6, 7);
x_28 = lean_ctor_get(x_6, 8);
x_29 = lean_ctor_get(x_6, 9);
x_30 = lean_ctor_get_uint8(x_6, sizeof(void*)*10);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_6);
x_31 = lean_ctor_get(x_7, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_7, 3);
lean_inc(x_32);
x_33 = lean_ctor_get(x_7, 4);
lean_inc(x_33);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 lean_ctor_release(x_7, 2);
 lean_ctor_release(x_7, 3);
 lean_ctor_release(x_7, 4);
 x_34 = x_7;
} else {
 lean_dec_ref(x_7);
 x_34 = lean_box(0);
}
if (lean_is_scalar(x_34)) {
 x_35 = lean_alloc_ctor(0, 5, 0);
} else {
 x_35 = x_34;
}
lean_ctor_set(x_35, 0, x_31);
lean_ctor_set(x_35, 1, x_1);
lean_ctor_set(x_35, 2, x_2);
lean_ctor_set(x_35, 3, x_32);
lean_ctor_set(x_35, 4, x_33);
x_36 = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_21);
lean_ctor_set(x_36, 2, x_22);
lean_ctor_set(x_36, 3, x_23);
lean_ctor_set(x_36, 4, x_24);
lean_ctor_set(x_36, 5, x_25);
lean_ctor_set(x_36, 6, x_26);
lean_ctor_set(x_36, 7, x_27);
lean_ctor_set(x_36, 8, x_28);
lean_ctor_set(x_36, 9, x_29);
lean_ctor_set_uint8(x_36, sizeof(void*)*10, x_30);
lean_ctor_set(x_4, 0, x_36);
x_37 = lean_apply_2(x_3, x_4, x_5);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_38 = lean_ctor_get(x_4, 1);
x_39 = lean_ctor_get(x_4, 2);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_4);
x_40 = lean_ctor_get(x_6, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_6, 2);
lean_inc(x_41);
x_42 = lean_ctor_get(x_6, 3);
lean_inc(x_42);
x_43 = lean_ctor_get(x_6, 4);
lean_inc(x_43);
x_44 = lean_ctor_get(x_6, 5);
lean_inc(x_44);
x_45 = lean_ctor_get(x_6, 6);
lean_inc(x_45);
x_46 = lean_ctor_get(x_6, 7);
lean_inc(x_46);
x_47 = lean_ctor_get(x_6, 8);
lean_inc(x_47);
x_48 = lean_ctor_get(x_6, 9);
lean_inc(x_48);
x_49 = lean_ctor_get_uint8(x_6, sizeof(void*)*10);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 lean_ctor_release(x_6, 4);
 lean_ctor_release(x_6, 5);
 lean_ctor_release(x_6, 6);
 lean_ctor_release(x_6, 7);
 lean_ctor_release(x_6, 8);
 lean_ctor_release(x_6, 9);
 x_50 = x_6;
} else {
 lean_dec_ref(x_6);
 x_50 = lean_box(0);
}
x_51 = lean_ctor_get(x_7, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_7, 3);
lean_inc(x_52);
x_53 = lean_ctor_get(x_7, 4);
lean_inc(x_53);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 lean_ctor_release(x_7, 2);
 lean_ctor_release(x_7, 3);
 lean_ctor_release(x_7, 4);
 x_54 = x_7;
} else {
 lean_dec_ref(x_7);
 x_54 = lean_box(0);
}
if (lean_is_scalar(x_54)) {
 x_55 = lean_alloc_ctor(0, 5, 0);
} else {
 x_55 = x_54;
}
lean_ctor_set(x_55, 0, x_51);
lean_ctor_set(x_55, 1, x_1);
lean_ctor_set(x_55, 2, x_2);
lean_ctor_set(x_55, 3, x_52);
lean_ctor_set(x_55, 4, x_53);
if (lean_is_scalar(x_50)) {
 x_56 = lean_alloc_ctor(0, 10, 1);
} else {
 x_56 = x_50;
}
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_40);
lean_ctor_set(x_56, 2, x_41);
lean_ctor_set(x_56, 3, x_42);
lean_ctor_set(x_56, 4, x_43);
lean_ctor_set(x_56, 5, x_44);
lean_ctor_set(x_56, 6, x_45);
lean_ctor_set(x_56, 7, x_46);
lean_ctor_set(x_56, 8, x_47);
lean_ctor_set(x_56, 9, x_48);
lean_ctor_set_uint8(x_56, sizeof(void*)*10, x_49);
x_57 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_38);
lean_ctor_set(x_57, 2, x_39);
x_58 = lean_apply_2(x_3, x_57, x_5);
return x_58;
}
}
}
lean_object* l_Lean_Elab_Tactic_withLCtx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withLCtx___rarg), 5, 0);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Tactic_resetSynthInstanceCache___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_resetSynthInstanceCache___boxed), 1, 0);
return x_1;
}
}
lean_object* l_Lean_Elab_Tactic_resetSynthInstanceCache(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Elab_Tactic_resetSynthInstanceCache___closed__1;
x_4 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_3, x_1, x_2);
return x_4;
}
}
lean_object* l_Lean_Elab_Tactic_resettingSynthInstanceCache___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_Elab_Tactic_resetSynthInstanceCache___closed__1;
lean_inc(x_2);
x_9 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_8, x_2, x_3);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_apply_2(x_1, x_2, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 2);
lean_inc(x_15);
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_11, 1);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_12);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_12, 0);
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_13);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_13, 0);
lean_dec(x_21);
x_22 = !lean_is_exclusive(x_14);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_14, 2);
lean_dec(x_23);
x_24 = !lean_is_exclusive(x_15);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_15, 2);
lean_dec(x_25);
lean_ctor_set(x_15, 2, x_7);
return x_11;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_15, 0);
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_15);
x_28 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set(x_28, 2, x_7);
lean_ctor_set(x_14, 2, x_28);
return x_11;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_29 = lean_ctor_get(x_14, 0);
x_30 = lean_ctor_get(x_14, 1);
x_31 = lean_ctor_get(x_14, 3);
x_32 = lean_ctor_get(x_14, 4);
x_33 = lean_ctor_get(x_14, 5);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_14);
x_34 = lean_ctor_get(x_15, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_15, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 lean_ctor_release(x_15, 2);
 x_36 = x_15;
} else {
 lean_dec_ref(x_15);
 x_36 = lean_box(0);
}
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(0, 3, 0);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_35);
lean_ctor_set(x_37, 2, x_7);
x_38 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_38, 0, x_29);
lean_ctor_set(x_38, 1, x_30);
lean_ctor_set(x_38, 2, x_37);
lean_ctor_set(x_38, 3, x_31);
lean_ctor_set(x_38, 4, x_32);
lean_ctor_set(x_38, 5, x_33);
lean_ctor_set(x_13, 0, x_38);
return x_11;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_39 = lean_ctor_get(x_13, 1);
x_40 = lean_ctor_get(x_13, 2);
x_41 = lean_ctor_get(x_13, 3);
x_42 = lean_ctor_get(x_13, 4);
x_43 = lean_ctor_get(x_13, 5);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_13);
x_44 = lean_ctor_get(x_14, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_14, 1);
lean_inc(x_45);
x_46 = lean_ctor_get(x_14, 3);
lean_inc(x_46);
x_47 = lean_ctor_get(x_14, 4);
lean_inc(x_47);
x_48 = lean_ctor_get(x_14, 5);
lean_inc(x_48);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 lean_ctor_release(x_14, 3);
 lean_ctor_release(x_14, 4);
 lean_ctor_release(x_14, 5);
 x_49 = x_14;
} else {
 lean_dec_ref(x_14);
 x_49 = lean_box(0);
}
x_50 = lean_ctor_get(x_15, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_15, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 lean_ctor_release(x_15, 2);
 x_52 = x_15;
} else {
 lean_dec_ref(x_15);
 x_52 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(0, 3, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_51);
lean_ctor_set(x_53, 2, x_7);
if (lean_is_scalar(x_49)) {
 x_54 = lean_alloc_ctor(0, 6, 0);
} else {
 x_54 = x_49;
}
lean_ctor_set(x_54, 0, x_44);
lean_ctor_set(x_54, 1, x_45);
lean_ctor_set(x_54, 2, x_53);
lean_ctor_set(x_54, 3, x_46);
lean_ctor_set(x_54, 4, x_47);
lean_ctor_set(x_54, 5, x_48);
x_55 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_39);
lean_ctor_set(x_55, 2, x_40);
lean_ctor_set(x_55, 3, x_41);
lean_ctor_set(x_55, 4, x_42);
lean_ctor_set(x_55, 5, x_43);
lean_ctor_set(x_12, 0, x_55);
return x_11;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_56 = lean_ctor_get(x_12, 1);
lean_inc(x_56);
lean_dec(x_12);
x_57 = lean_ctor_get(x_13, 1);
lean_inc(x_57);
x_58 = lean_ctor_get(x_13, 2);
lean_inc(x_58);
x_59 = lean_ctor_get(x_13, 3);
lean_inc(x_59);
x_60 = lean_ctor_get(x_13, 4);
lean_inc(x_60);
x_61 = lean_ctor_get(x_13, 5);
lean_inc(x_61);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 lean_ctor_release(x_13, 2);
 lean_ctor_release(x_13, 3);
 lean_ctor_release(x_13, 4);
 lean_ctor_release(x_13, 5);
 x_62 = x_13;
} else {
 lean_dec_ref(x_13);
 x_62 = lean_box(0);
}
x_63 = lean_ctor_get(x_14, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_14, 1);
lean_inc(x_64);
x_65 = lean_ctor_get(x_14, 3);
lean_inc(x_65);
x_66 = lean_ctor_get(x_14, 4);
lean_inc(x_66);
x_67 = lean_ctor_get(x_14, 5);
lean_inc(x_67);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 lean_ctor_release(x_14, 3);
 lean_ctor_release(x_14, 4);
 lean_ctor_release(x_14, 5);
 x_68 = x_14;
} else {
 lean_dec_ref(x_14);
 x_68 = lean_box(0);
}
x_69 = lean_ctor_get(x_15, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_15, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 lean_ctor_release(x_15, 2);
 x_71 = x_15;
} else {
 lean_dec_ref(x_15);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(0, 3, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_70);
lean_ctor_set(x_72, 2, x_7);
if (lean_is_scalar(x_68)) {
 x_73 = lean_alloc_ctor(0, 6, 0);
} else {
 x_73 = x_68;
}
lean_ctor_set(x_73, 0, x_63);
lean_ctor_set(x_73, 1, x_64);
lean_ctor_set(x_73, 2, x_72);
lean_ctor_set(x_73, 3, x_65);
lean_ctor_set(x_73, 4, x_66);
lean_ctor_set(x_73, 5, x_67);
if (lean_is_scalar(x_62)) {
 x_74 = lean_alloc_ctor(0, 6, 0);
} else {
 x_74 = x_62;
}
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_57);
lean_ctor_set(x_74, 2, x_58);
lean_ctor_set(x_74, 3, x_59);
lean_ctor_set(x_74, 4, x_60);
lean_ctor_set(x_74, 5, x_61);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_56);
lean_ctor_set(x_11, 1, x_75);
return x_11;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_76 = lean_ctor_get(x_11, 0);
lean_inc(x_76);
lean_dec(x_11);
x_77 = lean_ctor_get(x_12, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_78 = x_12;
} else {
 lean_dec_ref(x_12);
 x_78 = lean_box(0);
}
x_79 = lean_ctor_get(x_13, 1);
lean_inc(x_79);
x_80 = lean_ctor_get(x_13, 2);
lean_inc(x_80);
x_81 = lean_ctor_get(x_13, 3);
lean_inc(x_81);
x_82 = lean_ctor_get(x_13, 4);
lean_inc(x_82);
x_83 = lean_ctor_get(x_13, 5);
lean_inc(x_83);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 lean_ctor_release(x_13, 2);
 lean_ctor_release(x_13, 3);
 lean_ctor_release(x_13, 4);
 lean_ctor_release(x_13, 5);
 x_84 = x_13;
} else {
 lean_dec_ref(x_13);
 x_84 = lean_box(0);
}
x_85 = lean_ctor_get(x_14, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_14, 1);
lean_inc(x_86);
x_87 = lean_ctor_get(x_14, 3);
lean_inc(x_87);
x_88 = lean_ctor_get(x_14, 4);
lean_inc(x_88);
x_89 = lean_ctor_get(x_14, 5);
lean_inc(x_89);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 lean_ctor_release(x_14, 3);
 lean_ctor_release(x_14, 4);
 lean_ctor_release(x_14, 5);
 x_90 = x_14;
} else {
 lean_dec_ref(x_14);
 x_90 = lean_box(0);
}
x_91 = lean_ctor_get(x_15, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_15, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 lean_ctor_release(x_15, 2);
 x_93 = x_15;
} else {
 lean_dec_ref(x_15);
 x_93 = lean_box(0);
}
if (lean_is_scalar(x_93)) {
 x_94 = lean_alloc_ctor(0, 3, 0);
} else {
 x_94 = x_93;
}
lean_ctor_set(x_94, 0, x_91);
lean_ctor_set(x_94, 1, x_92);
lean_ctor_set(x_94, 2, x_7);
if (lean_is_scalar(x_90)) {
 x_95 = lean_alloc_ctor(0, 6, 0);
} else {
 x_95 = x_90;
}
lean_ctor_set(x_95, 0, x_85);
lean_ctor_set(x_95, 1, x_86);
lean_ctor_set(x_95, 2, x_94);
lean_ctor_set(x_95, 3, x_87);
lean_ctor_set(x_95, 4, x_88);
lean_ctor_set(x_95, 5, x_89);
if (lean_is_scalar(x_84)) {
 x_96 = lean_alloc_ctor(0, 6, 0);
} else {
 x_96 = x_84;
}
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_79);
lean_ctor_set(x_96, 2, x_80);
lean_ctor_set(x_96, 3, x_81);
lean_ctor_set(x_96, 4, x_82);
lean_ctor_set(x_96, 5, x_83);
if (lean_is_scalar(x_78)) {
 x_97 = lean_alloc_ctor(0, 2, 0);
} else {
 x_97 = x_78;
}
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_77);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_76);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_99 = lean_ctor_get(x_11, 1);
lean_inc(x_99);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_101, 2);
lean_inc(x_102);
x_103 = !lean_is_exclusive(x_11);
if (x_103 == 0)
{
lean_object* x_104; uint8_t x_105; 
x_104 = lean_ctor_get(x_11, 1);
lean_dec(x_104);
x_105 = !lean_is_exclusive(x_99);
if (x_105 == 0)
{
lean_object* x_106; uint8_t x_107; 
x_106 = lean_ctor_get(x_99, 0);
lean_dec(x_106);
x_107 = !lean_is_exclusive(x_100);
if (x_107 == 0)
{
lean_object* x_108; uint8_t x_109; 
x_108 = lean_ctor_get(x_100, 0);
lean_dec(x_108);
x_109 = !lean_is_exclusive(x_101);
if (x_109 == 0)
{
lean_object* x_110; uint8_t x_111; 
x_110 = lean_ctor_get(x_101, 2);
lean_dec(x_110);
x_111 = !lean_is_exclusive(x_102);
if (x_111 == 0)
{
lean_object* x_112; 
x_112 = lean_ctor_get(x_102, 2);
lean_dec(x_112);
lean_ctor_set(x_102, 2, x_7);
return x_11;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_102, 0);
x_114 = lean_ctor_get(x_102, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_102);
x_115 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
lean_ctor_set(x_115, 2, x_7);
lean_ctor_set(x_101, 2, x_115);
return x_11;
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_116 = lean_ctor_get(x_101, 0);
x_117 = lean_ctor_get(x_101, 1);
x_118 = lean_ctor_get(x_101, 3);
x_119 = lean_ctor_get(x_101, 4);
x_120 = lean_ctor_get(x_101, 5);
lean_inc(x_120);
lean_inc(x_119);
lean_inc(x_118);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_101);
x_121 = lean_ctor_get(x_102, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_102, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 lean_ctor_release(x_102, 2);
 x_123 = x_102;
} else {
 lean_dec_ref(x_102);
 x_123 = lean_box(0);
}
if (lean_is_scalar(x_123)) {
 x_124 = lean_alloc_ctor(0, 3, 0);
} else {
 x_124 = x_123;
}
lean_ctor_set(x_124, 0, x_121);
lean_ctor_set(x_124, 1, x_122);
lean_ctor_set(x_124, 2, x_7);
x_125 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_125, 0, x_116);
lean_ctor_set(x_125, 1, x_117);
lean_ctor_set(x_125, 2, x_124);
lean_ctor_set(x_125, 3, x_118);
lean_ctor_set(x_125, 4, x_119);
lean_ctor_set(x_125, 5, x_120);
lean_ctor_set(x_100, 0, x_125);
return x_11;
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_126 = lean_ctor_get(x_100, 1);
x_127 = lean_ctor_get(x_100, 2);
x_128 = lean_ctor_get(x_100, 3);
x_129 = lean_ctor_get(x_100, 4);
x_130 = lean_ctor_get(x_100, 5);
lean_inc(x_130);
lean_inc(x_129);
lean_inc(x_128);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_100);
x_131 = lean_ctor_get(x_101, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_101, 1);
lean_inc(x_132);
x_133 = lean_ctor_get(x_101, 3);
lean_inc(x_133);
x_134 = lean_ctor_get(x_101, 4);
lean_inc(x_134);
x_135 = lean_ctor_get(x_101, 5);
lean_inc(x_135);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 lean_ctor_release(x_101, 2);
 lean_ctor_release(x_101, 3);
 lean_ctor_release(x_101, 4);
 lean_ctor_release(x_101, 5);
 x_136 = x_101;
} else {
 lean_dec_ref(x_101);
 x_136 = lean_box(0);
}
x_137 = lean_ctor_get(x_102, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_102, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 lean_ctor_release(x_102, 2);
 x_139 = x_102;
} else {
 lean_dec_ref(x_102);
 x_139 = lean_box(0);
}
if (lean_is_scalar(x_139)) {
 x_140 = lean_alloc_ctor(0, 3, 0);
} else {
 x_140 = x_139;
}
lean_ctor_set(x_140, 0, x_137);
lean_ctor_set(x_140, 1, x_138);
lean_ctor_set(x_140, 2, x_7);
if (lean_is_scalar(x_136)) {
 x_141 = lean_alloc_ctor(0, 6, 0);
} else {
 x_141 = x_136;
}
lean_ctor_set(x_141, 0, x_131);
lean_ctor_set(x_141, 1, x_132);
lean_ctor_set(x_141, 2, x_140);
lean_ctor_set(x_141, 3, x_133);
lean_ctor_set(x_141, 4, x_134);
lean_ctor_set(x_141, 5, x_135);
x_142 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_126);
lean_ctor_set(x_142, 2, x_127);
lean_ctor_set(x_142, 3, x_128);
lean_ctor_set(x_142, 4, x_129);
lean_ctor_set(x_142, 5, x_130);
lean_ctor_set(x_99, 0, x_142);
return x_11;
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_143 = lean_ctor_get(x_99, 1);
lean_inc(x_143);
lean_dec(x_99);
x_144 = lean_ctor_get(x_100, 1);
lean_inc(x_144);
x_145 = lean_ctor_get(x_100, 2);
lean_inc(x_145);
x_146 = lean_ctor_get(x_100, 3);
lean_inc(x_146);
x_147 = lean_ctor_get(x_100, 4);
lean_inc(x_147);
x_148 = lean_ctor_get(x_100, 5);
lean_inc(x_148);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 lean_ctor_release(x_100, 2);
 lean_ctor_release(x_100, 3);
 lean_ctor_release(x_100, 4);
 lean_ctor_release(x_100, 5);
 x_149 = x_100;
} else {
 lean_dec_ref(x_100);
 x_149 = lean_box(0);
}
x_150 = lean_ctor_get(x_101, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_101, 1);
lean_inc(x_151);
x_152 = lean_ctor_get(x_101, 3);
lean_inc(x_152);
x_153 = lean_ctor_get(x_101, 4);
lean_inc(x_153);
x_154 = lean_ctor_get(x_101, 5);
lean_inc(x_154);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 lean_ctor_release(x_101, 2);
 lean_ctor_release(x_101, 3);
 lean_ctor_release(x_101, 4);
 lean_ctor_release(x_101, 5);
 x_155 = x_101;
} else {
 lean_dec_ref(x_101);
 x_155 = lean_box(0);
}
x_156 = lean_ctor_get(x_102, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_102, 1);
lean_inc(x_157);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 lean_ctor_release(x_102, 2);
 x_158 = x_102;
} else {
 lean_dec_ref(x_102);
 x_158 = lean_box(0);
}
if (lean_is_scalar(x_158)) {
 x_159 = lean_alloc_ctor(0, 3, 0);
} else {
 x_159 = x_158;
}
lean_ctor_set(x_159, 0, x_156);
lean_ctor_set(x_159, 1, x_157);
lean_ctor_set(x_159, 2, x_7);
if (lean_is_scalar(x_155)) {
 x_160 = lean_alloc_ctor(0, 6, 0);
} else {
 x_160 = x_155;
}
lean_ctor_set(x_160, 0, x_150);
lean_ctor_set(x_160, 1, x_151);
lean_ctor_set(x_160, 2, x_159);
lean_ctor_set(x_160, 3, x_152);
lean_ctor_set(x_160, 4, x_153);
lean_ctor_set(x_160, 5, x_154);
if (lean_is_scalar(x_149)) {
 x_161 = lean_alloc_ctor(0, 6, 0);
} else {
 x_161 = x_149;
}
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_144);
lean_ctor_set(x_161, 2, x_145);
lean_ctor_set(x_161, 3, x_146);
lean_ctor_set(x_161, 4, x_147);
lean_ctor_set(x_161, 5, x_148);
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_143);
lean_ctor_set(x_11, 1, x_162);
return x_11;
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_163 = lean_ctor_get(x_11, 0);
lean_inc(x_163);
lean_dec(x_11);
x_164 = lean_ctor_get(x_99, 1);
lean_inc(x_164);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_165 = x_99;
} else {
 lean_dec_ref(x_99);
 x_165 = lean_box(0);
}
x_166 = lean_ctor_get(x_100, 1);
lean_inc(x_166);
x_167 = lean_ctor_get(x_100, 2);
lean_inc(x_167);
x_168 = lean_ctor_get(x_100, 3);
lean_inc(x_168);
x_169 = lean_ctor_get(x_100, 4);
lean_inc(x_169);
x_170 = lean_ctor_get(x_100, 5);
lean_inc(x_170);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 lean_ctor_release(x_100, 2);
 lean_ctor_release(x_100, 3);
 lean_ctor_release(x_100, 4);
 lean_ctor_release(x_100, 5);
 x_171 = x_100;
} else {
 lean_dec_ref(x_100);
 x_171 = lean_box(0);
}
x_172 = lean_ctor_get(x_101, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_101, 1);
lean_inc(x_173);
x_174 = lean_ctor_get(x_101, 3);
lean_inc(x_174);
x_175 = lean_ctor_get(x_101, 4);
lean_inc(x_175);
x_176 = lean_ctor_get(x_101, 5);
lean_inc(x_176);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 lean_ctor_release(x_101, 2);
 lean_ctor_release(x_101, 3);
 lean_ctor_release(x_101, 4);
 lean_ctor_release(x_101, 5);
 x_177 = x_101;
} else {
 lean_dec_ref(x_101);
 x_177 = lean_box(0);
}
x_178 = lean_ctor_get(x_102, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_102, 1);
lean_inc(x_179);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 lean_ctor_release(x_102, 2);
 x_180 = x_102;
} else {
 lean_dec_ref(x_102);
 x_180 = lean_box(0);
}
if (lean_is_scalar(x_180)) {
 x_181 = lean_alloc_ctor(0, 3, 0);
} else {
 x_181 = x_180;
}
lean_ctor_set(x_181, 0, x_178);
lean_ctor_set(x_181, 1, x_179);
lean_ctor_set(x_181, 2, x_7);
if (lean_is_scalar(x_177)) {
 x_182 = lean_alloc_ctor(0, 6, 0);
} else {
 x_182 = x_177;
}
lean_ctor_set(x_182, 0, x_172);
lean_ctor_set(x_182, 1, x_173);
lean_ctor_set(x_182, 2, x_181);
lean_ctor_set(x_182, 3, x_174);
lean_ctor_set(x_182, 4, x_175);
lean_ctor_set(x_182, 5, x_176);
if (lean_is_scalar(x_171)) {
 x_183 = lean_alloc_ctor(0, 6, 0);
} else {
 x_183 = x_171;
}
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_166);
lean_ctor_set(x_183, 2, x_167);
lean_ctor_set(x_183, 3, x_168);
lean_ctor_set(x_183, 4, x_169);
lean_ctor_set(x_183, 5, x_170);
if (lean_is_scalar(x_165)) {
 x_184 = lean_alloc_ctor(0, 2, 0);
} else {
 x_184 = x_165;
}
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_164);
x_185 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_185, 0, x_163);
lean_ctor_set(x_185, 1, x_184);
return x_185;
}
}
}
else
{
uint8_t x_186; 
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_186 = !lean_is_exclusive(x_9);
if (x_186 == 0)
{
return x_9;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_187 = lean_ctor_get(x_9, 0);
x_188 = lean_ctor_get(x_9, 1);
lean_inc(x_188);
lean_inc(x_187);
lean_dec(x_9);
x_189 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_189, 0, x_187);
lean_ctor_set(x_189, 1, x_188);
return x_189;
}
}
}
}
lean_object* l_Lean_Elab_Tactic_resettingSynthInstanceCache(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_resettingSynthInstanceCache___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_resettingSynthInstanceCacheWhen___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (x_1 == 0)
{
lean_object* x_5; 
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_ctor_get(x_7, 2);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get(x_8, 2);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Lean_Elab_Tactic_resetSynthInstanceCache___closed__1;
lean_inc(x_3);
x_11 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_10, x_3, x_4);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_apply_2(x_2, x_3, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 2);
lean_inc(x_17);
x_18 = !lean_is_exclusive(x_13);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_13, 1);
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_14);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_14, 0);
lean_dec(x_21);
x_22 = !lean_is_exclusive(x_15);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_15, 0);
lean_dec(x_23);
x_24 = !lean_is_exclusive(x_16);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_16, 2);
lean_dec(x_25);
x_26 = !lean_is_exclusive(x_17);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_17, 2);
lean_dec(x_27);
lean_ctor_set(x_17, 2, x_9);
return x_13;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_17, 0);
x_29 = lean_ctor_get(x_17, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_17);
x_30 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set(x_30, 2, x_9);
lean_ctor_set(x_16, 2, x_30);
return x_13;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_31 = lean_ctor_get(x_16, 0);
x_32 = lean_ctor_get(x_16, 1);
x_33 = lean_ctor_get(x_16, 3);
x_34 = lean_ctor_get(x_16, 4);
x_35 = lean_ctor_get(x_16, 5);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_16);
x_36 = lean_ctor_get(x_17, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_17, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 lean_ctor_release(x_17, 2);
 x_38 = x_17;
} else {
 lean_dec_ref(x_17);
 x_38 = lean_box(0);
}
if (lean_is_scalar(x_38)) {
 x_39 = lean_alloc_ctor(0, 3, 0);
} else {
 x_39 = x_38;
}
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_37);
lean_ctor_set(x_39, 2, x_9);
x_40 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_40, 0, x_31);
lean_ctor_set(x_40, 1, x_32);
lean_ctor_set(x_40, 2, x_39);
lean_ctor_set(x_40, 3, x_33);
lean_ctor_set(x_40, 4, x_34);
lean_ctor_set(x_40, 5, x_35);
lean_ctor_set(x_15, 0, x_40);
return x_13;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_41 = lean_ctor_get(x_15, 1);
x_42 = lean_ctor_get(x_15, 2);
x_43 = lean_ctor_get(x_15, 3);
x_44 = lean_ctor_get(x_15, 4);
x_45 = lean_ctor_get(x_15, 5);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_15);
x_46 = lean_ctor_get(x_16, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_16, 1);
lean_inc(x_47);
x_48 = lean_ctor_get(x_16, 3);
lean_inc(x_48);
x_49 = lean_ctor_get(x_16, 4);
lean_inc(x_49);
x_50 = lean_ctor_get(x_16, 5);
lean_inc(x_50);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 lean_ctor_release(x_16, 2);
 lean_ctor_release(x_16, 3);
 lean_ctor_release(x_16, 4);
 lean_ctor_release(x_16, 5);
 x_51 = x_16;
} else {
 lean_dec_ref(x_16);
 x_51 = lean_box(0);
}
x_52 = lean_ctor_get(x_17, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_17, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 lean_ctor_release(x_17, 2);
 x_54 = x_17;
} else {
 lean_dec_ref(x_17);
 x_54 = lean_box(0);
}
if (lean_is_scalar(x_54)) {
 x_55 = lean_alloc_ctor(0, 3, 0);
} else {
 x_55 = x_54;
}
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_53);
lean_ctor_set(x_55, 2, x_9);
if (lean_is_scalar(x_51)) {
 x_56 = lean_alloc_ctor(0, 6, 0);
} else {
 x_56 = x_51;
}
lean_ctor_set(x_56, 0, x_46);
lean_ctor_set(x_56, 1, x_47);
lean_ctor_set(x_56, 2, x_55);
lean_ctor_set(x_56, 3, x_48);
lean_ctor_set(x_56, 4, x_49);
lean_ctor_set(x_56, 5, x_50);
x_57 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_41);
lean_ctor_set(x_57, 2, x_42);
lean_ctor_set(x_57, 3, x_43);
lean_ctor_set(x_57, 4, x_44);
lean_ctor_set(x_57, 5, x_45);
lean_ctor_set(x_14, 0, x_57);
return x_13;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_58 = lean_ctor_get(x_14, 1);
lean_inc(x_58);
lean_dec(x_14);
x_59 = lean_ctor_get(x_15, 1);
lean_inc(x_59);
x_60 = lean_ctor_get(x_15, 2);
lean_inc(x_60);
x_61 = lean_ctor_get(x_15, 3);
lean_inc(x_61);
x_62 = lean_ctor_get(x_15, 4);
lean_inc(x_62);
x_63 = lean_ctor_get(x_15, 5);
lean_inc(x_63);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 lean_ctor_release(x_15, 2);
 lean_ctor_release(x_15, 3);
 lean_ctor_release(x_15, 4);
 lean_ctor_release(x_15, 5);
 x_64 = x_15;
} else {
 lean_dec_ref(x_15);
 x_64 = lean_box(0);
}
x_65 = lean_ctor_get(x_16, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_16, 1);
lean_inc(x_66);
x_67 = lean_ctor_get(x_16, 3);
lean_inc(x_67);
x_68 = lean_ctor_get(x_16, 4);
lean_inc(x_68);
x_69 = lean_ctor_get(x_16, 5);
lean_inc(x_69);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 lean_ctor_release(x_16, 2);
 lean_ctor_release(x_16, 3);
 lean_ctor_release(x_16, 4);
 lean_ctor_release(x_16, 5);
 x_70 = x_16;
} else {
 lean_dec_ref(x_16);
 x_70 = lean_box(0);
}
x_71 = lean_ctor_get(x_17, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_17, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 lean_ctor_release(x_17, 2);
 x_73 = x_17;
} else {
 lean_dec_ref(x_17);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(0, 3, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_72);
lean_ctor_set(x_74, 2, x_9);
if (lean_is_scalar(x_70)) {
 x_75 = lean_alloc_ctor(0, 6, 0);
} else {
 x_75 = x_70;
}
lean_ctor_set(x_75, 0, x_65);
lean_ctor_set(x_75, 1, x_66);
lean_ctor_set(x_75, 2, x_74);
lean_ctor_set(x_75, 3, x_67);
lean_ctor_set(x_75, 4, x_68);
lean_ctor_set(x_75, 5, x_69);
if (lean_is_scalar(x_64)) {
 x_76 = lean_alloc_ctor(0, 6, 0);
} else {
 x_76 = x_64;
}
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_59);
lean_ctor_set(x_76, 2, x_60);
lean_ctor_set(x_76, 3, x_61);
lean_ctor_set(x_76, 4, x_62);
lean_ctor_set(x_76, 5, x_63);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_58);
lean_ctor_set(x_13, 1, x_77);
return x_13;
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_78 = lean_ctor_get(x_13, 0);
lean_inc(x_78);
lean_dec(x_13);
x_79 = lean_ctor_get(x_14, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_80 = x_14;
} else {
 lean_dec_ref(x_14);
 x_80 = lean_box(0);
}
x_81 = lean_ctor_get(x_15, 1);
lean_inc(x_81);
x_82 = lean_ctor_get(x_15, 2);
lean_inc(x_82);
x_83 = lean_ctor_get(x_15, 3);
lean_inc(x_83);
x_84 = lean_ctor_get(x_15, 4);
lean_inc(x_84);
x_85 = lean_ctor_get(x_15, 5);
lean_inc(x_85);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 lean_ctor_release(x_15, 2);
 lean_ctor_release(x_15, 3);
 lean_ctor_release(x_15, 4);
 lean_ctor_release(x_15, 5);
 x_86 = x_15;
} else {
 lean_dec_ref(x_15);
 x_86 = lean_box(0);
}
x_87 = lean_ctor_get(x_16, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_16, 1);
lean_inc(x_88);
x_89 = lean_ctor_get(x_16, 3);
lean_inc(x_89);
x_90 = lean_ctor_get(x_16, 4);
lean_inc(x_90);
x_91 = lean_ctor_get(x_16, 5);
lean_inc(x_91);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 lean_ctor_release(x_16, 2);
 lean_ctor_release(x_16, 3);
 lean_ctor_release(x_16, 4);
 lean_ctor_release(x_16, 5);
 x_92 = x_16;
} else {
 lean_dec_ref(x_16);
 x_92 = lean_box(0);
}
x_93 = lean_ctor_get(x_17, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_17, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 lean_ctor_release(x_17, 2);
 x_95 = x_17;
} else {
 lean_dec_ref(x_17);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(0, 3, 0);
} else {
 x_96 = x_95;
}
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_94);
lean_ctor_set(x_96, 2, x_9);
if (lean_is_scalar(x_92)) {
 x_97 = lean_alloc_ctor(0, 6, 0);
} else {
 x_97 = x_92;
}
lean_ctor_set(x_97, 0, x_87);
lean_ctor_set(x_97, 1, x_88);
lean_ctor_set(x_97, 2, x_96);
lean_ctor_set(x_97, 3, x_89);
lean_ctor_set(x_97, 4, x_90);
lean_ctor_set(x_97, 5, x_91);
if (lean_is_scalar(x_86)) {
 x_98 = lean_alloc_ctor(0, 6, 0);
} else {
 x_98 = x_86;
}
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_81);
lean_ctor_set(x_98, 2, x_82);
lean_ctor_set(x_98, 3, x_83);
lean_ctor_set(x_98, 4, x_84);
lean_ctor_set(x_98, 5, x_85);
if (lean_is_scalar(x_80)) {
 x_99 = lean_alloc_ctor(0, 2, 0);
} else {
 x_99 = x_80;
}
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_79);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_78);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; 
x_101 = lean_ctor_get(x_13, 1);
lean_inc(x_101);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_103, 2);
lean_inc(x_104);
x_105 = !lean_is_exclusive(x_13);
if (x_105 == 0)
{
lean_object* x_106; uint8_t x_107; 
x_106 = lean_ctor_get(x_13, 1);
lean_dec(x_106);
x_107 = !lean_is_exclusive(x_101);
if (x_107 == 0)
{
lean_object* x_108; uint8_t x_109; 
x_108 = lean_ctor_get(x_101, 0);
lean_dec(x_108);
x_109 = !lean_is_exclusive(x_102);
if (x_109 == 0)
{
lean_object* x_110; uint8_t x_111; 
x_110 = lean_ctor_get(x_102, 0);
lean_dec(x_110);
x_111 = !lean_is_exclusive(x_103);
if (x_111 == 0)
{
lean_object* x_112; uint8_t x_113; 
x_112 = lean_ctor_get(x_103, 2);
lean_dec(x_112);
x_113 = !lean_is_exclusive(x_104);
if (x_113 == 0)
{
lean_object* x_114; 
x_114 = lean_ctor_get(x_104, 2);
lean_dec(x_114);
lean_ctor_set(x_104, 2, x_9);
return x_13;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_104, 0);
x_116 = lean_ctor_get(x_104, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_104);
x_117 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
lean_ctor_set(x_117, 2, x_9);
lean_ctor_set(x_103, 2, x_117);
return x_13;
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_118 = lean_ctor_get(x_103, 0);
x_119 = lean_ctor_get(x_103, 1);
x_120 = lean_ctor_get(x_103, 3);
x_121 = lean_ctor_get(x_103, 4);
x_122 = lean_ctor_get(x_103, 5);
lean_inc(x_122);
lean_inc(x_121);
lean_inc(x_120);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_103);
x_123 = lean_ctor_get(x_104, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_104, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 lean_ctor_release(x_104, 2);
 x_125 = x_104;
} else {
 lean_dec_ref(x_104);
 x_125 = lean_box(0);
}
if (lean_is_scalar(x_125)) {
 x_126 = lean_alloc_ctor(0, 3, 0);
} else {
 x_126 = x_125;
}
lean_ctor_set(x_126, 0, x_123);
lean_ctor_set(x_126, 1, x_124);
lean_ctor_set(x_126, 2, x_9);
x_127 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_127, 0, x_118);
lean_ctor_set(x_127, 1, x_119);
lean_ctor_set(x_127, 2, x_126);
lean_ctor_set(x_127, 3, x_120);
lean_ctor_set(x_127, 4, x_121);
lean_ctor_set(x_127, 5, x_122);
lean_ctor_set(x_102, 0, x_127);
return x_13;
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_128 = lean_ctor_get(x_102, 1);
x_129 = lean_ctor_get(x_102, 2);
x_130 = lean_ctor_get(x_102, 3);
x_131 = lean_ctor_get(x_102, 4);
x_132 = lean_ctor_get(x_102, 5);
lean_inc(x_132);
lean_inc(x_131);
lean_inc(x_130);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_102);
x_133 = lean_ctor_get(x_103, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_103, 1);
lean_inc(x_134);
x_135 = lean_ctor_get(x_103, 3);
lean_inc(x_135);
x_136 = lean_ctor_get(x_103, 4);
lean_inc(x_136);
x_137 = lean_ctor_get(x_103, 5);
lean_inc(x_137);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 lean_ctor_release(x_103, 2);
 lean_ctor_release(x_103, 3);
 lean_ctor_release(x_103, 4);
 lean_ctor_release(x_103, 5);
 x_138 = x_103;
} else {
 lean_dec_ref(x_103);
 x_138 = lean_box(0);
}
x_139 = lean_ctor_get(x_104, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_104, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 lean_ctor_release(x_104, 2);
 x_141 = x_104;
} else {
 lean_dec_ref(x_104);
 x_141 = lean_box(0);
}
if (lean_is_scalar(x_141)) {
 x_142 = lean_alloc_ctor(0, 3, 0);
} else {
 x_142 = x_141;
}
lean_ctor_set(x_142, 0, x_139);
lean_ctor_set(x_142, 1, x_140);
lean_ctor_set(x_142, 2, x_9);
if (lean_is_scalar(x_138)) {
 x_143 = lean_alloc_ctor(0, 6, 0);
} else {
 x_143 = x_138;
}
lean_ctor_set(x_143, 0, x_133);
lean_ctor_set(x_143, 1, x_134);
lean_ctor_set(x_143, 2, x_142);
lean_ctor_set(x_143, 3, x_135);
lean_ctor_set(x_143, 4, x_136);
lean_ctor_set(x_143, 5, x_137);
x_144 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_128);
lean_ctor_set(x_144, 2, x_129);
lean_ctor_set(x_144, 3, x_130);
lean_ctor_set(x_144, 4, x_131);
lean_ctor_set(x_144, 5, x_132);
lean_ctor_set(x_101, 0, x_144);
return x_13;
}
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_145 = lean_ctor_get(x_101, 1);
lean_inc(x_145);
lean_dec(x_101);
x_146 = lean_ctor_get(x_102, 1);
lean_inc(x_146);
x_147 = lean_ctor_get(x_102, 2);
lean_inc(x_147);
x_148 = lean_ctor_get(x_102, 3);
lean_inc(x_148);
x_149 = lean_ctor_get(x_102, 4);
lean_inc(x_149);
x_150 = lean_ctor_get(x_102, 5);
lean_inc(x_150);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 lean_ctor_release(x_102, 2);
 lean_ctor_release(x_102, 3);
 lean_ctor_release(x_102, 4);
 lean_ctor_release(x_102, 5);
 x_151 = x_102;
} else {
 lean_dec_ref(x_102);
 x_151 = lean_box(0);
}
x_152 = lean_ctor_get(x_103, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_103, 1);
lean_inc(x_153);
x_154 = lean_ctor_get(x_103, 3);
lean_inc(x_154);
x_155 = lean_ctor_get(x_103, 4);
lean_inc(x_155);
x_156 = lean_ctor_get(x_103, 5);
lean_inc(x_156);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 lean_ctor_release(x_103, 2);
 lean_ctor_release(x_103, 3);
 lean_ctor_release(x_103, 4);
 lean_ctor_release(x_103, 5);
 x_157 = x_103;
} else {
 lean_dec_ref(x_103);
 x_157 = lean_box(0);
}
x_158 = lean_ctor_get(x_104, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_104, 1);
lean_inc(x_159);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 lean_ctor_release(x_104, 2);
 x_160 = x_104;
} else {
 lean_dec_ref(x_104);
 x_160 = lean_box(0);
}
if (lean_is_scalar(x_160)) {
 x_161 = lean_alloc_ctor(0, 3, 0);
} else {
 x_161 = x_160;
}
lean_ctor_set(x_161, 0, x_158);
lean_ctor_set(x_161, 1, x_159);
lean_ctor_set(x_161, 2, x_9);
if (lean_is_scalar(x_157)) {
 x_162 = lean_alloc_ctor(0, 6, 0);
} else {
 x_162 = x_157;
}
lean_ctor_set(x_162, 0, x_152);
lean_ctor_set(x_162, 1, x_153);
lean_ctor_set(x_162, 2, x_161);
lean_ctor_set(x_162, 3, x_154);
lean_ctor_set(x_162, 4, x_155);
lean_ctor_set(x_162, 5, x_156);
if (lean_is_scalar(x_151)) {
 x_163 = lean_alloc_ctor(0, 6, 0);
} else {
 x_163 = x_151;
}
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_146);
lean_ctor_set(x_163, 2, x_147);
lean_ctor_set(x_163, 3, x_148);
lean_ctor_set(x_163, 4, x_149);
lean_ctor_set(x_163, 5, x_150);
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_145);
lean_ctor_set(x_13, 1, x_164);
return x_13;
}
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_165 = lean_ctor_get(x_13, 0);
lean_inc(x_165);
lean_dec(x_13);
x_166 = lean_ctor_get(x_101, 1);
lean_inc(x_166);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_167 = x_101;
} else {
 lean_dec_ref(x_101);
 x_167 = lean_box(0);
}
x_168 = lean_ctor_get(x_102, 1);
lean_inc(x_168);
x_169 = lean_ctor_get(x_102, 2);
lean_inc(x_169);
x_170 = lean_ctor_get(x_102, 3);
lean_inc(x_170);
x_171 = lean_ctor_get(x_102, 4);
lean_inc(x_171);
x_172 = lean_ctor_get(x_102, 5);
lean_inc(x_172);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 lean_ctor_release(x_102, 2);
 lean_ctor_release(x_102, 3);
 lean_ctor_release(x_102, 4);
 lean_ctor_release(x_102, 5);
 x_173 = x_102;
} else {
 lean_dec_ref(x_102);
 x_173 = lean_box(0);
}
x_174 = lean_ctor_get(x_103, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_103, 1);
lean_inc(x_175);
x_176 = lean_ctor_get(x_103, 3);
lean_inc(x_176);
x_177 = lean_ctor_get(x_103, 4);
lean_inc(x_177);
x_178 = lean_ctor_get(x_103, 5);
lean_inc(x_178);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 lean_ctor_release(x_103, 2);
 lean_ctor_release(x_103, 3);
 lean_ctor_release(x_103, 4);
 lean_ctor_release(x_103, 5);
 x_179 = x_103;
} else {
 lean_dec_ref(x_103);
 x_179 = lean_box(0);
}
x_180 = lean_ctor_get(x_104, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_104, 1);
lean_inc(x_181);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 lean_ctor_release(x_104, 2);
 x_182 = x_104;
} else {
 lean_dec_ref(x_104);
 x_182 = lean_box(0);
}
if (lean_is_scalar(x_182)) {
 x_183 = lean_alloc_ctor(0, 3, 0);
} else {
 x_183 = x_182;
}
lean_ctor_set(x_183, 0, x_180);
lean_ctor_set(x_183, 1, x_181);
lean_ctor_set(x_183, 2, x_9);
if (lean_is_scalar(x_179)) {
 x_184 = lean_alloc_ctor(0, 6, 0);
} else {
 x_184 = x_179;
}
lean_ctor_set(x_184, 0, x_174);
lean_ctor_set(x_184, 1, x_175);
lean_ctor_set(x_184, 2, x_183);
lean_ctor_set(x_184, 3, x_176);
lean_ctor_set(x_184, 4, x_177);
lean_ctor_set(x_184, 5, x_178);
if (lean_is_scalar(x_173)) {
 x_185 = lean_alloc_ctor(0, 6, 0);
} else {
 x_185 = x_173;
}
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_168);
lean_ctor_set(x_185, 2, x_169);
lean_ctor_set(x_185, 3, x_170);
lean_ctor_set(x_185, 4, x_171);
lean_ctor_set(x_185, 5, x_172);
if (lean_is_scalar(x_167)) {
 x_186 = lean_alloc_ctor(0, 2, 0);
} else {
 x_186 = x_167;
}
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_166);
x_187 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_187, 0, x_165);
lean_ctor_set(x_187, 1, x_186);
return x_187;
}
}
}
else
{
uint8_t x_188; 
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_188 = !lean_is_exclusive(x_11);
if (x_188 == 0)
{
return x_11;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_189 = lean_ctor_get(x_11, 0);
x_190 = lean_ctor_get(x_11, 1);
lean_inc(x_190);
lean_inc(x_189);
lean_dec(x_11);
x_191 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_191, 0, x_189);
lean_ctor_set(x_191, 1, x_190);
return x_191;
}
}
}
}
}
lean_object* l_Lean_Elab_Tactic_resettingSynthInstanceCacheWhen(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_resettingSynthInstanceCacheWhen___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_resettingSynthInstanceCacheWhen___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l_Lean_Elab_Tactic_resettingSynthInstanceCacheWhen___rarg(x_5, x_2, x_3, x_4);
return x_6;
}
}
uint8_t l_Array_isEqvAux___main___at_Lean_Elab_Tactic_withMVarContext___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_12 = l_Lean_LocalInstance_beq(x_10, x_11);
lean_dec(x_11);
lean_dec(x_10);
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
lean_object* l_Lean_Elab_Tactic_withMVarContext___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_5 = l_Lean_Elab_Tactic_getMVarDecl(x_1, x_3, x_4);
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
lean_dec(x_5);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_3, 2);
lean_inc(x_11);
x_12 = !lean_is_exclusive(x_6);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_6, 0);
lean_dec(x_13);
x_14 = !lean_is_exclusive(x_7);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_15 = lean_ctor_get(x_7, 2);
x_16 = lean_ctor_get(x_7, 1);
lean_dec(x_16);
x_17 = lean_ctor_get(x_8, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_8, 4);
lean_inc(x_18);
x_19 = lean_array_get_size(x_15);
x_20 = lean_array_get_size(x_18);
x_21 = lean_nat_dec_eq(x_19, x_20);
lean_dec(x_20);
lean_dec(x_19);
lean_inc(x_18);
lean_ctor_set(x_7, 2, x_18);
lean_ctor_set(x_7, 1, x_17);
x_22 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_22, 0, x_6);
lean_ctor_set(x_22, 1, x_10);
lean_ctor_set(x_22, 2, x_11);
if (x_21 == 0)
{
lean_object* x_23; 
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_8);
lean_dec(x_3);
x_23 = lean_apply_2(x_2, x_22, x_9);
return x_23;
}
else
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_unsigned_to_nat(0u);
x_25 = l_Array_isEqvAux___main___at_Lean_Elab_Tactic_withMVarContext___spec__1(x_3, x_8, lean_box(0), x_15, x_18, x_24);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_8);
lean_dec(x_3);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_apply_2(x_2, x_22, x_9);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_27 = lean_ctor_get(x_9, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_ctor_get(x_28, 2);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_ctor_get(x_29, 2);
lean_inc(x_30);
lean_dec(x_29);
x_31 = l_Lean_Elab_Tactic_resetSynthInstanceCache___closed__1;
lean_inc(x_22);
x_32 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_31, x_22, x_9);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_apply_2(x_2, x_22, x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_37, 2);
lean_inc(x_38);
x_39 = !lean_is_exclusive(x_34);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_34, 1);
lean_dec(x_40);
x_41 = !lean_is_exclusive(x_35);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_35, 0);
lean_dec(x_42);
x_43 = !lean_is_exclusive(x_36);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_36, 0);
lean_dec(x_44);
x_45 = !lean_is_exclusive(x_37);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_ctor_get(x_37, 2);
lean_dec(x_46);
x_47 = !lean_is_exclusive(x_38);
if (x_47 == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_38, 2);
lean_dec(x_48);
lean_ctor_set(x_38, 2, x_30);
return x_34;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_38, 0);
x_50 = lean_ctor_get(x_38, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_38);
x_51 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
lean_ctor_set(x_51, 2, x_30);
lean_ctor_set(x_37, 2, x_51);
return x_34;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_52 = lean_ctor_get(x_37, 0);
x_53 = lean_ctor_get(x_37, 1);
x_54 = lean_ctor_get(x_37, 3);
x_55 = lean_ctor_get(x_37, 4);
x_56 = lean_ctor_get(x_37, 5);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_37);
x_57 = lean_ctor_get(x_38, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_38, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 lean_ctor_release(x_38, 2);
 x_59 = x_38;
} else {
 lean_dec_ref(x_38);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(0, 3, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_58);
lean_ctor_set(x_60, 2, x_30);
x_61 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_61, 0, x_52);
lean_ctor_set(x_61, 1, x_53);
lean_ctor_set(x_61, 2, x_60);
lean_ctor_set(x_61, 3, x_54);
lean_ctor_set(x_61, 4, x_55);
lean_ctor_set(x_61, 5, x_56);
lean_ctor_set(x_36, 0, x_61);
return x_34;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_62 = lean_ctor_get(x_36, 1);
x_63 = lean_ctor_get(x_36, 2);
x_64 = lean_ctor_get(x_36, 3);
x_65 = lean_ctor_get(x_36, 4);
x_66 = lean_ctor_get(x_36, 5);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_36);
x_67 = lean_ctor_get(x_37, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_37, 1);
lean_inc(x_68);
x_69 = lean_ctor_get(x_37, 3);
lean_inc(x_69);
x_70 = lean_ctor_get(x_37, 4);
lean_inc(x_70);
x_71 = lean_ctor_get(x_37, 5);
lean_inc(x_71);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 lean_ctor_release(x_37, 2);
 lean_ctor_release(x_37, 3);
 lean_ctor_release(x_37, 4);
 lean_ctor_release(x_37, 5);
 x_72 = x_37;
} else {
 lean_dec_ref(x_37);
 x_72 = lean_box(0);
}
x_73 = lean_ctor_get(x_38, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_38, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 lean_ctor_release(x_38, 2);
 x_75 = x_38;
} else {
 lean_dec_ref(x_38);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(0, 3, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_74);
lean_ctor_set(x_76, 2, x_30);
if (lean_is_scalar(x_72)) {
 x_77 = lean_alloc_ctor(0, 6, 0);
} else {
 x_77 = x_72;
}
lean_ctor_set(x_77, 0, x_67);
lean_ctor_set(x_77, 1, x_68);
lean_ctor_set(x_77, 2, x_76);
lean_ctor_set(x_77, 3, x_69);
lean_ctor_set(x_77, 4, x_70);
lean_ctor_set(x_77, 5, x_71);
x_78 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_62);
lean_ctor_set(x_78, 2, x_63);
lean_ctor_set(x_78, 3, x_64);
lean_ctor_set(x_78, 4, x_65);
lean_ctor_set(x_78, 5, x_66);
lean_ctor_set(x_35, 0, x_78);
return x_34;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_79 = lean_ctor_get(x_35, 1);
lean_inc(x_79);
lean_dec(x_35);
x_80 = lean_ctor_get(x_36, 1);
lean_inc(x_80);
x_81 = lean_ctor_get(x_36, 2);
lean_inc(x_81);
x_82 = lean_ctor_get(x_36, 3);
lean_inc(x_82);
x_83 = lean_ctor_get(x_36, 4);
lean_inc(x_83);
x_84 = lean_ctor_get(x_36, 5);
lean_inc(x_84);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 lean_ctor_release(x_36, 2);
 lean_ctor_release(x_36, 3);
 lean_ctor_release(x_36, 4);
 lean_ctor_release(x_36, 5);
 x_85 = x_36;
} else {
 lean_dec_ref(x_36);
 x_85 = lean_box(0);
}
x_86 = lean_ctor_get(x_37, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_37, 1);
lean_inc(x_87);
x_88 = lean_ctor_get(x_37, 3);
lean_inc(x_88);
x_89 = lean_ctor_get(x_37, 4);
lean_inc(x_89);
x_90 = lean_ctor_get(x_37, 5);
lean_inc(x_90);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 lean_ctor_release(x_37, 2);
 lean_ctor_release(x_37, 3);
 lean_ctor_release(x_37, 4);
 lean_ctor_release(x_37, 5);
 x_91 = x_37;
} else {
 lean_dec_ref(x_37);
 x_91 = lean_box(0);
}
x_92 = lean_ctor_get(x_38, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_38, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 lean_ctor_release(x_38, 2);
 x_94 = x_38;
} else {
 lean_dec_ref(x_38);
 x_94 = lean_box(0);
}
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(0, 3, 0);
} else {
 x_95 = x_94;
}
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_93);
lean_ctor_set(x_95, 2, x_30);
if (lean_is_scalar(x_91)) {
 x_96 = lean_alloc_ctor(0, 6, 0);
} else {
 x_96 = x_91;
}
lean_ctor_set(x_96, 0, x_86);
lean_ctor_set(x_96, 1, x_87);
lean_ctor_set(x_96, 2, x_95);
lean_ctor_set(x_96, 3, x_88);
lean_ctor_set(x_96, 4, x_89);
lean_ctor_set(x_96, 5, x_90);
if (lean_is_scalar(x_85)) {
 x_97 = lean_alloc_ctor(0, 6, 0);
} else {
 x_97 = x_85;
}
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_80);
lean_ctor_set(x_97, 2, x_81);
lean_ctor_set(x_97, 3, x_82);
lean_ctor_set(x_97, 4, x_83);
lean_ctor_set(x_97, 5, x_84);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_79);
lean_ctor_set(x_34, 1, x_98);
return x_34;
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_99 = lean_ctor_get(x_34, 0);
lean_inc(x_99);
lean_dec(x_34);
x_100 = lean_ctor_get(x_35, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_101 = x_35;
} else {
 lean_dec_ref(x_35);
 x_101 = lean_box(0);
}
x_102 = lean_ctor_get(x_36, 1);
lean_inc(x_102);
x_103 = lean_ctor_get(x_36, 2);
lean_inc(x_103);
x_104 = lean_ctor_get(x_36, 3);
lean_inc(x_104);
x_105 = lean_ctor_get(x_36, 4);
lean_inc(x_105);
x_106 = lean_ctor_get(x_36, 5);
lean_inc(x_106);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 lean_ctor_release(x_36, 2);
 lean_ctor_release(x_36, 3);
 lean_ctor_release(x_36, 4);
 lean_ctor_release(x_36, 5);
 x_107 = x_36;
} else {
 lean_dec_ref(x_36);
 x_107 = lean_box(0);
}
x_108 = lean_ctor_get(x_37, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_37, 1);
lean_inc(x_109);
x_110 = lean_ctor_get(x_37, 3);
lean_inc(x_110);
x_111 = lean_ctor_get(x_37, 4);
lean_inc(x_111);
x_112 = lean_ctor_get(x_37, 5);
lean_inc(x_112);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 lean_ctor_release(x_37, 2);
 lean_ctor_release(x_37, 3);
 lean_ctor_release(x_37, 4);
 lean_ctor_release(x_37, 5);
 x_113 = x_37;
} else {
 lean_dec_ref(x_37);
 x_113 = lean_box(0);
}
x_114 = lean_ctor_get(x_38, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_38, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 lean_ctor_release(x_38, 2);
 x_116 = x_38;
} else {
 lean_dec_ref(x_38);
 x_116 = lean_box(0);
}
if (lean_is_scalar(x_116)) {
 x_117 = lean_alloc_ctor(0, 3, 0);
} else {
 x_117 = x_116;
}
lean_ctor_set(x_117, 0, x_114);
lean_ctor_set(x_117, 1, x_115);
lean_ctor_set(x_117, 2, x_30);
if (lean_is_scalar(x_113)) {
 x_118 = lean_alloc_ctor(0, 6, 0);
} else {
 x_118 = x_113;
}
lean_ctor_set(x_118, 0, x_108);
lean_ctor_set(x_118, 1, x_109);
lean_ctor_set(x_118, 2, x_117);
lean_ctor_set(x_118, 3, x_110);
lean_ctor_set(x_118, 4, x_111);
lean_ctor_set(x_118, 5, x_112);
if (lean_is_scalar(x_107)) {
 x_119 = lean_alloc_ctor(0, 6, 0);
} else {
 x_119 = x_107;
}
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_102);
lean_ctor_set(x_119, 2, x_103);
lean_ctor_set(x_119, 3, x_104);
lean_ctor_set(x_119, 4, x_105);
lean_ctor_set(x_119, 5, x_106);
if (lean_is_scalar(x_101)) {
 x_120 = lean_alloc_ctor(0, 2, 0);
} else {
 x_120 = x_101;
}
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_100);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_99);
lean_ctor_set(x_121, 1, x_120);
return x_121;
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
x_122 = lean_ctor_get(x_34, 1);
lean_inc(x_122);
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_124, 2);
lean_inc(x_125);
x_126 = !lean_is_exclusive(x_34);
if (x_126 == 0)
{
lean_object* x_127; uint8_t x_128; 
x_127 = lean_ctor_get(x_34, 1);
lean_dec(x_127);
x_128 = !lean_is_exclusive(x_122);
if (x_128 == 0)
{
lean_object* x_129; uint8_t x_130; 
x_129 = lean_ctor_get(x_122, 0);
lean_dec(x_129);
x_130 = !lean_is_exclusive(x_123);
if (x_130 == 0)
{
lean_object* x_131; uint8_t x_132; 
x_131 = lean_ctor_get(x_123, 0);
lean_dec(x_131);
x_132 = !lean_is_exclusive(x_124);
if (x_132 == 0)
{
lean_object* x_133; uint8_t x_134; 
x_133 = lean_ctor_get(x_124, 2);
lean_dec(x_133);
x_134 = !lean_is_exclusive(x_125);
if (x_134 == 0)
{
lean_object* x_135; 
x_135 = lean_ctor_get(x_125, 2);
lean_dec(x_135);
lean_ctor_set(x_125, 2, x_30);
return x_34;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_125, 0);
x_137 = lean_ctor_get(x_125, 1);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_125);
x_138 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
lean_ctor_set(x_138, 2, x_30);
lean_ctor_set(x_124, 2, x_138);
return x_34;
}
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_139 = lean_ctor_get(x_124, 0);
x_140 = lean_ctor_get(x_124, 1);
x_141 = lean_ctor_get(x_124, 3);
x_142 = lean_ctor_get(x_124, 4);
x_143 = lean_ctor_get(x_124, 5);
lean_inc(x_143);
lean_inc(x_142);
lean_inc(x_141);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_124);
x_144 = lean_ctor_get(x_125, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_125, 1);
lean_inc(x_145);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 lean_ctor_release(x_125, 2);
 x_146 = x_125;
} else {
 lean_dec_ref(x_125);
 x_146 = lean_box(0);
}
if (lean_is_scalar(x_146)) {
 x_147 = lean_alloc_ctor(0, 3, 0);
} else {
 x_147 = x_146;
}
lean_ctor_set(x_147, 0, x_144);
lean_ctor_set(x_147, 1, x_145);
lean_ctor_set(x_147, 2, x_30);
x_148 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_148, 0, x_139);
lean_ctor_set(x_148, 1, x_140);
lean_ctor_set(x_148, 2, x_147);
lean_ctor_set(x_148, 3, x_141);
lean_ctor_set(x_148, 4, x_142);
lean_ctor_set(x_148, 5, x_143);
lean_ctor_set(x_123, 0, x_148);
return x_34;
}
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_149 = lean_ctor_get(x_123, 1);
x_150 = lean_ctor_get(x_123, 2);
x_151 = lean_ctor_get(x_123, 3);
x_152 = lean_ctor_get(x_123, 4);
x_153 = lean_ctor_get(x_123, 5);
lean_inc(x_153);
lean_inc(x_152);
lean_inc(x_151);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_123);
x_154 = lean_ctor_get(x_124, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_124, 1);
lean_inc(x_155);
x_156 = lean_ctor_get(x_124, 3);
lean_inc(x_156);
x_157 = lean_ctor_get(x_124, 4);
lean_inc(x_157);
x_158 = lean_ctor_get(x_124, 5);
lean_inc(x_158);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 lean_ctor_release(x_124, 2);
 lean_ctor_release(x_124, 3);
 lean_ctor_release(x_124, 4);
 lean_ctor_release(x_124, 5);
 x_159 = x_124;
} else {
 lean_dec_ref(x_124);
 x_159 = lean_box(0);
}
x_160 = lean_ctor_get(x_125, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_125, 1);
lean_inc(x_161);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 lean_ctor_release(x_125, 2);
 x_162 = x_125;
} else {
 lean_dec_ref(x_125);
 x_162 = lean_box(0);
}
if (lean_is_scalar(x_162)) {
 x_163 = lean_alloc_ctor(0, 3, 0);
} else {
 x_163 = x_162;
}
lean_ctor_set(x_163, 0, x_160);
lean_ctor_set(x_163, 1, x_161);
lean_ctor_set(x_163, 2, x_30);
if (lean_is_scalar(x_159)) {
 x_164 = lean_alloc_ctor(0, 6, 0);
} else {
 x_164 = x_159;
}
lean_ctor_set(x_164, 0, x_154);
lean_ctor_set(x_164, 1, x_155);
lean_ctor_set(x_164, 2, x_163);
lean_ctor_set(x_164, 3, x_156);
lean_ctor_set(x_164, 4, x_157);
lean_ctor_set(x_164, 5, x_158);
x_165 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_149);
lean_ctor_set(x_165, 2, x_150);
lean_ctor_set(x_165, 3, x_151);
lean_ctor_set(x_165, 4, x_152);
lean_ctor_set(x_165, 5, x_153);
lean_ctor_set(x_122, 0, x_165);
return x_34;
}
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_166 = lean_ctor_get(x_122, 1);
lean_inc(x_166);
lean_dec(x_122);
x_167 = lean_ctor_get(x_123, 1);
lean_inc(x_167);
x_168 = lean_ctor_get(x_123, 2);
lean_inc(x_168);
x_169 = lean_ctor_get(x_123, 3);
lean_inc(x_169);
x_170 = lean_ctor_get(x_123, 4);
lean_inc(x_170);
x_171 = lean_ctor_get(x_123, 5);
lean_inc(x_171);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 lean_ctor_release(x_123, 2);
 lean_ctor_release(x_123, 3);
 lean_ctor_release(x_123, 4);
 lean_ctor_release(x_123, 5);
 x_172 = x_123;
} else {
 lean_dec_ref(x_123);
 x_172 = lean_box(0);
}
x_173 = lean_ctor_get(x_124, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_124, 1);
lean_inc(x_174);
x_175 = lean_ctor_get(x_124, 3);
lean_inc(x_175);
x_176 = lean_ctor_get(x_124, 4);
lean_inc(x_176);
x_177 = lean_ctor_get(x_124, 5);
lean_inc(x_177);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 lean_ctor_release(x_124, 2);
 lean_ctor_release(x_124, 3);
 lean_ctor_release(x_124, 4);
 lean_ctor_release(x_124, 5);
 x_178 = x_124;
} else {
 lean_dec_ref(x_124);
 x_178 = lean_box(0);
}
x_179 = lean_ctor_get(x_125, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_125, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 lean_ctor_release(x_125, 2);
 x_181 = x_125;
} else {
 lean_dec_ref(x_125);
 x_181 = lean_box(0);
}
if (lean_is_scalar(x_181)) {
 x_182 = lean_alloc_ctor(0, 3, 0);
} else {
 x_182 = x_181;
}
lean_ctor_set(x_182, 0, x_179);
lean_ctor_set(x_182, 1, x_180);
lean_ctor_set(x_182, 2, x_30);
if (lean_is_scalar(x_178)) {
 x_183 = lean_alloc_ctor(0, 6, 0);
} else {
 x_183 = x_178;
}
lean_ctor_set(x_183, 0, x_173);
lean_ctor_set(x_183, 1, x_174);
lean_ctor_set(x_183, 2, x_182);
lean_ctor_set(x_183, 3, x_175);
lean_ctor_set(x_183, 4, x_176);
lean_ctor_set(x_183, 5, x_177);
if (lean_is_scalar(x_172)) {
 x_184 = lean_alloc_ctor(0, 6, 0);
} else {
 x_184 = x_172;
}
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_167);
lean_ctor_set(x_184, 2, x_168);
lean_ctor_set(x_184, 3, x_169);
lean_ctor_set(x_184, 4, x_170);
lean_ctor_set(x_184, 5, x_171);
x_185 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_166);
lean_ctor_set(x_34, 1, x_185);
return x_34;
}
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_186 = lean_ctor_get(x_34, 0);
lean_inc(x_186);
lean_dec(x_34);
x_187 = lean_ctor_get(x_122, 1);
lean_inc(x_187);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_188 = x_122;
} else {
 lean_dec_ref(x_122);
 x_188 = lean_box(0);
}
x_189 = lean_ctor_get(x_123, 1);
lean_inc(x_189);
x_190 = lean_ctor_get(x_123, 2);
lean_inc(x_190);
x_191 = lean_ctor_get(x_123, 3);
lean_inc(x_191);
x_192 = lean_ctor_get(x_123, 4);
lean_inc(x_192);
x_193 = lean_ctor_get(x_123, 5);
lean_inc(x_193);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 lean_ctor_release(x_123, 2);
 lean_ctor_release(x_123, 3);
 lean_ctor_release(x_123, 4);
 lean_ctor_release(x_123, 5);
 x_194 = x_123;
} else {
 lean_dec_ref(x_123);
 x_194 = lean_box(0);
}
x_195 = lean_ctor_get(x_124, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_124, 1);
lean_inc(x_196);
x_197 = lean_ctor_get(x_124, 3);
lean_inc(x_197);
x_198 = lean_ctor_get(x_124, 4);
lean_inc(x_198);
x_199 = lean_ctor_get(x_124, 5);
lean_inc(x_199);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 lean_ctor_release(x_124, 2);
 lean_ctor_release(x_124, 3);
 lean_ctor_release(x_124, 4);
 lean_ctor_release(x_124, 5);
 x_200 = x_124;
} else {
 lean_dec_ref(x_124);
 x_200 = lean_box(0);
}
x_201 = lean_ctor_get(x_125, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_125, 1);
lean_inc(x_202);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 lean_ctor_release(x_125, 2);
 x_203 = x_125;
} else {
 lean_dec_ref(x_125);
 x_203 = lean_box(0);
}
if (lean_is_scalar(x_203)) {
 x_204 = lean_alloc_ctor(0, 3, 0);
} else {
 x_204 = x_203;
}
lean_ctor_set(x_204, 0, x_201);
lean_ctor_set(x_204, 1, x_202);
lean_ctor_set(x_204, 2, x_30);
if (lean_is_scalar(x_200)) {
 x_205 = lean_alloc_ctor(0, 6, 0);
} else {
 x_205 = x_200;
}
lean_ctor_set(x_205, 0, x_195);
lean_ctor_set(x_205, 1, x_196);
lean_ctor_set(x_205, 2, x_204);
lean_ctor_set(x_205, 3, x_197);
lean_ctor_set(x_205, 4, x_198);
lean_ctor_set(x_205, 5, x_199);
if (lean_is_scalar(x_194)) {
 x_206 = lean_alloc_ctor(0, 6, 0);
} else {
 x_206 = x_194;
}
lean_ctor_set(x_206, 0, x_205);
lean_ctor_set(x_206, 1, x_189);
lean_ctor_set(x_206, 2, x_190);
lean_ctor_set(x_206, 3, x_191);
lean_ctor_set(x_206, 4, x_192);
lean_ctor_set(x_206, 5, x_193);
if (lean_is_scalar(x_188)) {
 x_207 = lean_alloc_ctor(0, 2, 0);
} else {
 x_207 = x_188;
}
lean_ctor_set(x_207, 0, x_206);
lean_ctor_set(x_207, 1, x_187);
x_208 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_208, 0, x_186);
lean_ctor_set(x_208, 1, x_207);
return x_208;
}
}
}
else
{
uint8_t x_209; 
lean_dec(x_30);
lean_dec(x_22);
lean_dec(x_2);
x_209 = !lean_is_exclusive(x_32);
if (x_209 == 0)
{
return x_32;
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_210 = lean_ctor_get(x_32, 0);
x_211 = lean_ctor_get(x_32, 1);
lean_inc(x_211);
lean_inc(x_210);
lean_dec(x_32);
x_212 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_212, 0, x_210);
lean_ctor_set(x_212, 1, x_211);
return x_212;
}
}
}
}
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; uint8_t x_221; lean_object* x_222; lean_object* x_223; 
x_213 = lean_ctor_get(x_7, 0);
x_214 = lean_ctor_get(x_7, 2);
x_215 = lean_ctor_get(x_7, 3);
x_216 = lean_ctor_get(x_7, 4);
lean_inc(x_216);
lean_inc(x_215);
lean_inc(x_214);
lean_inc(x_213);
lean_dec(x_7);
x_217 = lean_ctor_get(x_8, 1);
lean_inc(x_217);
x_218 = lean_ctor_get(x_8, 4);
lean_inc(x_218);
x_219 = lean_array_get_size(x_214);
x_220 = lean_array_get_size(x_218);
x_221 = lean_nat_dec_eq(x_219, x_220);
lean_dec(x_220);
lean_dec(x_219);
lean_inc(x_218);
x_222 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_222, 0, x_213);
lean_ctor_set(x_222, 1, x_217);
lean_ctor_set(x_222, 2, x_218);
lean_ctor_set(x_222, 3, x_215);
lean_ctor_set(x_222, 4, x_216);
lean_ctor_set(x_6, 0, x_222);
x_223 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_223, 0, x_6);
lean_ctor_set(x_223, 1, x_10);
lean_ctor_set(x_223, 2, x_11);
if (x_221 == 0)
{
lean_object* x_224; 
lean_dec(x_218);
lean_dec(x_214);
lean_dec(x_8);
lean_dec(x_3);
x_224 = lean_apply_2(x_2, x_223, x_9);
return x_224;
}
else
{
lean_object* x_225; uint8_t x_226; 
x_225 = lean_unsigned_to_nat(0u);
x_226 = l_Array_isEqvAux___main___at_Lean_Elab_Tactic_withMVarContext___spec__1(x_3, x_8, lean_box(0), x_214, x_218, x_225);
lean_dec(x_218);
lean_dec(x_214);
lean_dec(x_8);
lean_dec(x_3);
if (x_226 == 0)
{
lean_object* x_227; 
x_227 = lean_apply_2(x_2, x_223, x_9);
return x_227;
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_228 = lean_ctor_get(x_9, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_228, 0);
lean_inc(x_229);
lean_dec(x_228);
x_230 = lean_ctor_get(x_229, 2);
lean_inc(x_230);
lean_dec(x_229);
x_231 = lean_ctor_get(x_230, 2);
lean_inc(x_231);
lean_dec(x_230);
x_232 = l_Lean_Elab_Tactic_resetSynthInstanceCache___closed__1;
lean_inc(x_223);
x_233 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_232, x_223, x_9);
if (lean_obj_tag(x_233) == 0)
{
lean_object* x_234; lean_object* x_235; 
x_234 = lean_ctor_get(x_233, 1);
lean_inc(x_234);
lean_dec(x_233);
x_235 = lean_apply_2(x_2, x_223, x_234);
if (lean_obj_tag(x_235) == 0)
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_236 = lean_ctor_get(x_235, 1);
lean_inc(x_236);
x_237 = lean_ctor_get(x_236, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_238, 2);
lean_inc(x_239);
x_240 = lean_ctor_get(x_235, 0);
lean_inc(x_240);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 lean_ctor_release(x_235, 1);
 x_241 = x_235;
} else {
 lean_dec_ref(x_235);
 x_241 = lean_box(0);
}
x_242 = lean_ctor_get(x_236, 1);
lean_inc(x_242);
if (lean_is_exclusive(x_236)) {
 lean_ctor_release(x_236, 0);
 lean_ctor_release(x_236, 1);
 x_243 = x_236;
} else {
 lean_dec_ref(x_236);
 x_243 = lean_box(0);
}
x_244 = lean_ctor_get(x_237, 1);
lean_inc(x_244);
x_245 = lean_ctor_get(x_237, 2);
lean_inc(x_245);
x_246 = lean_ctor_get(x_237, 3);
lean_inc(x_246);
x_247 = lean_ctor_get(x_237, 4);
lean_inc(x_247);
x_248 = lean_ctor_get(x_237, 5);
lean_inc(x_248);
if (lean_is_exclusive(x_237)) {
 lean_ctor_release(x_237, 0);
 lean_ctor_release(x_237, 1);
 lean_ctor_release(x_237, 2);
 lean_ctor_release(x_237, 3);
 lean_ctor_release(x_237, 4);
 lean_ctor_release(x_237, 5);
 x_249 = x_237;
} else {
 lean_dec_ref(x_237);
 x_249 = lean_box(0);
}
x_250 = lean_ctor_get(x_238, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_238, 1);
lean_inc(x_251);
x_252 = lean_ctor_get(x_238, 3);
lean_inc(x_252);
x_253 = lean_ctor_get(x_238, 4);
lean_inc(x_253);
x_254 = lean_ctor_get(x_238, 5);
lean_inc(x_254);
if (lean_is_exclusive(x_238)) {
 lean_ctor_release(x_238, 0);
 lean_ctor_release(x_238, 1);
 lean_ctor_release(x_238, 2);
 lean_ctor_release(x_238, 3);
 lean_ctor_release(x_238, 4);
 lean_ctor_release(x_238, 5);
 x_255 = x_238;
} else {
 lean_dec_ref(x_238);
 x_255 = lean_box(0);
}
x_256 = lean_ctor_get(x_239, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_239, 1);
lean_inc(x_257);
if (lean_is_exclusive(x_239)) {
 lean_ctor_release(x_239, 0);
 lean_ctor_release(x_239, 1);
 lean_ctor_release(x_239, 2);
 x_258 = x_239;
} else {
 lean_dec_ref(x_239);
 x_258 = lean_box(0);
}
if (lean_is_scalar(x_258)) {
 x_259 = lean_alloc_ctor(0, 3, 0);
} else {
 x_259 = x_258;
}
lean_ctor_set(x_259, 0, x_256);
lean_ctor_set(x_259, 1, x_257);
lean_ctor_set(x_259, 2, x_231);
if (lean_is_scalar(x_255)) {
 x_260 = lean_alloc_ctor(0, 6, 0);
} else {
 x_260 = x_255;
}
lean_ctor_set(x_260, 0, x_250);
lean_ctor_set(x_260, 1, x_251);
lean_ctor_set(x_260, 2, x_259);
lean_ctor_set(x_260, 3, x_252);
lean_ctor_set(x_260, 4, x_253);
lean_ctor_set(x_260, 5, x_254);
if (lean_is_scalar(x_249)) {
 x_261 = lean_alloc_ctor(0, 6, 0);
} else {
 x_261 = x_249;
}
lean_ctor_set(x_261, 0, x_260);
lean_ctor_set(x_261, 1, x_244);
lean_ctor_set(x_261, 2, x_245);
lean_ctor_set(x_261, 3, x_246);
lean_ctor_set(x_261, 4, x_247);
lean_ctor_set(x_261, 5, x_248);
if (lean_is_scalar(x_243)) {
 x_262 = lean_alloc_ctor(0, 2, 0);
} else {
 x_262 = x_243;
}
lean_ctor_set(x_262, 0, x_261);
lean_ctor_set(x_262, 1, x_242);
if (lean_is_scalar(x_241)) {
 x_263 = lean_alloc_ctor(0, 2, 0);
} else {
 x_263 = x_241;
}
lean_ctor_set(x_263, 0, x_240);
lean_ctor_set(x_263, 1, x_262);
return x_263;
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; 
x_264 = lean_ctor_get(x_235, 1);
lean_inc(x_264);
x_265 = lean_ctor_get(x_264, 0);
lean_inc(x_265);
x_266 = lean_ctor_get(x_265, 0);
lean_inc(x_266);
x_267 = lean_ctor_get(x_266, 2);
lean_inc(x_267);
x_268 = lean_ctor_get(x_235, 0);
lean_inc(x_268);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 lean_ctor_release(x_235, 1);
 x_269 = x_235;
} else {
 lean_dec_ref(x_235);
 x_269 = lean_box(0);
}
x_270 = lean_ctor_get(x_264, 1);
lean_inc(x_270);
if (lean_is_exclusive(x_264)) {
 lean_ctor_release(x_264, 0);
 lean_ctor_release(x_264, 1);
 x_271 = x_264;
} else {
 lean_dec_ref(x_264);
 x_271 = lean_box(0);
}
x_272 = lean_ctor_get(x_265, 1);
lean_inc(x_272);
x_273 = lean_ctor_get(x_265, 2);
lean_inc(x_273);
x_274 = lean_ctor_get(x_265, 3);
lean_inc(x_274);
x_275 = lean_ctor_get(x_265, 4);
lean_inc(x_275);
x_276 = lean_ctor_get(x_265, 5);
lean_inc(x_276);
if (lean_is_exclusive(x_265)) {
 lean_ctor_release(x_265, 0);
 lean_ctor_release(x_265, 1);
 lean_ctor_release(x_265, 2);
 lean_ctor_release(x_265, 3);
 lean_ctor_release(x_265, 4);
 lean_ctor_release(x_265, 5);
 x_277 = x_265;
} else {
 lean_dec_ref(x_265);
 x_277 = lean_box(0);
}
x_278 = lean_ctor_get(x_266, 0);
lean_inc(x_278);
x_279 = lean_ctor_get(x_266, 1);
lean_inc(x_279);
x_280 = lean_ctor_get(x_266, 3);
lean_inc(x_280);
x_281 = lean_ctor_get(x_266, 4);
lean_inc(x_281);
x_282 = lean_ctor_get(x_266, 5);
lean_inc(x_282);
if (lean_is_exclusive(x_266)) {
 lean_ctor_release(x_266, 0);
 lean_ctor_release(x_266, 1);
 lean_ctor_release(x_266, 2);
 lean_ctor_release(x_266, 3);
 lean_ctor_release(x_266, 4);
 lean_ctor_release(x_266, 5);
 x_283 = x_266;
} else {
 lean_dec_ref(x_266);
 x_283 = lean_box(0);
}
x_284 = lean_ctor_get(x_267, 0);
lean_inc(x_284);
x_285 = lean_ctor_get(x_267, 1);
lean_inc(x_285);
if (lean_is_exclusive(x_267)) {
 lean_ctor_release(x_267, 0);
 lean_ctor_release(x_267, 1);
 lean_ctor_release(x_267, 2);
 x_286 = x_267;
} else {
 lean_dec_ref(x_267);
 x_286 = lean_box(0);
}
if (lean_is_scalar(x_286)) {
 x_287 = lean_alloc_ctor(0, 3, 0);
} else {
 x_287 = x_286;
}
lean_ctor_set(x_287, 0, x_284);
lean_ctor_set(x_287, 1, x_285);
lean_ctor_set(x_287, 2, x_231);
if (lean_is_scalar(x_283)) {
 x_288 = lean_alloc_ctor(0, 6, 0);
} else {
 x_288 = x_283;
}
lean_ctor_set(x_288, 0, x_278);
lean_ctor_set(x_288, 1, x_279);
lean_ctor_set(x_288, 2, x_287);
lean_ctor_set(x_288, 3, x_280);
lean_ctor_set(x_288, 4, x_281);
lean_ctor_set(x_288, 5, x_282);
if (lean_is_scalar(x_277)) {
 x_289 = lean_alloc_ctor(0, 6, 0);
} else {
 x_289 = x_277;
}
lean_ctor_set(x_289, 0, x_288);
lean_ctor_set(x_289, 1, x_272);
lean_ctor_set(x_289, 2, x_273);
lean_ctor_set(x_289, 3, x_274);
lean_ctor_set(x_289, 4, x_275);
lean_ctor_set(x_289, 5, x_276);
if (lean_is_scalar(x_271)) {
 x_290 = lean_alloc_ctor(0, 2, 0);
} else {
 x_290 = x_271;
}
lean_ctor_set(x_290, 0, x_289);
lean_ctor_set(x_290, 1, x_270);
if (lean_is_scalar(x_269)) {
 x_291 = lean_alloc_ctor(1, 2, 0);
} else {
 x_291 = x_269;
}
lean_ctor_set(x_291, 0, x_268);
lean_ctor_set(x_291, 1, x_290);
return x_291;
}
}
else
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; 
lean_dec(x_231);
lean_dec(x_223);
lean_dec(x_2);
x_292 = lean_ctor_get(x_233, 0);
lean_inc(x_292);
x_293 = lean_ctor_get(x_233, 1);
lean_inc(x_293);
if (lean_is_exclusive(x_233)) {
 lean_ctor_release(x_233, 0);
 lean_ctor_release(x_233, 1);
 x_294 = x_233;
} else {
 lean_dec_ref(x_233);
 x_294 = lean_box(0);
}
if (lean_is_scalar(x_294)) {
 x_295 = lean_alloc_ctor(1, 2, 0);
} else {
 x_295 = x_294;
}
lean_ctor_set(x_295, 0, x_292);
lean_ctor_set(x_295, 1, x_293);
return x_295;
}
}
}
}
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; uint8_t x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; uint8_t x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; 
x_296 = lean_ctor_get(x_6, 1);
x_297 = lean_ctor_get(x_6, 2);
x_298 = lean_ctor_get(x_6, 3);
x_299 = lean_ctor_get(x_6, 4);
x_300 = lean_ctor_get(x_6, 5);
x_301 = lean_ctor_get(x_6, 6);
x_302 = lean_ctor_get(x_6, 7);
x_303 = lean_ctor_get(x_6, 8);
x_304 = lean_ctor_get(x_6, 9);
x_305 = lean_ctor_get_uint8(x_6, sizeof(void*)*10);
lean_inc(x_304);
lean_inc(x_303);
lean_inc(x_302);
lean_inc(x_301);
lean_inc(x_300);
lean_inc(x_299);
lean_inc(x_298);
lean_inc(x_297);
lean_inc(x_296);
lean_dec(x_6);
x_306 = lean_ctor_get(x_7, 0);
lean_inc(x_306);
x_307 = lean_ctor_get(x_7, 2);
lean_inc(x_307);
x_308 = lean_ctor_get(x_7, 3);
lean_inc(x_308);
x_309 = lean_ctor_get(x_7, 4);
lean_inc(x_309);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 lean_ctor_release(x_7, 2);
 lean_ctor_release(x_7, 3);
 lean_ctor_release(x_7, 4);
 x_310 = x_7;
} else {
 lean_dec_ref(x_7);
 x_310 = lean_box(0);
}
x_311 = lean_ctor_get(x_8, 1);
lean_inc(x_311);
x_312 = lean_ctor_get(x_8, 4);
lean_inc(x_312);
x_313 = lean_array_get_size(x_307);
x_314 = lean_array_get_size(x_312);
x_315 = lean_nat_dec_eq(x_313, x_314);
lean_dec(x_314);
lean_dec(x_313);
lean_inc(x_312);
if (lean_is_scalar(x_310)) {
 x_316 = lean_alloc_ctor(0, 5, 0);
} else {
 x_316 = x_310;
}
lean_ctor_set(x_316, 0, x_306);
lean_ctor_set(x_316, 1, x_311);
lean_ctor_set(x_316, 2, x_312);
lean_ctor_set(x_316, 3, x_308);
lean_ctor_set(x_316, 4, x_309);
x_317 = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(x_317, 0, x_316);
lean_ctor_set(x_317, 1, x_296);
lean_ctor_set(x_317, 2, x_297);
lean_ctor_set(x_317, 3, x_298);
lean_ctor_set(x_317, 4, x_299);
lean_ctor_set(x_317, 5, x_300);
lean_ctor_set(x_317, 6, x_301);
lean_ctor_set(x_317, 7, x_302);
lean_ctor_set(x_317, 8, x_303);
lean_ctor_set(x_317, 9, x_304);
lean_ctor_set_uint8(x_317, sizeof(void*)*10, x_305);
x_318 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_318, 0, x_317);
lean_ctor_set(x_318, 1, x_10);
lean_ctor_set(x_318, 2, x_11);
if (x_315 == 0)
{
lean_object* x_319; 
lean_dec(x_312);
lean_dec(x_307);
lean_dec(x_8);
lean_dec(x_3);
x_319 = lean_apply_2(x_2, x_318, x_9);
return x_319;
}
else
{
lean_object* x_320; uint8_t x_321; 
x_320 = lean_unsigned_to_nat(0u);
x_321 = l_Array_isEqvAux___main___at_Lean_Elab_Tactic_withMVarContext___spec__1(x_3, x_8, lean_box(0), x_307, x_312, x_320);
lean_dec(x_312);
lean_dec(x_307);
lean_dec(x_8);
lean_dec(x_3);
if (x_321 == 0)
{
lean_object* x_322; 
x_322 = lean_apply_2(x_2, x_318, x_9);
return x_322;
}
else
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; 
x_323 = lean_ctor_get(x_9, 0);
lean_inc(x_323);
x_324 = lean_ctor_get(x_323, 0);
lean_inc(x_324);
lean_dec(x_323);
x_325 = lean_ctor_get(x_324, 2);
lean_inc(x_325);
lean_dec(x_324);
x_326 = lean_ctor_get(x_325, 2);
lean_inc(x_326);
lean_dec(x_325);
x_327 = l_Lean_Elab_Tactic_resetSynthInstanceCache___closed__1;
lean_inc(x_318);
x_328 = l_Lean_Elab_Tactic_liftTermElabM___rarg(x_327, x_318, x_9);
if (lean_obj_tag(x_328) == 0)
{
lean_object* x_329; lean_object* x_330; 
x_329 = lean_ctor_get(x_328, 1);
lean_inc(x_329);
lean_dec(x_328);
x_330 = lean_apply_2(x_2, x_318, x_329);
if (lean_obj_tag(x_330) == 0)
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; 
x_331 = lean_ctor_get(x_330, 1);
lean_inc(x_331);
x_332 = lean_ctor_get(x_331, 0);
lean_inc(x_332);
x_333 = lean_ctor_get(x_332, 0);
lean_inc(x_333);
x_334 = lean_ctor_get(x_333, 2);
lean_inc(x_334);
x_335 = lean_ctor_get(x_330, 0);
lean_inc(x_335);
if (lean_is_exclusive(x_330)) {
 lean_ctor_release(x_330, 0);
 lean_ctor_release(x_330, 1);
 x_336 = x_330;
} else {
 lean_dec_ref(x_330);
 x_336 = lean_box(0);
}
x_337 = lean_ctor_get(x_331, 1);
lean_inc(x_337);
if (lean_is_exclusive(x_331)) {
 lean_ctor_release(x_331, 0);
 lean_ctor_release(x_331, 1);
 x_338 = x_331;
} else {
 lean_dec_ref(x_331);
 x_338 = lean_box(0);
}
x_339 = lean_ctor_get(x_332, 1);
lean_inc(x_339);
x_340 = lean_ctor_get(x_332, 2);
lean_inc(x_340);
x_341 = lean_ctor_get(x_332, 3);
lean_inc(x_341);
x_342 = lean_ctor_get(x_332, 4);
lean_inc(x_342);
x_343 = lean_ctor_get(x_332, 5);
lean_inc(x_343);
if (lean_is_exclusive(x_332)) {
 lean_ctor_release(x_332, 0);
 lean_ctor_release(x_332, 1);
 lean_ctor_release(x_332, 2);
 lean_ctor_release(x_332, 3);
 lean_ctor_release(x_332, 4);
 lean_ctor_release(x_332, 5);
 x_344 = x_332;
} else {
 lean_dec_ref(x_332);
 x_344 = lean_box(0);
}
x_345 = lean_ctor_get(x_333, 0);
lean_inc(x_345);
x_346 = lean_ctor_get(x_333, 1);
lean_inc(x_346);
x_347 = lean_ctor_get(x_333, 3);
lean_inc(x_347);
x_348 = lean_ctor_get(x_333, 4);
lean_inc(x_348);
x_349 = lean_ctor_get(x_333, 5);
lean_inc(x_349);
if (lean_is_exclusive(x_333)) {
 lean_ctor_release(x_333, 0);
 lean_ctor_release(x_333, 1);
 lean_ctor_release(x_333, 2);
 lean_ctor_release(x_333, 3);
 lean_ctor_release(x_333, 4);
 lean_ctor_release(x_333, 5);
 x_350 = x_333;
} else {
 lean_dec_ref(x_333);
 x_350 = lean_box(0);
}
x_351 = lean_ctor_get(x_334, 0);
lean_inc(x_351);
x_352 = lean_ctor_get(x_334, 1);
lean_inc(x_352);
if (lean_is_exclusive(x_334)) {
 lean_ctor_release(x_334, 0);
 lean_ctor_release(x_334, 1);
 lean_ctor_release(x_334, 2);
 x_353 = x_334;
} else {
 lean_dec_ref(x_334);
 x_353 = lean_box(0);
}
if (lean_is_scalar(x_353)) {
 x_354 = lean_alloc_ctor(0, 3, 0);
} else {
 x_354 = x_353;
}
lean_ctor_set(x_354, 0, x_351);
lean_ctor_set(x_354, 1, x_352);
lean_ctor_set(x_354, 2, x_326);
if (lean_is_scalar(x_350)) {
 x_355 = lean_alloc_ctor(0, 6, 0);
} else {
 x_355 = x_350;
}
lean_ctor_set(x_355, 0, x_345);
lean_ctor_set(x_355, 1, x_346);
lean_ctor_set(x_355, 2, x_354);
lean_ctor_set(x_355, 3, x_347);
lean_ctor_set(x_355, 4, x_348);
lean_ctor_set(x_355, 5, x_349);
if (lean_is_scalar(x_344)) {
 x_356 = lean_alloc_ctor(0, 6, 0);
} else {
 x_356 = x_344;
}
lean_ctor_set(x_356, 0, x_355);
lean_ctor_set(x_356, 1, x_339);
lean_ctor_set(x_356, 2, x_340);
lean_ctor_set(x_356, 3, x_341);
lean_ctor_set(x_356, 4, x_342);
lean_ctor_set(x_356, 5, x_343);
if (lean_is_scalar(x_338)) {
 x_357 = lean_alloc_ctor(0, 2, 0);
} else {
 x_357 = x_338;
}
lean_ctor_set(x_357, 0, x_356);
lean_ctor_set(x_357, 1, x_337);
if (lean_is_scalar(x_336)) {
 x_358 = lean_alloc_ctor(0, 2, 0);
} else {
 x_358 = x_336;
}
lean_ctor_set(x_358, 0, x_335);
lean_ctor_set(x_358, 1, x_357);
return x_358;
}
else
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; 
x_359 = lean_ctor_get(x_330, 1);
lean_inc(x_359);
x_360 = lean_ctor_get(x_359, 0);
lean_inc(x_360);
x_361 = lean_ctor_get(x_360, 0);
lean_inc(x_361);
x_362 = lean_ctor_get(x_361, 2);
lean_inc(x_362);
x_363 = lean_ctor_get(x_330, 0);
lean_inc(x_363);
if (lean_is_exclusive(x_330)) {
 lean_ctor_release(x_330, 0);
 lean_ctor_release(x_330, 1);
 x_364 = x_330;
} else {
 lean_dec_ref(x_330);
 x_364 = lean_box(0);
}
x_365 = lean_ctor_get(x_359, 1);
lean_inc(x_365);
if (lean_is_exclusive(x_359)) {
 lean_ctor_release(x_359, 0);
 lean_ctor_release(x_359, 1);
 x_366 = x_359;
} else {
 lean_dec_ref(x_359);
 x_366 = lean_box(0);
}
x_367 = lean_ctor_get(x_360, 1);
lean_inc(x_367);
x_368 = lean_ctor_get(x_360, 2);
lean_inc(x_368);
x_369 = lean_ctor_get(x_360, 3);
lean_inc(x_369);
x_370 = lean_ctor_get(x_360, 4);
lean_inc(x_370);
x_371 = lean_ctor_get(x_360, 5);
lean_inc(x_371);
if (lean_is_exclusive(x_360)) {
 lean_ctor_release(x_360, 0);
 lean_ctor_release(x_360, 1);
 lean_ctor_release(x_360, 2);
 lean_ctor_release(x_360, 3);
 lean_ctor_release(x_360, 4);
 lean_ctor_release(x_360, 5);
 x_372 = x_360;
} else {
 lean_dec_ref(x_360);
 x_372 = lean_box(0);
}
x_373 = lean_ctor_get(x_361, 0);
lean_inc(x_373);
x_374 = lean_ctor_get(x_361, 1);
lean_inc(x_374);
x_375 = lean_ctor_get(x_361, 3);
lean_inc(x_375);
x_376 = lean_ctor_get(x_361, 4);
lean_inc(x_376);
x_377 = lean_ctor_get(x_361, 5);
lean_inc(x_377);
if (lean_is_exclusive(x_361)) {
 lean_ctor_release(x_361, 0);
 lean_ctor_release(x_361, 1);
 lean_ctor_release(x_361, 2);
 lean_ctor_release(x_361, 3);
 lean_ctor_release(x_361, 4);
 lean_ctor_release(x_361, 5);
 x_378 = x_361;
} else {
 lean_dec_ref(x_361);
 x_378 = lean_box(0);
}
x_379 = lean_ctor_get(x_362, 0);
lean_inc(x_379);
x_380 = lean_ctor_get(x_362, 1);
lean_inc(x_380);
if (lean_is_exclusive(x_362)) {
 lean_ctor_release(x_362, 0);
 lean_ctor_release(x_362, 1);
 lean_ctor_release(x_362, 2);
 x_381 = x_362;
} else {
 lean_dec_ref(x_362);
 x_381 = lean_box(0);
}
if (lean_is_scalar(x_381)) {
 x_382 = lean_alloc_ctor(0, 3, 0);
} else {
 x_382 = x_381;
}
lean_ctor_set(x_382, 0, x_379);
lean_ctor_set(x_382, 1, x_380);
lean_ctor_set(x_382, 2, x_326);
if (lean_is_scalar(x_378)) {
 x_383 = lean_alloc_ctor(0, 6, 0);
} else {
 x_383 = x_378;
}
lean_ctor_set(x_383, 0, x_373);
lean_ctor_set(x_383, 1, x_374);
lean_ctor_set(x_383, 2, x_382);
lean_ctor_set(x_383, 3, x_375);
lean_ctor_set(x_383, 4, x_376);
lean_ctor_set(x_383, 5, x_377);
if (lean_is_scalar(x_372)) {
 x_384 = lean_alloc_ctor(0, 6, 0);
} else {
 x_384 = x_372;
}
lean_ctor_set(x_384, 0, x_383);
lean_ctor_set(x_384, 1, x_367);
lean_ctor_set(x_384, 2, x_368);
lean_ctor_set(x_384, 3, x_369);
lean_ctor_set(x_384, 4, x_370);
lean_ctor_set(x_384, 5, x_371);
if (lean_is_scalar(x_366)) {
 x_385 = lean_alloc_ctor(0, 2, 0);
} else {
 x_385 = x_366;
}
lean_ctor_set(x_385, 0, x_384);
lean_ctor_set(x_385, 1, x_365);
if (lean_is_scalar(x_364)) {
 x_386 = lean_alloc_ctor(1, 2, 0);
} else {
 x_386 = x_364;
}
lean_ctor_set(x_386, 0, x_363);
lean_ctor_set(x_386, 1, x_385);
return x_386;
}
}
else
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; 
lean_dec(x_326);
lean_dec(x_318);
lean_dec(x_2);
x_387 = lean_ctor_get(x_328, 0);
lean_inc(x_387);
x_388 = lean_ctor_get(x_328, 1);
lean_inc(x_388);
if (lean_is_exclusive(x_328)) {
 lean_ctor_release(x_328, 0);
 lean_ctor_release(x_328, 1);
 x_389 = x_328;
} else {
 lean_dec_ref(x_328);
 x_389 = lean_box(0);
}
if (lean_is_scalar(x_389)) {
 x_390 = lean_alloc_ctor(1, 2, 0);
} else {
 x_390 = x_389;
}
lean_ctor_set(x_390, 0, x_387);
lean_ctor_set(x_390, 1, x_388);
return x_390;
}
}
}
}
}
}
lean_object* l_Lean_Elab_Tactic_withMVarContext(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withMVarContext___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Array_isEqvAux___main___at_Lean_Elab_Tactic_withMVarContext___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Array_isEqvAux___main___at_Lean_Elab_Tactic_withMVarContext___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
lean_object* l_Lean_Elab_Tactic_withMVarContext___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Tactic_withMVarContext___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Tactic_liftMetaTactic___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_4, 1);
lean_dec(x_6);
x_7 = l_List_append___rarg(x_2, x_1);
lean_ctor_set(x_4, 1, x_7);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_4);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_4, 0);
lean_inc(x_10);
lean_dec(x_4);
x_11 = l_List_append___rarg(x_2, x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
}
lean_object* _init_l_Lean_Elab_Tactic_liftMetaTactic___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("no goals to be solved");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Tactic_liftMetaTactic___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_liftMetaTactic___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Tactic_liftMetaTactic___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_liftMetaTactic___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_liftMetaTactic(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = l_Lean_Elab_Tactic_liftMetaTactic___closed__3;
x_7 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_6, x_3, x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
lean_dec(x_5);
lean_inc(x_8);
x_10 = lean_apply_1(x_2, x_8);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaM___rarg), 4, 2);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_10);
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaTactic___lambda__1___boxed), 4, 1);
lean_closure_set(x_12, 0, x_9);
x_13 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_monadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_13, 0, x_11);
lean_closure_set(x_13, 1, x_12);
x_14 = l_Lean_Elab_Tactic_withMVarContext___rarg(x_8, x_13, x_3, x_4);
lean_dec(x_8);
return x_14;
}
}
}
lean_object* l_Lean_Elab_Tactic_liftMetaTactic___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Tactic_liftMetaTactic___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_Syntax_foldArgsAuxM___main___at_Lean_Elab_Tactic_evalSeq___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
x_10 = lean_array_fget(x_2, x_3);
lean_inc(x_5);
x_11 = l_Lean_Elab_Tactic_evalTactic___main(x_10, x_5, x_6);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_nat_add(x_3, x_1);
lean_dec(x_3);
x_3 = x_14;
x_4 = x_12;
x_6 = x_13;
goto _start;
}
else
{
uint8_t x_16; 
lean_dec(x_5);
lean_dec(x_3);
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_11, 0);
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_11);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
}
lean_object* l_Lean_Elab_Tactic_evalSeq(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_Syntax_getArg(x_1, x_4);
x_6 = l_Lean_Syntax_getArgs(x_5);
lean_dec(x_5);
x_7 = lean_unsigned_to_nat(2u);
x_8 = lean_box(0);
x_9 = l_Lean_Syntax_foldArgsAuxM___main___at_Lean_Elab_Tactic_evalSeq___spec__1(x_7, x_6, x_4, x_8, x_2, x_3);
lean_dec(x_6);
return x_9;
}
}
lean_object* l_Lean_Syntax_foldArgsAuxM___main___at_Lean_Elab_Tactic_evalSeq___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Syntax_foldArgsAuxM___main___at_Lean_Elab_Tactic_evalSeq___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Elab_Tactic_evalSeq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Tactic_evalSeq(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalSeq___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_registerBuiltinTacticAttr___lambda__1___closed__3;
x_2 = l_Lean_Parser_Term_seq___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalSeq___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("evalSeq");
return x_1;
}
}
lean_object* _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalSeq___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_declareBuiltinTactic___closed__3;
x_2 = l___regBuiltinTactic_Lean_Elab_Tactic_evalSeq___closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalSeq___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSeq___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltinTactic_Lean_Elab_Tactic_evalSeq(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___regBuiltinTactic_Lean_Elab_Tactic_evalSeq___closed__1;
x_3 = l___regBuiltinTactic_Lean_Elab_Tactic_evalSeq___closed__3;
x_4 = l___regBuiltinTactic_Lean_Elab_Tactic_evalSeq___closed__4;
x_5 = l_Lean_Elab_Tactic_addBuiltinTactic(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Tactic_evalAssumption___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
lean_object* _init_l_Lean_Elab_Tactic_evalAssumption___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalAssumption___lambda__1___boxed), 3, 0);
return x_1;
}
}
lean_object* l_Lean_Elab_Tactic_evalAssumption(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Elab_Tactic_liftMetaTactic___closed__3;
x_6 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_5, x_2, x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
lean_dec(x_4);
lean_inc(x_7);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_assumption___boxed), 3, 1);
lean_closure_set(x_9, 0, x_7);
x_10 = l_Lean_Elab_Tactic_evalAssumption___closed__1;
x_11 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_11, 0, x_9);
lean_closure_set(x_11, 1, x_10);
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaM___rarg), 4, 2);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_11);
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaTactic___lambda__1___boxed), 4, 1);
lean_closure_set(x_13, 0, x_8);
x_14 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_monadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_14, 0, x_12);
lean_closure_set(x_14, 1, x_13);
x_15 = l_Lean_Elab_Tactic_withMVarContext___rarg(x_7, x_14, x_2, x_3);
lean_dec(x_7);
return x_15;
}
}
}
lean_object* l_Lean_Elab_Tactic_evalAssumption___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Tactic_evalAssumption___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalAssumption___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_registerBuiltinTacticAttr___lambda__1___closed__3;
x_2 = l_Lean_Meta_assumptionAux___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalAssumption___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("evalAssumption");
return x_1;
}
}
lean_object* _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalAssumption___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_declareBuiltinTactic___closed__3;
x_2 = l___regBuiltinTactic_Lean_Elab_Tactic_evalAssumption___closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalAssumption___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalAssumption), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltinTactic_Lean_Elab_Tactic_evalAssumption(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___regBuiltinTactic_Lean_Elab_Tactic_evalAssumption___closed__1;
x_3 = l___regBuiltinTactic_Lean_Elab_Tactic_evalAssumption___closed__3;
x_4 = l___regBuiltinTactic_Lean_Elab_Tactic_evalAssumption___closed__4;
x_5 = l_Lean_Elab_Tactic_addBuiltinTactic(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Tactic_evalIntro___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Syntax_getId(x_1);
x_6 = l_Lean_Meta_intro(x_2, x_5, x_3, x_4);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set(x_6, 0, x_11);
return x_6;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_6, 0);
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_6);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_13);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_6);
if (x_18 == 0)
{
return x_6;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_6, 0);
x_20 = lean_ctor_get(x_6, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_6);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
lean_object* l_Lean_Elab_Tactic_evalIntro___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_intro1(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_4, 0, x_9);
return x_4;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_4);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_4);
if (x_16 == 0)
{
return x_4;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_4, 0);
x_18 = lean_ctor_get(x_4, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_4);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
lean_object* _init_l_Lean_Elab_Tactic_evalIntro___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_registerBuiltinTacticAttr___lambda__1___closed__3;
x_2 = l_Lean_Parser_Tactic_intro___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Tactic_evalIntro(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_61; uint8_t x_62; 
x_61 = l_Lean_Elab_Tactic_evalIntro___closed__1;
lean_inc(x_1);
x_62 = l_Lean_Syntax_isOfKind(x_1, x_61);
if (x_62 == 0)
{
uint8_t x_63; 
x_63 = 0;
x_4 = x_63;
goto block_60;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_64 = l_Lean_Syntax_getArgs(x_1);
x_65 = lean_array_get_size(x_64);
lean_dec(x_64);
x_66 = lean_unsigned_to_nat(2u);
x_67 = lean_nat_dec_eq(x_65, x_66);
lean_dec(x_65);
x_4 = x_67;
goto block_60;
}
block_60:
{
uint8_t x_5; 
x_5 = l_coeDecidableEq(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_1);
x_6 = l_Lean_Elab_Tactic_throwUnsupportedSyntax___rarg(x_2, x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = l_Lean_Syntax_getArg(x_1, x_7);
x_9 = l_Lean_nullKind___closed__2;
lean_inc(x_8);
x_10 = l_Lean_Syntax_isOfKind(x_8, x_9);
if (x_10 == 0)
{
uint8_t x_55; 
x_55 = 0;
x_11 = x_55;
goto block_54;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_56 = l_Lean_Syntax_getArgs(x_8);
x_57 = lean_array_get_size(x_56);
lean_dec(x_56);
x_58 = lean_unsigned_to_nat(0u);
x_59 = lean_nat_dec_eq(x_57, x_58);
lean_dec(x_57);
x_11 = x_59;
goto block_54;
}
block_54:
{
uint8_t x_12; 
x_12 = l_coeDecidableEq(x_11);
if (x_12 == 0)
{
if (x_10 == 0)
{
uint8_t x_13; 
x_13 = l___private_Init_Lean_Elab_Term_4__hasCDot___main___closed__1;
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_8);
lean_dec(x_1);
x_14 = l_Lean_Elab_Tactic_throwUnsupportedSyntax___rarg(x_2, x_3);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_3, 1);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_8);
x_16 = l_Lean_Elab_Tactic_liftMetaTactic___closed__3;
x_17 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_16, x_2, x_3);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_unsigned_to_nat(0u);
x_21 = l_Lean_Syntax_getArg(x_8, x_20);
lean_dec(x_8);
lean_inc(x_18);
x_22 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalIntro___lambda__1___boxed), 4, 2);
lean_closure_set(x_22, 0, x_21);
lean_closure_set(x_22, 1, x_18);
x_23 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaM___rarg), 4, 2);
lean_closure_set(x_23, 0, x_1);
lean_closure_set(x_23, 1, x_22);
x_24 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaTactic___lambda__1___boxed), 4, 1);
lean_closure_set(x_24, 0, x_19);
x_25 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_monadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_25, 0, x_23);
lean_closure_set(x_25, 1, x_24);
x_26 = l_Lean_Elab_Tactic_withMVarContext___rarg(x_18, x_25, x_2, x_3);
lean_dec(x_18);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_30; 
x_27 = l_Lean_Syntax_getArgs(x_8);
x_28 = lean_array_get_size(x_27);
lean_dec(x_27);
x_29 = lean_nat_dec_eq(x_28, x_7);
lean_dec(x_28);
x_30 = l_coeDecidableEq(x_29);
if (x_30 == 0)
{
lean_object* x_31; 
lean_dec(x_8);
lean_dec(x_1);
x_31 = l_Lean_Elab_Tactic_throwUnsupportedSyntax___rarg(x_2, x_3);
return x_31;
}
else
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_3, 1);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_8);
x_33 = l_Lean_Elab_Tactic_liftMetaTactic___closed__3;
x_34 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_33, x_2, x_3);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_35 = lean_ctor_get(x_32, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_32, 1);
lean_inc(x_36);
lean_dec(x_32);
x_37 = lean_unsigned_to_nat(0u);
x_38 = l_Lean_Syntax_getArg(x_8, x_37);
lean_dec(x_8);
lean_inc(x_35);
x_39 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalIntro___lambda__1___boxed), 4, 2);
lean_closure_set(x_39, 0, x_38);
lean_closure_set(x_39, 1, x_35);
x_40 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaM___rarg), 4, 2);
lean_closure_set(x_40, 0, x_1);
lean_closure_set(x_40, 1, x_39);
x_41 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaTactic___lambda__1___boxed), 4, 1);
lean_closure_set(x_41, 0, x_36);
x_42 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_monadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_42, 0, x_40);
lean_closure_set(x_42, 1, x_41);
x_43 = l_Lean_Elab_Tactic_withMVarContext___rarg(x_35, x_42, x_2, x_3);
lean_dec(x_35);
return x_43;
}
}
}
}
else
{
lean_object* x_44; 
lean_dec(x_8);
x_44 = lean_ctor_get(x_3, 1);
lean_inc(x_44);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = l_Lean_Elab_Tactic_liftMetaTactic___closed__3;
x_46 = l_Lean_Elab_Tactic_throwError___rarg(x_1, x_45, x_2, x_3);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_47 = lean_ctor_get(x_44, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_44, 1);
lean_inc(x_48);
lean_dec(x_44);
lean_inc(x_47);
x_49 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalIntro___lambda__2___boxed), 3, 1);
lean_closure_set(x_49, 0, x_47);
x_50 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaM___rarg), 4, 2);
lean_closure_set(x_50, 0, x_1);
lean_closure_set(x_50, 1, x_49);
x_51 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_liftMetaTactic___lambda__1___boxed), 4, 1);
lean_closure_set(x_51, 0, x_48);
x_52 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_monadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_52, 0, x_50);
lean_closure_set(x_52, 1, x_51);
x_53 = l_Lean_Elab_Tactic_withMVarContext___rarg(x_47, x_52, x_2, x_3);
lean_dec(x_47);
return x_53;
}
}
}
}
}
}
}
lean_object* l_Lean_Elab_Tactic_evalIntro___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Tactic_evalIntro___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Tactic_evalIntro___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Tactic_evalIntro___lambda__2(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalIntro___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("evalIntro");
return x_1;
}
}
lean_object* _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalIntro___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_declareBuiltinTactic___closed__3;
x_2 = l___regBuiltinTactic_Lean_Elab_Tactic_evalIntro___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalIntro___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalIntro), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltinTactic_Lean_Elab_Tactic_evalIntro(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Tactic_evalIntro___closed__1;
x_3 = l___regBuiltinTactic_Lean_Elab_Tactic_evalIntro___closed__2;
x_4 = l___regBuiltinTactic_Lean_Elab_Tactic_evalIntro___closed__3;
x_5 = l_Lean_Elab_Tactic_addBuiltinTactic(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* _init_l___private_Init_Lean_Elab_Tactic_Basic_2__regTraceClasses___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Lean_Elab_Util_8__regTraceClasses___closed__2;
x_2 = l_Lean_Parser_regBuiltinTacticParserAttr___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Init_Lean_Elab_Tactic_Basic_2__regTraceClasses(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Init_Lean_Elab_Tactic_Basic_2__regTraceClasses___closed__1;
x_3 = l_Lean_registerTraceClass(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_dec(x_5);
x_6 = lean_box(0);
lean_ctor_set(x_3, 0, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
return x_3;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
lean_object* initialize_Init_Lean_Elab_Util(lean_object*);
lean_object* initialize_Init_Lean_Elab_Term(lean_object*);
lean_object* initialize_Init_Lean_Meta_Tactic_Assumption(lean_object*);
lean_object* initialize_Init_Lean_Meta_Tactic_Intro(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Elab_Tactic_Basic(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Elab_Util(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Elab_Term(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Meta_Tactic_Assumption(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Meta_Tactic_Intro(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Tactic_State_inhabited___closed__1 = _init_l_Lean_Elab_Tactic_State_inhabited___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_State_inhabited___closed__1);
l_Lean_Elab_Tactic_State_inhabited = _init_l_Lean_Elab_Tactic_State_inhabited();
lean_mark_persistent(l_Lean_Elab_Tactic_State_inhabited);
l_Lean_Elab_Tactic_liftTermElabM___rarg___closed__1 = _init_l_Lean_Elab_Tactic_liftTermElabM___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_liftTermElabM___rarg___closed__1);
l_Lean_Elab_Tactic_monadLog___closed__1 = _init_l_Lean_Elab_Tactic_monadLog___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_monadLog___closed__1);
l_Lean_Elab_Tactic_monadLog___closed__2 = _init_l_Lean_Elab_Tactic_monadLog___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_monadLog___closed__2);
l_Lean_Elab_Tactic_monadLog___closed__3 = _init_l_Lean_Elab_Tactic_monadLog___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_monadLog___closed__3);
l_Lean_Elab_Tactic_monadLog___closed__4 = _init_l_Lean_Elab_Tactic_monadLog___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_monadLog___closed__4);
l_Lean_Elab_Tactic_monadLog___closed__5 = _init_l_Lean_Elab_Tactic_monadLog___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_monadLog___closed__5);
l_Lean_Elab_Tactic_monadLog___closed__6 = _init_l_Lean_Elab_Tactic_monadLog___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_monadLog___closed__6);
l_Lean_Elab_Tactic_monadLog___closed__7 = _init_l_Lean_Elab_Tactic_monadLog___closed__7();
lean_mark_persistent(l_Lean_Elab_Tactic_monadLog___closed__7);
l_Lean_Elab_Tactic_monadLog___closed__8 = _init_l_Lean_Elab_Tactic_monadLog___closed__8();
lean_mark_persistent(l_Lean_Elab_Tactic_monadLog___closed__8);
l_Lean_Elab_Tactic_monadLog___closed__9 = _init_l_Lean_Elab_Tactic_monadLog___closed__9();
lean_mark_persistent(l_Lean_Elab_Tactic_monadLog___closed__9);
l_Lean_Elab_Tactic_monadLog___closed__10 = _init_l_Lean_Elab_Tactic_monadLog___closed__10();
lean_mark_persistent(l_Lean_Elab_Tactic_monadLog___closed__10);
l_Lean_Elab_Tactic_monadLog___closed__11 = _init_l_Lean_Elab_Tactic_monadLog___closed__11();
lean_mark_persistent(l_Lean_Elab_Tactic_monadLog___closed__11);
l_Lean_Elab_Tactic_monadLog = _init_l_Lean_Elab_Tactic_monadLog();
lean_mark_persistent(l_Lean_Elab_Tactic_monadLog);
l_Lean_Elab_Tactic_throwUnsupportedSyntax___rarg___closed__1 = _init_l_Lean_Elab_Tactic_throwUnsupportedSyntax___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_throwUnsupportedSyntax___rarg___closed__1);
l_Lean_Elab_Tactic_monadQuotation___closed__1 = _init_l_Lean_Elab_Tactic_monadQuotation___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_monadQuotation___closed__1);
l_Lean_Elab_Tactic_monadQuotation___closed__2 = _init_l_Lean_Elab_Tactic_monadQuotation___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_monadQuotation___closed__2);
l_Lean_Elab_Tactic_monadQuotation___closed__3 = _init_l_Lean_Elab_Tactic_monadQuotation___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_monadQuotation___closed__3);
l_Lean_Elab_Tactic_monadQuotation = _init_l_Lean_Elab_Tactic_monadQuotation();
lean_mark_persistent(l_Lean_Elab_Tactic_monadQuotation);
l_PersistentHashMap_empty___at_Lean_Elab_Tactic_mkBuiltinTacticTable___spec__3 = _init_l_PersistentHashMap_empty___at_Lean_Elab_Tactic_mkBuiltinTacticTable___spec__3();
lean_mark_persistent(l_PersistentHashMap_empty___at_Lean_Elab_Tactic_mkBuiltinTacticTable___spec__3);
l_Lean_SMap_empty___at_Lean_Elab_Tactic_mkBuiltinTacticTable___spec__1___closed__1 = _init_l_Lean_SMap_empty___at_Lean_Elab_Tactic_mkBuiltinTacticTable___spec__1___closed__1();
lean_mark_persistent(l_Lean_SMap_empty___at_Lean_Elab_Tactic_mkBuiltinTacticTable___spec__1___closed__1);
l_Lean_SMap_empty___at_Lean_Elab_Tactic_mkBuiltinTacticTable___spec__1___closed__2 = _init_l_Lean_SMap_empty___at_Lean_Elab_Tactic_mkBuiltinTacticTable___spec__1___closed__2();
lean_mark_persistent(l_Lean_SMap_empty___at_Lean_Elab_Tactic_mkBuiltinTacticTable___spec__1___closed__2);
l_Lean_SMap_empty___at_Lean_Elab_Tactic_mkBuiltinTacticTable___spec__1 = _init_l_Lean_SMap_empty___at_Lean_Elab_Tactic_mkBuiltinTacticTable___spec__1();
lean_mark_persistent(l_Lean_SMap_empty___at_Lean_Elab_Tactic_mkBuiltinTacticTable___spec__1);
res = l_Lean_Elab_Tactic_mkBuiltinTacticTable(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Tactic_builtinTacticTable = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Tactic_builtinTacticTable);
lean_dec_ref(res);
l_Lean_Elab_Tactic_addBuiltinTactic___closed__1 = _init_l_Lean_Elab_Tactic_addBuiltinTactic___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_addBuiltinTactic___closed__1);
l_Lean_Elab_Tactic_declareBuiltinTactic___closed__1 = _init_l_Lean_Elab_Tactic_declareBuiltinTactic___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_declareBuiltinTactic___closed__1);
l_Lean_Elab_Tactic_declareBuiltinTactic___closed__2 = _init_l_Lean_Elab_Tactic_declareBuiltinTactic___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_declareBuiltinTactic___closed__2);
l_Lean_Elab_Tactic_declareBuiltinTactic___closed__3 = _init_l_Lean_Elab_Tactic_declareBuiltinTactic___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_declareBuiltinTactic___closed__3);
l_Lean_Elab_Tactic_declareBuiltinTactic___closed__4 = _init_l_Lean_Elab_Tactic_declareBuiltinTactic___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_declareBuiltinTactic___closed__4);
l_Lean_Elab_Tactic_declareBuiltinTactic___closed__5 = _init_l_Lean_Elab_Tactic_declareBuiltinTactic___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_declareBuiltinTactic___closed__5);
l_Lean_Elab_Tactic_declareBuiltinTactic___closed__6 = _init_l_Lean_Elab_Tactic_declareBuiltinTactic___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_declareBuiltinTactic___closed__6);
l_Lean_Elab_Tactic_declareBuiltinTactic___closed__7 = _init_l_Lean_Elab_Tactic_declareBuiltinTactic___closed__7();
lean_mark_persistent(l_Lean_Elab_Tactic_declareBuiltinTactic___closed__7);
l_Lean_Elab_Tactic_registerBuiltinTacticAttr___lambda__1___closed__1 = _init_l_Lean_Elab_Tactic_registerBuiltinTacticAttr___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_registerBuiltinTacticAttr___lambda__1___closed__1);
l_Lean_Elab_Tactic_registerBuiltinTacticAttr___lambda__1___closed__2 = _init_l_Lean_Elab_Tactic_registerBuiltinTacticAttr___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_registerBuiltinTacticAttr___lambda__1___closed__2);
l_Lean_Elab_Tactic_registerBuiltinTacticAttr___lambda__1___closed__3 = _init_l_Lean_Elab_Tactic_registerBuiltinTacticAttr___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_registerBuiltinTacticAttr___lambda__1___closed__3);
l_Lean_Elab_Tactic_registerBuiltinTacticAttr___lambda__1___closed__4 = _init_l_Lean_Elab_Tactic_registerBuiltinTacticAttr___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_registerBuiltinTacticAttr___lambda__1___closed__4);
l_Lean_Elab_Tactic_registerBuiltinTacticAttr___lambda__1___closed__5 = _init_l_Lean_Elab_Tactic_registerBuiltinTacticAttr___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_registerBuiltinTacticAttr___lambda__1___closed__5);
l_Lean_Elab_Tactic_registerBuiltinTacticAttr___closed__1 = _init_l_Lean_Elab_Tactic_registerBuiltinTacticAttr___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_registerBuiltinTacticAttr___closed__1);
l_Lean_Elab_Tactic_registerBuiltinTacticAttr___closed__2 = _init_l_Lean_Elab_Tactic_registerBuiltinTacticAttr___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_registerBuiltinTacticAttr___closed__2);
l_Lean_Elab_Tactic_registerBuiltinTacticAttr___closed__3 = _init_l_Lean_Elab_Tactic_registerBuiltinTacticAttr___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_registerBuiltinTacticAttr___closed__3);
l_Lean_Elab_Tactic_registerBuiltinTacticAttr___closed__4 = _init_l_Lean_Elab_Tactic_registerBuiltinTacticAttr___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_registerBuiltinTacticAttr___closed__4);
l_Lean_Elab_Tactic_registerBuiltinTacticAttr___closed__5 = _init_l_Lean_Elab_Tactic_registerBuiltinTacticAttr___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_registerBuiltinTacticAttr___closed__5);
res = l_Lean_Elab_Tactic_registerBuiltinTacticAttr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Tactic_mkTacticAttribute___closed__1 = _init_l_Lean_Elab_Tactic_mkTacticAttribute___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_mkTacticAttribute___closed__1);
l_Lean_Elab_Tactic_tacticElabAttribute___closed__1 = _init_l_Lean_Elab_Tactic_tacticElabAttribute___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_tacticElabAttribute___closed__1);
l_Lean_Elab_Tactic_tacticElabAttribute___closed__2 = _init_l_Lean_Elab_Tactic_tacticElabAttribute___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_tacticElabAttribute___closed__2);
l_Lean_Elab_Tactic_tacticElabAttribute___closed__3 = _init_l_Lean_Elab_Tactic_tacticElabAttribute___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_tacticElabAttribute___closed__3);
l_Lean_Elab_Tactic_tacticElabAttribute___closed__4 = _init_l_Lean_Elab_Tactic_tacticElabAttribute___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_tacticElabAttribute___closed__4);
l_Lean_Elab_Tactic_tacticElabAttribute___closed__5 = _init_l_Lean_Elab_Tactic_tacticElabAttribute___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_tacticElabAttribute___closed__5);
res = l_Lean_Elab_Tactic_mkTacticAttribute(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Tactic_tacticElabAttribute = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Tactic_tacticElabAttribute);
lean_dec_ref(res);
l_Lean_Elab_Tactic_evalTactic___main___closed__1 = _init_l_Lean_Elab_Tactic_evalTactic___main___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalTactic___main___closed__1);
l_Lean_Elab_Tactic_evalTactic___main___closed__2 = _init_l_Lean_Elab_Tactic_evalTactic___main___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalTactic___main___closed__2);
l_Lean_Elab_Tactic_evalTactic___main___closed__3 = _init_l_Lean_Elab_Tactic_evalTactic___main___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_evalTactic___main___closed__3);
l_Lean_Elab_Tactic_evalTactic___main___closed__4 = _init_l_Lean_Elab_Tactic_evalTactic___main___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_evalTactic___main___closed__4);
l_Lean_Elab_Tactic_resetSynthInstanceCache___closed__1 = _init_l_Lean_Elab_Tactic_resetSynthInstanceCache___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_resetSynthInstanceCache___closed__1);
l_Lean_Elab_Tactic_liftMetaTactic___closed__1 = _init_l_Lean_Elab_Tactic_liftMetaTactic___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_liftMetaTactic___closed__1);
l_Lean_Elab_Tactic_liftMetaTactic___closed__2 = _init_l_Lean_Elab_Tactic_liftMetaTactic___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_liftMetaTactic___closed__2);
l_Lean_Elab_Tactic_liftMetaTactic___closed__3 = _init_l_Lean_Elab_Tactic_liftMetaTactic___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_liftMetaTactic___closed__3);
l___regBuiltinTactic_Lean_Elab_Tactic_evalSeq___closed__1 = _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalSeq___closed__1();
lean_mark_persistent(l___regBuiltinTactic_Lean_Elab_Tactic_evalSeq___closed__1);
l___regBuiltinTactic_Lean_Elab_Tactic_evalSeq___closed__2 = _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalSeq___closed__2();
lean_mark_persistent(l___regBuiltinTactic_Lean_Elab_Tactic_evalSeq___closed__2);
l___regBuiltinTactic_Lean_Elab_Tactic_evalSeq___closed__3 = _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalSeq___closed__3();
lean_mark_persistent(l___regBuiltinTactic_Lean_Elab_Tactic_evalSeq___closed__3);
l___regBuiltinTactic_Lean_Elab_Tactic_evalSeq___closed__4 = _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalSeq___closed__4();
lean_mark_persistent(l___regBuiltinTactic_Lean_Elab_Tactic_evalSeq___closed__4);
res = l___regBuiltinTactic_Lean_Elab_Tactic_evalSeq(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Tactic_evalAssumption___closed__1 = _init_l_Lean_Elab_Tactic_evalAssumption___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalAssumption___closed__1);
l___regBuiltinTactic_Lean_Elab_Tactic_evalAssumption___closed__1 = _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalAssumption___closed__1();
lean_mark_persistent(l___regBuiltinTactic_Lean_Elab_Tactic_evalAssumption___closed__1);
l___regBuiltinTactic_Lean_Elab_Tactic_evalAssumption___closed__2 = _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalAssumption___closed__2();
lean_mark_persistent(l___regBuiltinTactic_Lean_Elab_Tactic_evalAssumption___closed__2);
l___regBuiltinTactic_Lean_Elab_Tactic_evalAssumption___closed__3 = _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalAssumption___closed__3();
lean_mark_persistent(l___regBuiltinTactic_Lean_Elab_Tactic_evalAssumption___closed__3);
l___regBuiltinTactic_Lean_Elab_Tactic_evalAssumption___closed__4 = _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalAssumption___closed__4();
lean_mark_persistent(l___regBuiltinTactic_Lean_Elab_Tactic_evalAssumption___closed__4);
res = l___regBuiltinTactic_Lean_Elab_Tactic_evalAssumption(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Tactic_evalIntro___closed__1 = _init_l_Lean_Elab_Tactic_evalIntro___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalIntro___closed__1);
l___regBuiltinTactic_Lean_Elab_Tactic_evalIntro___closed__1 = _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalIntro___closed__1();
lean_mark_persistent(l___regBuiltinTactic_Lean_Elab_Tactic_evalIntro___closed__1);
l___regBuiltinTactic_Lean_Elab_Tactic_evalIntro___closed__2 = _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalIntro___closed__2();
lean_mark_persistent(l___regBuiltinTactic_Lean_Elab_Tactic_evalIntro___closed__2);
l___regBuiltinTactic_Lean_Elab_Tactic_evalIntro___closed__3 = _init_l___regBuiltinTactic_Lean_Elab_Tactic_evalIntro___closed__3();
lean_mark_persistent(l___regBuiltinTactic_Lean_Elab_Tactic_evalIntro___closed__3);
res = l___regBuiltinTactic_Lean_Elab_Tactic_evalIntro(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Init_Lean_Elab_Tactic_Basic_2__regTraceClasses___closed__1 = _init_l___private_Init_Lean_Elab_Tactic_Basic_2__regTraceClasses___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_Tactic_Basic_2__regTraceClasses___closed__1);
res = l___private_Init_Lean_Elab_Tactic_Basic_2__regTraceClasses(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
