// Lean compiler output
// Module: Lean.Elab.Tactic.Rewrites
// Imports: public import Lean.Elab.Tactic.Location public import Lean.Meta.Tactic.Replace public import Lean.Meta.Tactic.Rewrites
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
lean_object* l_Lean_FVarId_findDecl_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__10(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Elab_Rewrites_evalExact___lam__2___closed__1;
static lean_object* l_Lean_Elab_Rewrites_evalExact___lam__2___closed__5;
lean_object* l_Lean_Meta_Rewrites_RewriteResult_addSuggestion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Rewrites_evalExact___lam__1___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Elab_Rewrites_evalExact_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__8(size_t, size_t, lean_object*);
lean_object* l_Lean_Elab_Tactic_expandOptLocation(lean_object*);
lean_object* l_List_get_x3fInternal___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___closed__4;
lean_object* l_Lean_Meta_Rewrites_findRewrites(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Rewrites_evalExact___closed__8;
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Rewrites_evalExact___lam__2___closed__9;
uint8_t lean_usize_dec_eq(size_t, size_t);
static lean_object* l_Lean_Elab_Rewrites_evalExact___closed__6;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_replaceTargetEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Rewrites_evalExact___closed__11;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__4;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Rewrites_evalExact_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Elab_Rewrites_evalExact_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_Meta_Rewrites_localHypotheses(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_Elab_Rewrites_evalExact___closed__1;
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Rewrites_evalExact_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__0___redArg();
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__8___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Rewrites_evalExact___lam__2___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__2;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__0___redArg___closed__1;
static lean_object* l_Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__1;
static lean_object* l_Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__0;
uint8_t l_Lean_Expr_hasMVar(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Rewrites_evalExact_spec__9(lean_object*, size_t, size_t, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Rewrites_evalExact___lam__2___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__0___redArg___boxed(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Rewrites_evalExact_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withLocation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__5;
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Rewrites_evalExact___closed__7;
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Rewrites_createModuleTreeRef(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Rewrites_evalExact___closed__9;
static lean_object* l_Lean_Elab_Rewrites_evalExact___closed__5;
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1();
lean_object* lean_st_ref_get(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___boxed(lean_object*);
static lean_object* l_Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact___lam__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Elab_Rewrites_evalExact_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___boxed(lean_object*);
static lean_object* l_Lean_Elab_Rewrites_evalExact___lam__2___closed__8;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_reportOutOfHeartbeats(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__10___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Rewrites_evalExact_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_Rewrites_evalExact_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkOptionalNode(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Rewrites_evalExact___lam__0___closed__1;
static lean_object* l_Lean_Elab_Rewrites_evalExact___closed__3;
static lean_object* l_Lean_Elab_Rewrites_evalExact___lam__1___closed__1;
static lean_object* l_Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___closed__2;
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact___lam__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_saveState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Rewrites_evalExact_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getUserName___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isImplementationDetail(lean_object*);
static lean_object* l_Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___closed__3;
static lean_object* l_Lean_Elab_Rewrites_evalExact___closed__0;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__6_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Rewrites_evalExact___closed__4;
extern lean_object* l_Lean_NameSet_empty;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__6_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Rewrites_evalExact___closed__10;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Elab_Rewrites_evalExact_spec__5___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Elab_Rewrites_evalExact_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Rewrites_evalExact___lam__1___closed__2;
uint8_t l_Lean_Syntax_isNone(lean_object*);
static lean_object* l_Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__6;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__10___closed__0;
static lean_object* l_Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___closed__1;
static lean_object* l_Lean_Elab_Rewrites_evalExact___lam__2___closed__4;
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Rewrites_evalExact___closed__2;
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__6_spec__6___redArg___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
size_t lean_array_size(lean_object*);
static lean_object* l_Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__3;
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_Rewrites_evalExact_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Rewrites_evalExact___lam__1___closed__3;
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getType___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3();
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Rewrites_evalExact_spec__11(uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Rewrites_evalExact_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lean_Elab_Rewrites_evalExact___lam__0___closed__0;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Elab_Rewrites_evalExact_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__6_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__6_spec__6___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Rewrites_evalExact___lam__2___closed__3;
static lean_object* l_Lean_Elab_Rewrites_evalExact___lam__2___closed__7;
static lean_object* l_Lean_Elab_Rewrites_evalExact___lam__2___closed__2;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__6_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMCtxImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_unsupportedSyntaxExceptionId;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__0___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__0___redArg___closed__0;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__0___redArg() {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__0___redArg___closed__1;
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__0___redArg();
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_st_ref_get(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
lean_dec_ref(x_7);
x_9 = lean_st_ref_get(x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_10);
lean_dec_ref(x_9);
x_11 = lean_ctor_get(x_2, 2);
x_12 = lean_ctor_get(x_4, 2);
lean_inc(x_12);
lean_inc_ref(x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set(x_13, 2, x_11);
lean_ctor_set(x_13, 3, x_12);
x_14 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_1);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_7);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__1___redArg(x_2, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Rewrites_evalExact_spec__3___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Expr_hasMVar(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_1);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_6 = lean_st_ref_get(x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
lean_dec_ref(x_6);
x_8 = l_Lean_instantiateMVarsCore(x_7, x_1);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_st_ref_take(x_2);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_10);
x_14 = lean_st_ref_set(x_2, x_11);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_11, 1);
x_17 = lean_ctor_get(x_11, 2);
x_18 = lean_ctor_get(x_11, 3);
x_19 = lean_ctor_get(x_11, 4);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
x_20 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_20, 0, x_10);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set(x_20, 2, x_17);
lean_ctor_set(x_20, 3, x_18);
lean_ctor_set(x_20, 4, x_19);
x_21 = lean_st_ref_set(x_2, x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_9);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Rewrites_evalExact_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_instantiateMVars___at___00Lean_Elab_Rewrites_evalExact_spec__3___redArg(x_1, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_Rewrites_evalExact_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_3, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_3, 1);
lean_inc(x_16);
lean_dec_ref(x_3);
lean_inc_ref(x_1);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_1);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_2);
x_18 = l_Lean_Meta_Rewrites_RewriteResult_addSuggestion(x_2, x_15, x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_dec_ref(x_18);
x_3 = x_16;
goto _start;
}
else
{
lean_dec(x_16);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Elab_Rewrites_evalExact_spec__5___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = lean_apply_9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, lean_box(0));
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Elab_Rewrites_evalExact_spec__5___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at___00Lean_Elab_Rewrites_evalExact_spec__5___redArg___lam__0___boxed), 10, 5);
lean_closure_set(x_12, 0, x_2);
lean_closure_set(x_12, 1, x_3);
lean_closure_set(x_12, 2, x_4);
lean_closure_set(x_12, 3, x_5);
lean_closure_set(x_12, 4, x_6);
x_13 = l___private_Lean_Meta_Basic_0__Lean_Meta_withMCtxImp(lean_box(0), x_1, x_12, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
return x_13;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
return x_13;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Elab_Rewrites_evalExact_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_withMCtx___at___00Lean_Elab_Rewrites_evalExact_spec__5___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__6_spec__6___redArg___lam__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Elab_Tactic_saveState___redArg(x_7, x_9, x_11, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = lean_ctor_get(x_12, 5);
x_18 = lean_ctor_get(x_1, 0);
x_19 = lean_box(x_3);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_2);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
lean_inc_ref(x_18);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_18);
x_24 = l_Lean_Expr_fvar___override(x_4);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
lean_inc(x_17);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_17);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_16);
x_28 = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion(x_5, x_22, x_23, x_25, x_26, x_27, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_28;
}
else
{
uint8_t x_29; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
x_29 = !lean_is_exclusive(x_15);
if (x_29 == 0)
{
return x_15;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_15, 0);
lean_inc(x_30);
lean_dec(x_15);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__6_spec__6___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_15; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_5);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_16 = lean_ctor_get(x_4, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_4, 1);
lean_inc(x_17);
lean_dec_ref(x_4);
x_18 = lean_ctor_get(x_16, 0);
lean_inc_ref(x_18);
x_19 = lean_ctor_get_uint8(x_16, sizeof(void*)*4);
x_20 = lean_ctor_get(x_16, 2);
lean_inc_ref(x_20);
x_21 = lean_ctor_get(x_16, 3);
lean_inc_ref(x_21);
lean_dec(x_16);
x_22 = lean_box(x_19);
lean_inc(x_2);
lean_inc(x_1);
x_23 = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__6_spec__6___redArg___lam__0___boxed), 14, 5);
lean_closure_set(x_23, 0, x_20);
lean_closure_set(x_23, 1, x_18);
lean_closure_set(x_23, 2, x_22);
lean_closure_set(x_23, 3, x_1);
lean_closure_set(x_23, 4, x_2);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_24 = l_Lean_Meta_withMCtx___at___00Lean_Elab_Rewrites_evalExact_spec__5___redArg(x_21, x_23, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_24) == 0)
{
lean_dec_ref(x_24);
{
lean_object* _tmp_3 = x_17;
lean_object* _tmp_4 = x_3;
x_4 = _tmp_3;
x_5 = _tmp_4;
}
goto _start;
}
else
{
lean_dec(x_17);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__6_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_17; 
x_17 = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__6_spec__6___redArg(x_1, x_2, x_3, x_5, x_6, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_17;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__6___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_16; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_6);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_17 = lean_ctor_get(x_5, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_5, 1);
lean_inc(x_18);
lean_dec_ref(x_5);
x_19 = lean_ctor_get(x_17, 0);
lean_inc_ref(x_19);
x_20 = lean_ctor_get_uint8(x_17, sizeof(void*)*4);
x_21 = lean_ctor_get(x_17, 2);
lean_inc_ref(x_21);
x_22 = lean_ctor_get(x_17, 3);
lean_inc_ref(x_22);
lean_dec(x_17);
x_23 = lean_box(x_20);
lean_inc(x_2);
lean_inc(x_1);
x_24 = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__6_spec__6___redArg___lam__0___boxed), 14, 5);
lean_closure_set(x_24, 0, x_21);
lean_closure_set(x_24, 1, x_19);
lean_closure_set(x_24, 2, x_23);
lean_closure_set(x_24, 3, x_1);
lean_closure_set(x_24, 4, x_2);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_25 = l_Lean_Meta_withMCtx___at___00Lean_Elab_Rewrites_evalExact_spec__5___redArg(x_22, x_24, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
lean_dec_ref(x_25);
x_26 = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__6_spec__6___redArg(x_1, x_2, x_3, x_18, x_3, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_26;
}
else
{
lean_dec(x_18);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_17; 
x_17 = l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__6___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_17;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__8(size_t x_1, size_t x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Rewrites_evalExact_spec__9(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lean_NameSet_insert(x_4, x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__10___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("group", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__10___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__10___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__10(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_array_uget(x_4, x_3);
x_8 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__10___closed__1;
lean_inc(x_7);
x_9 = l_Lean_Syntax_isOfKind(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_7);
lean_dec_ref(x_4);
x_10 = lean_box(0);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_array_uset(x_4, x_3, x_11);
x_13 = l_Lean_Syntax_getArg(x_7, x_1);
lean_dec(x_7);
x_14 = 1;
x_15 = lean_usize_add(x_3, x_14);
x_16 = lean_array_uset(x_12, x_3, x_13);
x_3 = x_15;
x_4 = x_16;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Rewrites_evalExact_spec__11(uint8_t x_1, uint8_t x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_12; 
x_12 = lean_usize_dec_eq(x_4, x_5);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_6, 0);
x_14 = lean_unbox(x_13);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_6);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_6, 0);
lean_dec(x_16);
x_17 = lean_box(x_1);
lean_ctor_set(x_6, 0, x_17);
x_7 = x_6;
goto block_11;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_6, 1);
lean_inc(x_18);
lean_dec(x_6);
x_19 = lean_box(x_1);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_7 = x_20;
goto block_11;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_6);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_6, 1);
x_23 = lean_ctor_get(x_6, 0);
lean_dec(x_23);
x_24 = lean_array_uget(x_3, x_4);
x_25 = lean_array_push(x_22, x_24);
x_26 = lean_box(x_2);
lean_ctor_set(x_6, 1, x_25);
lean_ctor_set(x_6, 0, x_26);
x_7 = x_6;
goto block_11;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_6, 1);
lean_inc(x_27);
lean_dec(x_6);
x_28 = lean_array_uget(x_3, x_4);
x_29 = lean_array_push(x_27, x_28);
x_30 = lean_box(x_2);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
x_7 = x_31;
goto block_11;
}
}
}
else
{
return x_6;
}
block_11:
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_4, x_8);
x_4 = x_9;
x_6 = x_7;
goto _start;
}
}
}
static lean_object* _init_l_Lean_Elab_Rewrites_evalExact___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Failed to find a rewrite for some location", 42, 42);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Rewrites_evalExact___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Rewrites_evalExact___lam__0___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_Elab_Rewrites_evalExact___lam__0___closed__1;
x_12 = l_Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__1___redArg(x_11, x_6, x_7, x_8, x_9);
return x_12;
}
}
static lean_object* _init_l_Lean_Elab_Rewrites_evalExact___lam__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("rewrites", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Rewrites_evalExact___lam__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Rewrites_evalExact___lam__1___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Rewrites_evalExact___lam__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Could not find any lemmas which can rewrite the hypothesis ", 59, 59);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Rewrites_evalExact___lam__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Rewrites_evalExact___lam__1___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_17; 
lean_inc_ref(x_12);
lean_inc(x_7);
x_17 = l_Lean_FVarId_findDecl_x3f___redArg(x_7, x_12);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
if (lean_obj_tag(x_19) == 1)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = l_Lean_LocalDecl_isImplementationDetail(x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_free_object(x_17);
lean_inc_ref(x_12);
lean_inc(x_7);
x_22 = l_Lean_FVarId_getType___redArg(x_7, x_12, x_14, x_15);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_24 = l_Lean_instantiateMVars___at___00Lean_Elab_Rewrites_evalExact_spec__3___redArg(x_23, x_13);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec_ref(x_24);
x_26 = lean_box(0);
lean_inc(x_7);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_7);
lean_ctor_set(x_27, 1, x_26);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
x_28 = l_Lean_Meta_Rewrites_localHypotheses(x_27, x_12, x_13, x_14, x_15);
lean_dec_ref(x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec_ref(x_28);
x_30 = 2;
x_31 = lean_unsigned_to_nat(20u);
x_32 = lean_unsigned_to_nat(10u);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_2);
x_33 = l_Lean_Meta_Rewrites_findRewrites(x_29, x_1, x_2, x_25, x_3, x_30, x_21, x_31, x_32, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec_ref(x_33);
x_35 = l_Lean_Elab_Rewrites_evalExact___lam__1___closed__1;
lean_inc_ref(x_14);
x_36 = l_Lean_reportOutOfHeartbeats(x_35, x_4, x_5, x_14, x_15);
if (lean_obj_tag(x_36) == 0)
{
uint8_t x_37; 
lean_dec_ref(x_36);
x_37 = l_List_isEmpty___redArg(x_34);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_box(0);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_9);
lean_inc(x_34);
lean_inc(x_7);
x_39 = l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__6___redArg(x_7, x_4, x_38, x_34, x_34, x_38, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_39, 0);
lean_dec(x_41);
x_42 = l_List_get_x3fInternal___redArg(x_34, x_6);
lean_dec(x_34);
if (lean_obj_tag(x_42) == 1)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
lean_free_object(x_39);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
lean_dec_ref(x_42);
x_44 = lean_st_ref_take(x_13);
x_45 = lean_ctor_get(x_43, 2);
lean_inc_ref(x_45);
x_46 = lean_ctor_get(x_43, 3);
lean_inc_ref(x_46);
lean_dec(x_43);
x_47 = !lean_is_exclusive(x_44);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_48 = lean_ctor_get(x_44, 0);
lean_dec(x_48);
lean_ctor_set(x_44, 0, x_46);
x_49 = lean_st_ref_set(x_13, x_44);
x_50 = lean_ctor_get(x_45, 0);
lean_inc_ref(x_50);
x_51 = lean_ctor_get(x_45, 1);
lean_inc_ref(x_51);
x_52 = lean_ctor_get(x_45, 2);
lean_inc(x_52);
lean_dec_ref(x_45);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
x_53 = l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore(x_2, x_7, x_50, x_51, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
lean_dec_ref(x_53);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec(x_54);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_52);
x_57 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_56, x_9, x_12, x_13, x_14, x_15);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_9);
return x_57;
}
else
{
uint8_t x_58; 
lean_dec(x_52);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_9);
x_58 = !lean_is_exclusive(x_53);
if (x_58 == 0)
{
return x_53;
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_53, 0);
lean_inc(x_59);
lean_dec(x_53);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_59);
return x_60;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_61 = lean_ctor_get(x_44, 1);
x_62 = lean_ctor_get(x_44, 2);
x_63 = lean_ctor_get(x_44, 3);
x_64 = lean_ctor_get(x_44, 4);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_44);
x_65 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_65, 0, x_46);
lean_ctor_set(x_65, 1, x_61);
lean_ctor_set(x_65, 2, x_62);
lean_ctor_set(x_65, 3, x_63);
lean_ctor_set(x_65, 4, x_64);
x_66 = lean_st_ref_set(x_13, x_65);
x_67 = lean_ctor_get(x_45, 0);
lean_inc_ref(x_67);
x_68 = lean_ctor_get(x_45, 1);
lean_inc_ref(x_68);
x_69 = lean_ctor_get(x_45, 2);
lean_inc(x_69);
lean_dec_ref(x_45);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
x_70 = l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore(x_2, x_7, x_67, x_68, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
lean_dec_ref(x_70);
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
lean_dec(x_71);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_69);
x_74 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_73, x_9, x_12, x_13, x_14, x_15);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_9);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_69);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_9);
x_75 = lean_ctor_get(x_70, 0);
lean_inc(x_75);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 x_76 = x_70;
} else {
 lean_dec_ref(x_70);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(1, 1, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_75);
return x_77;
}
}
}
else
{
lean_dec(x_42);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_2);
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
}
else
{
lean_object* x_78; 
lean_dec(x_39);
x_78 = l_List_get_x3fInternal___redArg(x_34, x_6);
lean_dec(x_34);
if (lean_obj_tag(x_78) == 1)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
lean_dec_ref(x_78);
x_80 = lean_st_ref_take(x_13);
x_81 = lean_ctor_get(x_79, 2);
lean_inc_ref(x_81);
x_82 = lean_ctor_get(x_79, 3);
lean_inc_ref(x_82);
lean_dec(x_79);
x_83 = lean_ctor_get(x_80, 1);
lean_inc_ref(x_83);
x_84 = lean_ctor_get(x_80, 2);
lean_inc(x_84);
x_85 = lean_ctor_get(x_80, 3);
lean_inc_ref(x_85);
x_86 = lean_ctor_get(x_80, 4);
lean_inc_ref(x_86);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 lean_ctor_release(x_80, 2);
 lean_ctor_release(x_80, 3);
 lean_ctor_release(x_80, 4);
 x_87 = x_80;
} else {
 lean_dec_ref(x_80);
 x_87 = lean_box(0);
}
if (lean_is_scalar(x_87)) {
 x_88 = lean_alloc_ctor(0, 5, 0);
} else {
 x_88 = x_87;
}
lean_ctor_set(x_88, 0, x_82);
lean_ctor_set(x_88, 1, x_83);
lean_ctor_set(x_88, 2, x_84);
lean_ctor_set(x_88, 3, x_85);
lean_ctor_set(x_88, 4, x_86);
x_89 = lean_st_ref_set(x_13, x_88);
x_90 = lean_ctor_get(x_81, 0);
lean_inc_ref(x_90);
x_91 = lean_ctor_get(x_81, 1);
lean_inc_ref(x_91);
x_92 = lean_ctor_get(x_81, 2);
lean_inc(x_92);
lean_dec_ref(x_81);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
x_93 = l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore(x_2, x_7, x_90, x_91, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
lean_dec_ref(x_93);
x_95 = lean_ctor_get(x_94, 1);
lean_inc(x_95);
lean_dec(x_94);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_92);
x_97 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_96, x_9, x_12, x_13, x_14, x_15);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_9);
return x_97;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_92);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_9);
x_98 = lean_ctor_get(x_93, 0);
lean_inc(x_98);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 x_99 = x_93;
} else {
 lean_dec_ref(x_93);
 x_99 = lean_box(0);
}
if (lean_is_scalar(x_99)) {
 x_100 = lean_alloc_ctor(1, 1, 0);
} else {
 x_100 = x_99;
}
lean_ctor_set(x_100, 0, x_98);
return x_100;
}
}
else
{
lean_object* x_101; 
lean_dec(x_78);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_2);
x_101 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_101, 0, x_38);
return x_101;
}
}
}
else
{
lean_dec(x_34);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_39;
}
}
else
{
lean_object* x_102; 
lean_dec(x_34);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_inc_ref(x_12);
x_102 = l_Lean_FVarId_getUserName___redArg(x_7, x_12, x_14, x_15);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
lean_dec_ref(x_102);
x_104 = l_Lean_Elab_Rewrites_evalExact___lam__1___closed__3;
x_105 = l_Lean_MessageData_ofName(x_103);
x_106 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
x_107 = l_Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__1___redArg(x_106, x_12, x_13, x_14, x_15);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
return x_107;
}
else
{
uint8_t x_108; 
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
x_108 = !lean_is_exclusive(x_102);
if (x_108 == 0)
{
return x_102;
}
else
{
lean_object* x_109; lean_object* x_110; 
x_109 = lean_ctor_get(x_102, 0);
lean_inc(x_109);
lean_dec(x_102);
x_110 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_110, 0, x_109);
return x_110;
}
}
}
}
else
{
lean_dec(x_34);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
return x_36;
}
}
else
{
uint8_t x_111; 
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_111 = !lean_is_exclusive(x_33);
if (x_111 == 0)
{
return x_33;
}
else
{
lean_object* x_112; lean_object* x_113; 
x_112 = lean_ctor_get(x_33, 0);
lean_inc(x_112);
lean_dec(x_33);
x_113 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_113, 0, x_112);
return x_113;
}
}
}
else
{
uint8_t x_114; 
lean_dec(x_25);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_114 = !lean_is_exclusive(x_28);
if (x_114 == 0)
{
return x_28;
}
else
{
lean_object* x_115; lean_object* x_116; 
x_115 = lean_ctor_get(x_28, 0);
lean_inc(x_115);
lean_dec(x_28);
x_116 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_116, 0, x_115);
return x_116;
}
}
}
else
{
uint8_t x_117; 
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_117 = !lean_is_exclusive(x_22);
if (x_117 == 0)
{
return x_22;
}
else
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_22, 0);
lean_inc(x_118);
lean_dec(x_22);
x_119 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_119, 0, x_118);
return x_119;
}
}
}
else
{
lean_object* x_120; 
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_120 = lean_box(0);
lean_ctor_set(x_17, 0, x_120);
return x_17;
}
}
else
{
lean_object* x_121; 
lean_dec(x_19);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_121 = lean_box(0);
lean_ctor_set(x_17, 0, x_121);
return x_17;
}
}
else
{
lean_object* x_122; 
x_122 = lean_ctor_get(x_17, 0);
lean_inc(x_122);
lean_dec(x_17);
if (lean_obj_tag(x_122) == 1)
{
lean_object* x_123; uint8_t x_124; 
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
lean_dec_ref(x_122);
x_124 = l_Lean_LocalDecl_isImplementationDetail(x_123);
lean_dec(x_123);
if (x_124 == 0)
{
lean_object* x_125; 
lean_inc_ref(x_12);
lean_inc(x_7);
x_125 = l_Lean_FVarId_getType___redArg(x_7, x_12, x_14, x_15);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
lean_dec_ref(x_125);
x_127 = l_Lean_instantiateMVars___at___00Lean_Elab_Rewrites_evalExact_spec__3___redArg(x_126, x_13);
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
lean_dec_ref(x_127);
x_129 = lean_box(0);
lean_inc(x_7);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_7);
lean_ctor_set(x_130, 1, x_129);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
x_131 = l_Lean_Meta_Rewrites_localHypotheses(x_130, x_12, x_13, x_14, x_15);
lean_dec_ref(x_130);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; uint8_t x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
lean_dec_ref(x_131);
x_133 = 2;
x_134 = lean_unsigned_to_nat(20u);
x_135 = lean_unsigned_to_nat(10u);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_2);
x_136 = l_Lean_Meta_Rewrites_findRewrites(x_132, x_1, x_2, x_128, x_3, x_133, x_124, x_134, x_135, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
lean_dec_ref(x_136);
x_138 = l_Lean_Elab_Rewrites_evalExact___lam__1___closed__1;
lean_inc_ref(x_14);
x_139 = l_Lean_reportOutOfHeartbeats(x_138, x_4, x_5, x_14, x_15);
if (lean_obj_tag(x_139) == 0)
{
uint8_t x_140; 
lean_dec_ref(x_139);
x_140 = l_List_isEmpty___redArg(x_137);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; 
x_141 = lean_box(0);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_9);
lean_inc(x_137);
lean_inc(x_7);
x_142 = l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__6___redArg(x_7, x_4, x_141, x_137, x_137, x_141, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; 
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 x_143 = x_142;
} else {
 lean_dec_ref(x_142);
 x_143 = lean_box(0);
}
x_144 = l_List_get_x3fInternal___redArg(x_137, x_6);
lean_dec(x_137);
if (lean_obj_tag(x_144) == 1)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_dec(x_143);
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
lean_dec_ref(x_144);
x_146 = lean_st_ref_take(x_13);
x_147 = lean_ctor_get(x_145, 2);
lean_inc_ref(x_147);
x_148 = lean_ctor_get(x_145, 3);
lean_inc_ref(x_148);
lean_dec(x_145);
x_149 = lean_ctor_get(x_146, 1);
lean_inc_ref(x_149);
x_150 = lean_ctor_get(x_146, 2);
lean_inc(x_150);
x_151 = lean_ctor_get(x_146, 3);
lean_inc_ref(x_151);
x_152 = lean_ctor_get(x_146, 4);
lean_inc_ref(x_152);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 lean_ctor_release(x_146, 2);
 lean_ctor_release(x_146, 3);
 lean_ctor_release(x_146, 4);
 x_153 = x_146;
} else {
 lean_dec_ref(x_146);
 x_153 = lean_box(0);
}
if (lean_is_scalar(x_153)) {
 x_154 = lean_alloc_ctor(0, 5, 0);
} else {
 x_154 = x_153;
}
lean_ctor_set(x_154, 0, x_148);
lean_ctor_set(x_154, 1, x_149);
lean_ctor_set(x_154, 2, x_150);
lean_ctor_set(x_154, 3, x_151);
lean_ctor_set(x_154, 4, x_152);
x_155 = lean_st_ref_set(x_13, x_154);
x_156 = lean_ctor_get(x_147, 0);
lean_inc_ref(x_156);
x_157 = lean_ctor_get(x_147, 1);
lean_inc_ref(x_157);
x_158 = lean_ctor_get(x_147, 2);
lean_inc(x_158);
lean_dec_ref(x_147);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
x_159 = l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore(x_2, x_7, x_156, x_157, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
lean_dec_ref(x_159);
x_161 = lean_ctor_get(x_160, 1);
lean_inc(x_161);
lean_dec(x_160);
x_162 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_158);
x_163 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_162, x_9, x_12, x_13, x_14, x_15);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_9);
return x_163;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec(x_158);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_9);
x_164 = lean_ctor_get(x_159, 0);
lean_inc(x_164);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 x_165 = x_159;
} else {
 lean_dec_ref(x_159);
 x_165 = lean_box(0);
}
if (lean_is_scalar(x_165)) {
 x_166 = lean_alloc_ctor(1, 1, 0);
} else {
 x_166 = x_165;
}
lean_ctor_set(x_166, 0, x_164);
return x_166;
}
}
else
{
lean_object* x_167; 
lean_dec(x_144);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_2);
if (lean_is_scalar(x_143)) {
 x_167 = lean_alloc_ctor(0, 1, 0);
} else {
 x_167 = x_143;
}
lean_ctor_set(x_167, 0, x_141);
return x_167;
}
}
else
{
lean_dec(x_137);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_142;
}
}
else
{
lean_object* x_168; 
lean_dec(x_137);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_inc_ref(x_12);
x_168 = l_Lean_FVarId_getUserName___redArg(x_7, x_12, x_14, x_15);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
lean_dec_ref(x_168);
x_170 = l_Lean_Elab_Rewrites_evalExact___lam__1___closed__3;
x_171 = l_Lean_MessageData_ofName(x_169);
x_172 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_172, 0, x_170);
lean_ctor_set(x_172, 1, x_171);
x_173 = l_Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__1___redArg(x_172, x_12, x_13, x_14, x_15);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
return x_173;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; 
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
x_174 = lean_ctor_get(x_168, 0);
lean_inc(x_174);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 x_175 = x_168;
} else {
 lean_dec_ref(x_168);
 x_175 = lean_box(0);
}
if (lean_is_scalar(x_175)) {
 x_176 = lean_alloc_ctor(1, 1, 0);
} else {
 x_176 = x_175;
}
lean_ctor_set(x_176, 0, x_174);
return x_176;
}
}
}
else
{
lean_dec(x_137);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
return x_139;
}
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_177 = lean_ctor_get(x_136, 0);
lean_inc(x_177);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 x_178 = x_136;
} else {
 lean_dec_ref(x_136);
 x_178 = lean_box(0);
}
if (lean_is_scalar(x_178)) {
 x_179 = lean_alloc_ctor(1, 1, 0);
} else {
 x_179 = x_178;
}
lean_ctor_set(x_179, 0, x_177);
return x_179;
}
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; 
lean_dec(x_128);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_180 = lean_ctor_get(x_131, 0);
lean_inc(x_180);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 x_181 = x_131;
} else {
 lean_dec_ref(x_131);
 x_181 = lean_box(0);
}
if (lean_is_scalar(x_181)) {
 x_182 = lean_alloc_ctor(1, 1, 0);
} else {
 x_182 = x_181;
}
lean_ctor_set(x_182, 0, x_180);
return x_182;
}
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_183 = lean_ctor_get(x_125, 0);
lean_inc(x_183);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 x_184 = x_125;
} else {
 lean_dec_ref(x_125);
 x_184 = lean_box(0);
}
if (lean_is_scalar(x_184)) {
 x_185 = lean_alloc_ctor(1, 1, 0);
} else {
 x_185 = x_184;
}
lean_ctor_set(x_185, 0, x_183);
return x_185;
}
}
else
{
lean_object* x_186; lean_object* x_187; 
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_186 = lean_box(0);
x_187 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_187, 0, x_186);
return x_187;
}
}
else
{
lean_object* x_188; lean_object* x_189; 
lean_dec(x_122);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_188 = lean_box(0);
x_189 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_189, 0, x_188);
return x_189;
}
}
}
else
{
uint8_t x_190; 
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_190 = !lean_is_exclusive(x_17);
if (x_190 == 0)
{
return x_17;
}
else
{
lean_object* x_191; lean_object* x_192; 
x_191 = lean_ctor_get(x_17, 0);
lean_inc(x_191);
lean_dec(x_17);
x_192 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_192, 0, x_191);
return x_192;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Rewrites_evalExact___lam__2___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tacticTry_", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Rewrites_evalExact___lam__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("try", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Rewrites_evalExact___lam__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tacticSeq", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Rewrites_evalExact___lam__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Rewrites_evalExact___lam__2___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("null", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Rewrites_evalExact___lam__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Rewrites_evalExact___lam__2___closed__4;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Rewrites_evalExact___lam__2___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tacticRfl", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Rewrites_evalExact___lam__2___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("rfl", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Rewrites_evalExact___lam__2___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Could not find any lemmas which can rewrite the goal", 52, 52);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Rewrites_evalExact___lam__2___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Rewrites_evalExact___lam__2___closed__8;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
lean_object* x_20; 
lean_inc(x_1);
x_20 = l_Lean_MVarId_getType(x_1, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = l_Lean_instantiateMVars___at___00Lean_Elab_Rewrites_evalExact_spec__3___redArg(x_21, x_16);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_24 = lean_box(0);
lean_inc(x_18);
lean_inc_ref(x_17);
lean_inc(x_16);
lean_inc_ref(x_15);
x_25 = l_Lean_Meta_Rewrites_localHypotheses(x_24, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec_ref(x_25);
x_27 = 2;
x_28 = lean_unsigned_to_nat(20u);
x_29 = lean_unsigned_to_nat(10u);
lean_inc(x_18);
lean_inc_ref(x_17);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_1);
x_30 = l_Lean_Meta_Rewrites_findRewrites(x_26, x_2, x_1, x_23, x_3, x_27, x_4, x_28, x_29, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec_ref(x_30);
x_32 = l_Lean_Elab_Rewrites_evalExact___lam__1___closed__1;
lean_inc_ref(x_17);
x_33 = l_Lean_reportOutOfHeartbeats(x_32, x_5, x_6, x_17, x_18);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
lean_dec_ref(x_33);
x_34 = l_List_isEmpty___redArg(x_31);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = l_Lean_Elab_Tactic_saveState___redArg(x_12, x_14, x_16, x_18);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec_ref(x_35);
x_37 = l_List_get_x3fInternal___redArg(x_31, x_7);
if (lean_obj_tag(x_37) == 1)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
lean_dec(x_36);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
x_39 = lean_st_ref_take(x_16);
x_40 = lean_ctor_get(x_38, 2);
lean_inc_ref(x_40);
x_41 = lean_ctor_get(x_38, 3);
lean_inc_ref(x_41);
lean_dec(x_38);
x_42 = !lean_is_exclusive(x_39);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_39, 0);
lean_dec(x_43);
lean_ctor_set(x_39, 0, x_41);
x_44 = lean_st_ref_set(x_16, x_39);
x_45 = l_Lean_Elab_Tactic_saveState___redArg(x_12, x_14, x_16, x_18);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_dec_ref(x_45);
x_47 = lean_ctor_get(x_40, 0);
lean_inc_ref(x_47);
x_48 = lean_ctor_get(x_40, 1);
lean_inc_ref(x_48);
x_49 = lean_ctor_get(x_40, 2);
lean_inc(x_49);
lean_dec_ref(x_40);
lean_inc(x_18);
lean_inc_ref(x_17);
lean_inc(x_16);
lean_inc_ref(x_15);
x_50 = l_Lean_MVarId_replaceTargetEq(x_1, x_47, x_48, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
lean_dec_ref(x_50);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_49);
x_53 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_52, x_12, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec_ref(x_53);
x_54 = lean_ctor_get(x_17, 5);
x_55 = l_Lean_SourceInfo_fromRef(x_54, x_34);
x_56 = l_Lean_Elab_Rewrites_evalExact___lam__2___closed__0;
lean_inc_ref(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_8);
x_57 = l_Lean_Name_mkStr4(x_8, x_9, x_10, x_56);
x_58 = l_Lean_Elab_Rewrites_evalExact___lam__2___closed__1;
lean_inc(x_55);
x_59 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_59, 0, x_55);
lean_ctor_set(x_59, 1, x_58);
x_60 = l_Lean_Elab_Rewrites_evalExact___lam__2___closed__2;
lean_inc_ref(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_8);
x_61 = l_Lean_Name_mkStr4(x_8, x_9, x_10, x_60);
x_62 = l_Lean_Elab_Rewrites_evalExact___lam__2___closed__3;
lean_inc_ref(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_8);
x_63 = l_Lean_Name_mkStr4(x_8, x_9, x_10, x_62);
x_64 = l_Lean_Elab_Rewrites_evalExact___lam__2___closed__5;
x_65 = l_Lean_Elab_Rewrites_evalExact___lam__2___closed__6;
x_66 = l_Lean_Name_mkStr4(x_8, x_9, x_10, x_65);
x_67 = l_Lean_Elab_Rewrites_evalExact___lam__2___closed__7;
lean_inc(x_55);
x_68 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_68, 0, x_55);
lean_ctor_set(x_68, 1, x_67);
lean_inc(x_55);
x_69 = l_Lean_Syntax_node1(x_55, x_66, x_68);
lean_inc(x_55);
x_70 = l_Lean_Syntax_node1(x_55, x_64, x_69);
lean_inc(x_55);
x_71 = l_Lean_Syntax_node1(x_55, x_63, x_70);
lean_inc(x_55);
x_72 = l_Lean_Syntax_node1(x_55, x_61, x_71);
x_73 = l_Lean_Syntax_node2(x_55, x_57, x_59, x_72);
lean_inc(x_18);
lean_inc_ref(x_17);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
x_74 = l_Lean_Elab_Tactic_evalTactic(x_73, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; 
lean_dec_ref(x_74);
x_75 = l_List_forM___at___00Lean_Elab_Rewrites_evalExact_spec__4(x_46, x_5, x_31, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
return x_75;
}
else
{
lean_dec(x_46);
lean_dec(x_31);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_5);
return x_74;
}
}
else
{
lean_dec(x_46);
lean_dec(x_31);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_5);
return x_53;
}
}
else
{
uint8_t x_76; 
lean_dec(x_49);
lean_dec(x_46);
lean_dec(x_31);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_5);
x_76 = !lean_is_exclusive(x_50);
if (x_76 == 0)
{
return x_50;
}
else
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_50, 0);
lean_inc(x_77);
lean_dec(x_50);
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_77);
return x_78;
}
}
}
else
{
uint8_t x_79; 
lean_dec_ref(x_40);
lean_dec(x_31);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_5);
lean_dec(x_1);
x_79 = !lean_is_exclusive(x_45);
if (x_79 == 0)
{
return x_45;
}
else
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_45, 0);
lean_inc(x_80);
lean_dec(x_45);
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_80);
return x_81;
}
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_82 = lean_ctor_get(x_39, 1);
x_83 = lean_ctor_get(x_39, 2);
x_84 = lean_ctor_get(x_39, 3);
x_85 = lean_ctor_get(x_39, 4);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_39);
x_86 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_86, 0, x_41);
lean_ctor_set(x_86, 1, x_82);
lean_ctor_set(x_86, 2, x_83);
lean_ctor_set(x_86, 3, x_84);
lean_ctor_set(x_86, 4, x_85);
x_87 = lean_st_ref_set(x_16, x_86);
x_88 = l_Lean_Elab_Tactic_saveState___redArg(x_12, x_14, x_16, x_18);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
lean_dec_ref(x_88);
x_90 = lean_ctor_get(x_40, 0);
lean_inc_ref(x_90);
x_91 = lean_ctor_get(x_40, 1);
lean_inc_ref(x_91);
x_92 = lean_ctor_get(x_40, 2);
lean_inc(x_92);
lean_dec_ref(x_40);
lean_inc(x_18);
lean_inc_ref(x_17);
lean_inc(x_16);
lean_inc_ref(x_15);
x_93 = l_Lean_MVarId_replaceTargetEq(x_1, x_90, x_91, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
lean_dec_ref(x_93);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_92);
x_96 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_95, x_12, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec_ref(x_96);
x_97 = lean_ctor_get(x_17, 5);
x_98 = l_Lean_SourceInfo_fromRef(x_97, x_34);
x_99 = l_Lean_Elab_Rewrites_evalExact___lam__2___closed__0;
lean_inc_ref(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_8);
x_100 = l_Lean_Name_mkStr4(x_8, x_9, x_10, x_99);
x_101 = l_Lean_Elab_Rewrites_evalExact___lam__2___closed__1;
lean_inc(x_98);
x_102 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_102, 0, x_98);
lean_ctor_set(x_102, 1, x_101);
x_103 = l_Lean_Elab_Rewrites_evalExact___lam__2___closed__2;
lean_inc_ref(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_8);
x_104 = l_Lean_Name_mkStr4(x_8, x_9, x_10, x_103);
x_105 = l_Lean_Elab_Rewrites_evalExact___lam__2___closed__3;
lean_inc_ref(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_8);
x_106 = l_Lean_Name_mkStr4(x_8, x_9, x_10, x_105);
x_107 = l_Lean_Elab_Rewrites_evalExact___lam__2___closed__5;
x_108 = l_Lean_Elab_Rewrites_evalExact___lam__2___closed__6;
x_109 = l_Lean_Name_mkStr4(x_8, x_9, x_10, x_108);
x_110 = l_Lean_Elab_Rewrites_evalExact___lam__2___closed__7;
lean_inc(x_98);
x_111 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_111, 0, x_98);
lean_ctor_set(x_111, 1, x_110);
lean_inc(x_98);
x_112 = l_Lean_Syntax_node1(x_98, x_109, x_111);
lean_inc(x_98);
x_113 = l_Lean_Syntax_node1(x_98, x_107, x_112);
lean_inc(x_98);
x_114 = l_Lean_Syntax_node1(x_98, x_106, x_113);
lean_inc(x_98);
x_115 = l_Lean_Syntax_node1(x_98, x_104, x_114);
x_116 = l_Lean_Syntax_node2(x_98, x_100, x_102, x_115);
lean_inc(x_18);
lean_inc_ref(x_17);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
x_117 = l_Lean_Elab_Tactic_evalTactic(x_116, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; 
lean_dec_ref(x_117);
x_118 = l_List_forM___at___00Lean_Elab_Rewrites_evalExact_spec__4(x_89, x_5, x_31, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
return x_118;
}
else
{
lean_dec(x_89);
lean_dec(x_31);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_5);
return x_117;
}
}
else
{
lean_dec(x_89);
lean_dec(x_31);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_5);
return x_96;
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_92);
lean_dec(x_89);
lean_dec(x_31);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_5);
x_119 = lean_ctor_get(x_93, 0);
lean_inc(x_119);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 x_120 = x_93;
} else {
 lean_dec_ref(x_93);
 x_120 = lean_box(0);
}
if (lean_is_scalar(x_120)) {
 x_121 = lean_alloc_ctor(1, 1, 0);
} else {
 x_121 = x_120;
}
lean_ctor_set(x_121, 0, x_119);
return x_121;
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec_ref(x_40);
lean_dec(x_31);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_5);
lean_dec(x_1);
x_122 = lean_ctor_get(x_88, 0);
lean_inc(x_122);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 x_123 = x_88;
} else {
 lean_dec_ref(x_88);
 x_123 = lean_box(0);
}
if (lean_is_scalar(x_123)) {
 x_124 = lean_alloc_ctor(1, 1, 0);
} else {
 x_124 = x_123;
}
lean_ctor_set(x_124, 0, x_122);
return x_124;
}
}
}
else
{
lean_object* x_125; 
lean_dec(x_37);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_1);
x_125 = l_List_forM___at___00Lean_Elab_Rewrites_evalExact_spec__4(x_36, x_5, x_31, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
return x_125;
}
}
else
{
uint8_t x_126; 
lean_dec(x_31);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_126 = !lean_is_exclusive(x_35);
if (x_126 == 0)
{
return x_35;
}
else
{
lean_object* x_127; lean_object* x_128; 
x_127 = lean_ctor_get(x_35, 0);
lean_inc(x_127);
lean_dec(x_35);
x_128 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_128, 0, x_127);
return x_128;
}
}
}
else
{
lean_object* x_129; lean_object* x_130; 
lean_dec(x_31);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_129 = l_Lean_Elab_Rewrites_evalExact___lam__2___closed__9;
x_130 = l_Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__1___redArg(x_129, x_15, x_16, x_17, x_18);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
return x_130;
}
}
else
{
lean_dec(x_31);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
return x_33;
}
}
else
{
uint8_t x_131; 
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_131 = !lean_is_exclusive(x_30);
if (x_131 == 0)
{
return x_30;
}
else
{
lean_object* x_132; lean_object* x_133; 
x_132 = lean_ctor_get(x_30, 0);
lean_inc(x_132);
lean_dec(x_30);
x_133 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_133, 0, x_132);
return x_133;
}
}
}
else
{
uint8_t x_134; 
lean_dec(x_23);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_134 = !lean_is_exclusive(x_25);
if (x_134 == 0)
{
return x_25;
}
else
{
lean_object* x_135; lean_object* x_136; 
x_135 = lean_ctor_get(x_25, 0);
lean_inc(x_135);
lean_dec(x_25);
x_136 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_136, 0, x_135);
return x_136;
}
}
}
else
{
uint8_t x_137; 
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_137 = !lean_is_exclusive(x_20);
if (x_137 == 0)
{
return x_20;
}
else
{
lean_object* x_138; lean_object* x_139; 
x_138 = lean_ctor_get(x_20, 0);
lean_inc(x_138);
lean_dec(x_20);
x_139 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_139, 0, x_138);
return x_139;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Rewrites_evalExact___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Rewrites_evalExact___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Rewrites_evalExact___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Rewrites_evalExact___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("rewrites\?", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Rewrites_evalExact___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Rewrites_evalExact___closed__3;
x_2 = l_Lean_Elab_Rewrites_evalExact___closed__2;
x_3 = l_Lean_Elab_Rewrites_evalExact___closed__1;
x_4 = l_Lean_Elab_Rewrites_evalExact___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Rewrites_evalExact___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("findRewrites", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Rewrites_evalExact___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Rewrites_evalExact___closed__5;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Rewrites_evalExact___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_NameSet_empty;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Rewrites_evalExact___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Rewrites_evalExact___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("rewrites_forbidden", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Rewrites_evalExact___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Rewrites_evalExact___closed__9;
x_2 = l_Lean_Elab_Rewrites_evalExact___closed__2;
x_3 = l_Lean_Elab_Rewrites_evalExact___closed__1;
x_4 = l_Lean_Elab_Rewrites_evalExact___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Rewrites_evalExact___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_28 = l_Lean_Elab_Rewrites_evalExact___closed__0;
x_29 = l_Lean_Elab_Rewrites_evalExact___closed__1;
x_30 = l_Lean_Elab_Rewrites_evalExact___closed__2;
x_31 = l_Lean_Elab_Rewrites_evalExact___closed__4;
lean_inc(x_1);
x_32 = l_Lean_Syntax_isOfKind(x_1, x_31);
if (x_32 == 0)
{
lean_object* x_33; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_33 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__0___redArg();
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_159; uint8_t x_160; 
x_34 = lean_alloc_closure((void*)(l_Lean_Elab_Rewrites_evalExact___lam__0___boxed), 10, 0);
x_35 = lean_unsigned_to_nat(0u);
x_36 = l_Lean_Syntax_getArg(x_1, x_35);
x_109 = lean_unsigned_to_nat(1u);
x_159 = l_Lean_Syntax_getArg(x_1, x_109);
x_160 = l_Lean_Syntax_isNone(x_159);
if (x_160 == 0)
{
uint8_t x_161; 
lean_inc(x_159);
x_161 = l_Lean_Syntax_matchesNull(x_159, x_109);
if (x_161 == 0)
{
lean_object* x_162; 
lean_dec(x_159);
lean_dec(x_36);
lean_dec_ref(x_34);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_162 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__0___redArg();
return x_162;
}
else
{
lean_object* x_163; lean_object* x_164; 
x_163 = l_Lean_Syntax_getArg(x_159, x_35);
lean_dec(x_159);
x_164 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_164, 0, x_163);
x_126 = x_164;
x_127 = x_2;
x_128 = x_3;
x_129 = x_4;
x_130 = x_5;
x_131 = x_6;
x_132 = x_7;
x_133 = x_8;
x_134 = x_9;
x_135 = lean_box(0);
goto block_158;
}
}
else
{
lean_object* x_165; 
lean_dec(x_159);
x_165 = lean_box(0);
x_126 = x_165;
x_127 = x_2;
x_128 = x_3;
x_129 = x_4;
x_130 = x_5;
x_131 = x_6;
x_132 = x_7;
x_133 = x_8;
x_134 = x_9;
x_135 = lean_box(0);
goto block_158;
}
block_65:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = l_Lean_Elab_Rewrites_evalExact___closed__6;
x_51 = lean_unsigned_to_nat(90u);
lean_inc_ref(x_47);
x_52 = l_Lean_reportOutOfHeartbeats(x_50, x_36, x_51, x_47, x_39);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; 
lean_dec_ref(x_52);
x_53 = l_Lean_Elab_Tactic_getMainGoal___redArg(x_45, x_41, x_43, x_47, x_39);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
lean_dec_ref(x_53);
lean_inc(x_36);
lean_inc(x_49);
lean_inc(x_54);
lean_inc(x_37);
x_55 = lean_alloc_closure((void*)(l_Lean_Elab_Rewrites_evalExact___lam__1___boxed), 16, 6);
lean_closure_set(x_55, 0, x_37);
lean_closure_set(x_55, 1, x_54);
lean_closure_set(x_55, 2, x_49);
lean_closure_set(x_55, 3, x_36);
lean_closure_set(x_55, 4, x_51);
lean_closure_set(x_55, 5, x_35);
x_56 = lean_box(x_32);
x_57 = lean_alloc_closure((void*)(l_Lean_Elab_Rewrites_evalExact___lam__2___boxed), 19, 10);
lean_closure_set(x_57, 0, x_54);
lean_closure_set(x_57, 1, x_37);
lean_closure_set(x_57, 2, x_49);
lean_closure_set(x_57, 3, x_56);
lean_closure_set(x_57, 4, x_36);
lean_closure_set(x_57, 5, x_51);
lean_closure_set(x_57, 6, x_35);
lean_closure_set(x_57, 7, x_28);
lean_closure_set(x_57, 8, x_29);
lean_closure_set(x_57, 9, x_30);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_58; 
x_58 = lean_box(0);
x_11 = x_38;
x_12 = x_39;
x_13 = x_57;
x_14 = x_40;
x_15 = lean_box(0);
x_16 = x_41;
x_17 = x_43;
x_18 = x_44;
x_19 = x_45;
x_20 = x_55;
x_21 = x_47;
x_22 = x_48;
x_23 = x_58;
goto block_27;
}
else
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_42);
if (x_59 == 0)
{
x_11 = x_38;
x_12 = x_39;
x_13 = x_57;
x_14 = x_40;
x_15 = lean_box(0);
x_16 = x_41;
x_17 = x_43;
x_18 = x_44;
x_19 = x_45;
x_20 = x_55;
x_21 = x_47;
x_22 = x_48;
x_23 = x_42;
goto block_27;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_42, 0);
lean_inc(x_60);
lean_dec(x_42);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
x_11 = x_38;
x_12 = x_39;
x_13 = x_57;
x_14 = x_40;
x_15 = lean_box(0);
x_16 = x_41;
x_17 = x_43;
x_18 = x_44;
x_19 = x_45;
x_20 = x_55;
x_21 = x_47;
x_22 = x_48;
x_23 = x_61;
goto block_27;
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_49);
lean_dec(x_48);
lean_dec_ref(x_47);
lean_dec(x_45);
lean_dec_ref(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec_ref(x_40);
lean_dec(x_39);
lean_dec_ref(x_38);
lean_dec(x_37);
lean_dec(x_36);
x_62 = !lean_is_exclusive(x_53);
if (x_62 == 0)
{
return x_53;
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_53, 0);
lean_inc(x_63);
lean_dec(x_53);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
return x_64;
}
}
}
else
{
lean_dec(x_49);
lean_dec(x_48);
lean_dec_ref(x_47);
lean_dec(x_45);
lean_dec_ref(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec_ref(x_40);
lean_dec(x_39);
lean_dec_ref(x_38);
lean_dec(x_37);
lean_dec(x_36);
return x_52;
}
}
block_88:
{
size_t x_80; size_t x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_80 = lean_array_size(x_79);
x_81 = 0;
x_82 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__8(x_80, x_81, x_79);
x_83 = lean_array_get_size(x_82);
x_84 = lean_nat_dec_lt(x_35, x_83);
if (x_84 == 0)
{
lean_dec(x_83);
lean_dec_ref(x_82);
x_37 = x_67;
x_38 = x_68;
x_39 = x_69;
x_40 = x_70;
x_41 = x_71;
x_42 = x_74;
x_43 = x_73;
x_44 = x_75;
x_45 = x_76;
x_46 = lean_box(0);
x_47 = x_77;
x_48 = x_78;
x_49 = x_72;
goto block_65;
}
else
{
uint8_t x_85; 
x_85 = lean_nat_dec_le(x_83, x_83);
if (x_85 == 0)
{
lean_dec(x_83);
lean_dec_ref(x_82);
x_37 = x_67;
x_38 = x_68;
x_39 = x_69;
x_40 = x_70;
x_41 = x_71;
x_42 = x_74;
x_43 = x_73;
x_44 = x_75;
x_45 = x_76;
x_46 = lean_box(0);
x_47 = x_77;
x_48 = x_78;
x_49 = x_72;
goto block_65;
}
else
{
size_t x_86; lean_object* x_87; 
x_86 = lean_usize_of_nat(x_83);
lean_dec(x_83);
x_87 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Rewrites_evalExact_spec__9(x_82, x_81, x_86, x_72);
lean_dec_ref(x_82);
x_37 = x_67;
x_38 = x_68;
x_39 = x_69;
x_40 = x_70;
x_41 = x_71;
x_42 = x_74;
x_43 = x_73;
x_44 = x_75;
x_45 = x_76;
x_46 = lean_box(0);
x_47 = x_77;
x_48 = x_78;
x_49 = x_87;
goto block_65;
}
}
}
block_108:
{
lean_object* x_100; 
lean_inc(x_98);
lean_inc_ref(x_97);
lean_inc(x_96);
lean_inc_ref(x_95);
x_100 = l_Lean_Meta_Rewrites_createModuleTreeRef(x_95, x_96, x_97, x_98);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
lean_dec_ref(x_100);
x_102 = l_Lean_Elab_Rewrites_evalExact___closed__7;
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_103; 
x_103 = l_Lean_Elab_Rewrites_evalExact___closed__8;
x_66 = lean_box(0);
x_67 = x_101;
x_68 = x_91;
x_69 = x_98;
x_70 = x_34;
x_71 = x_95;
x_72 = x_102;
x_73 = x_96;
x_74 = x_89;
x_75 = x_93;
x_76 = x_92;
x_77 = x_97;
x_78 = x_94;
x_79 = x_103;
goto block_88;
}
else
{
lean_object* x_104; 
x_104 = lean_ctor_get(x_90, 0);
lean_inc(x_104);
lean_dec_ref(x_90);
x_66 = lean_box(0);
x_67 = x_101;
x_68 = x_91;
x_69 = x_98;
x_70 = x_34;
x_71 = x_95;
x_72 = x_102;
x_73 = x_96;
x_74 = x_89;
x_75 = x_93;
x_76 = x_92;
x_77 = x_97;
x_78 = x_94;
x_79 = x_104;
goto block_88;
}
}
else
{
uint8_t x_105; 
lean_dec(x_98);
lean_dec_ref(x_97);
lean_dec(x_96);
lean_dec_ref(x_95);
lean_dec(x_94);
lean_dec_ref(x_93);
lean_dec(x_92);
lean_dec_ref(x_91);
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_36);
lean_dec_ref(x_34);
x_105 = !lean_is_exclusive(x_100);
if (x_105 == 0)
{
return x_100;
}
else
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_100, 0);
lean_inc(x_106);
lean_dec(x_100);
x_107 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_107, 0, x_106);
return x_107;
}
}
}
block_125:
{
size_t x_121; size_t x_122; lean_object* x_123; 
x_121 = lean_array_size(x_120);
x_122 = 0;
x_123 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__10(x_109, x_121, x_122, x_120);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; 
lean_dec_ref(x_118);
lean_dec(x_117);
lean_dec(x_116);
lean_dec_ref(x_115);
lean_dec(x_114);
lean_dec_ref(x_113);
lean_dec(x_112);
lean_dec_ref(x_111);
lean_dec(x_110);
lean_dec(x_36);
lean_dec_ref(x_34);
x_124 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__0___redArg();
return x_124;
}
else
{
x_89 = x_116;
x_90 = x_123;
x_91 = x_115;
x_92 = x_114;
x_93 = x_111;
x_94 = x_110;
x_95 = x_113;
x_96 = x_117;
x_97 = x_118;
x_98 = x_112;
x_99 = lean_box(0);
goto block_108;
}
}
block_158:
{
lean_object* x_136; lean_object* x_137; uint8_t x_138; 
x_136 = lean_unsigned_to_nat(2u);
x_137 = l_Lean_Syntax_getArg(x_1, x_136);
lean_dec(x_1);
x_138 = l_Lean_Syntax_isNone(x_137);
if (x_138 == 0)
{
uint8_t x_139; 
lean_inc(x_137);
x_139 = l_Lean_Syntax_matchesNull(x_137, x_109);
if (x_139 == 0)
{
lean_object* x_140; 
lean_dec(x_137);
lean_dec(x_134);
lean_dec_ref(x_133);
lean_dec(x_132);
lean_dec_ref(x_131);
lean_dec(x_130);
lean_dec_ref(x_129);
lean_dec(x_128);
lean_dec_ref(x_127);
lean_dec(x_126);
lean_dec(x_36);
lean_dec_ref(x_34);
x_140 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__0___redArg();
return x_140;
}
else
{
lean_object* x_141; lean_object* x_142; uint8_t x_143; 
x_141 = l_Lean_Syntax_getArg(x_137, x_35);
lean_dec(x_137);
x_142 = l_Lean_Elab_Rewrites_evalExact___closed__10;
lean_inc(x_141);
x_143 = l_Lean_Syntax_isOfKind(x_141, x_142);
if (x_143 == 0)
{
lean_object* x_144; 
lean_dec(x_141);
lean_dec(x_134);
lean_dec_ref(x_133);
lean_dec(x_132);
lean_dec_ref(x_131);
lean_dec(x_130);
lean_dec_ref(x_129);
lean_dec(x_128);
lean_dec_ref(x_127);
lean_dec(x_126);
lean_dec(x_36);
lean_dec_ref(x_34);
x_144 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__0___redArg();
return x_144;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; 
x_145 = l_Lean_Syntax_getArg(x_141, x_109);
lean_dec(x_141);
x_146 = l_Lean_Syntax_getArgs(x_145);
lean_dec(x_145);
x_147 = l_Lean_Elab_Rewrites_evalExact___closed__11;
x_148 = lean_array_get_size(x_146);
x_149 = lean_nat_dec_lt(x_35, x_148);
if (x_149 == 0)
{
lean_dec(x_148);
lean_dec_ref(x_146);
x_110 = x_130;
x_111 = x_129;
x_112 = x_134;
x_113 = x_131;
x_114 = x_128;
x_115 = x_127;
x_116 = x_126;
x_117 = x_132;
x_118 = x_133;
x_119 = lean_box(0);
x_120 = x_147;
goto block_125;
}
else
{
uint8_t x_150; 
x_150 = lean_nat_dec_le(x_148, x_148);
if (x_150 == 0)
{
lean_dec(x_148);
lean_dec_ref(x_146);
x_110 = x_130;
x_111 = x_129;
x_112 = x_134;
x_113 = x_131;
x_114 = x_128;
x_115 = x_127;
x_116 = x_126;
x_117 = x_132;
x_118 = x_133;
x_119 = lean_box(0);
x_120 = x_147;
goto block_125;
}
else
{
lean_object* x_151; lean_object* x_152; size_t x_153; size_t x_154; lean_object* x_155; lean_object* x_156; 
x_151 = lean_box(x_143);
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_147);
x_153 = 0;
x_154 = lean_usize_of_nat(x_148);
lean_dec(x_148);
x_155 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Rewrites_evalExact_spec__11(x_143, x_138, x_146, x_153, x_154, x_152);
lean_dec_ref(x_146);
x_156 = lean_ctor_get(x_155, 1);
lean_inc(x_156);
lean_dec_ref(x_155);
x_110 = x_130;
x_111 = x_129;
x_112 = x_134;
x_113 = x_131;
x_114 = x_128;
x_115 = x_127;
x_116 = x_126;
x_117 = x_132;
x_118 = x_133;
x_119 = lean_box(0);
x_120 = x_156;
goto block_125;
}
}
}
}
}
else
{
lean_object* x_157; 
lean_dec(x_137);
x_157 = lean_box(0);
x_89 = x_126;
x_90 = x_157;
x_91 = x_127;
x_92 = x_128;
x_93 = x_129;
x_94 = x_130;
x_95 = x_131;
x_96 = x_132;
x_97 = x_133;
x_98 = x_134;
x_99 = lean_box(0);
goto block_108;
}
}
}
block_27:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = l_Lean_mkOptionalNode(x_23);
x_25 = l_Lean_Elab_Tactic_expandOptLocation(x_24);
lean_dec(x_24);
x_26 = l_Lean_Elab_Tactic_withLocation(x_25, x_20, x_13, x_14, x_11, x_19, x_18, x_22, x_16, x_17, x_21, x_12);
lean_dec(x_25);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__0___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__0___redArg();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__1___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Rewrites_evalExact_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_instantiateMVars___at___00Lean_Elab_Rewrites_evalExact_spec__3___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Rewrites_evalExact_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_instantiateMVars___at___00Lean_Elab_Rewrites_evalExact_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_Rewrites_evalExact_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_List_forM___at___00Lean_Elab_Rewrites_evalExact_spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Elab_Rewrites_evalExact_spec__5___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_withMCtx___at___00Lean_Elab_Rewrites_evalExact_spec__5___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Elab_Rewrites_evalExact_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_withMCtx___at___00Lean_Elab_Rewrites_evalExact_spec__5___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Elab_Rewrites_evalExact_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_withMCtx___at___00Lean_Elab_Rewrites_evalExact_spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__6_spec__6___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_3);
x_16 = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__6_spec__6___redArg___lam__0(x_1, x_2, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__6_spec__6___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__6_spec__6___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__6_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__6_spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_4);
return x_17;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__6___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__6___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_4);
return x_16;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_4);
return x_17;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__8(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Rewrites_evalExact_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Rewrites_evalExact_spec__9(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__10(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Rewrites_evalExact_spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_7 = lean_unbox(x_1);
x_8 = lean_unbox(x_2);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_11 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Rewrites_evalExact_spec__11(x_7, x_8, x_3, x_9, x_10, x_6);
lean_dec_ref(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Rewrites_evalExact___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Lean_Elab_Rewrites_evalExact___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_5);
lean_dec(x_3);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact___lam__2___boxed(lean_object** _args) {
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
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
_start:
{
uint8_t x_20; lean_object* x_21; 
x_20 = lean_unbox(x_4);
x_21 = l_Lean_Elab_Rewrites_evalExact___lam__2(x_1, x_2, x_3, x_20, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_6);
lean_dec(x_3);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Rewrites_evalExact(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
static lean_object* _init_l_Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Tactic_tacticElabAttribute;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Elab", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Rewrites", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("evalExact", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___closed__3;
x_2 = l_Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___closed__2;
x_3 = l_Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___closed__1;
x_4 = l_Lean_Elab_Rewrites_evalExact___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___closed__0;
x_3 = l_Lean_Elab_Rewrites_evalExact___closed__4;
x_4 = l_Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___closed__4;
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Rewrites_evalExact___boxed), 10, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1();
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_unsigned_to_nat(29u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(70u);
x_2 = lean_unsigned_to_nat(67u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(70u);
x_2 = l_Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__1;
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__0;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(29u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(13u);
x_2 = lean_unsigned_to_nat(29u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(13u);
x_2 = l_Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__4;
x_3 = lean_unsigned_to_nat(4u);
x_4 = l_Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__3;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__5;
x_2 = l_Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___closed__4;
x_3 = l_Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__6;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3();
return x_2;
}
}
lean_object* initialize_Lean_Elab_Tactic_Location(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Replace(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Rewrites(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Rewrites(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Location(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Replace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Rewrites(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__0___redArg___closed__0 = _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__0___redArg___closed__0();
lean_mark_persistent(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__0___redArg___closed__0);
l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__0___redArg___closed__1 = _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__0___redArg___closed__1();
lean_mark_persistent(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__0___redArg___closed__1);
l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__10___closed__0 = _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__10___closed__0();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__10___closed__0);
l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__10___closed__1 = _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__10___closed__1();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__10___closed__1);
l_Lean_Elab_Rewrites_evalExact___lam__0___closed__0 = _init_l_Lean_Elab_Rewrites_evalExact___lam__0___closed__0();
lean_mark_persistent(l_Lean_Elab_Rewrites_evalExact___lam__0___closed__0);
l_Lean_Elab_Rewrites_evalExact___lam__0___closed__1 = _init_l_Lean_Elab_Rewrites_evalExact___lam__0___closed__1();
lean_mark_persistent(l_Lean_Elab_Rewrites_evalExact___lam__0___closed__1);
l_Lean_Elab_Rewrites_evalExact___lam__1___closed__0 = _init_l_Lean_Elab_Rewrites_evalExact___lam__1___closed__0();
lean_mark_persistent(l_Lean_Elab_Rewrites_evalExact___lam__1___closed__0);
l_Lean_Elab_Rewrites_evalExact___lam__1___closed__1 = _init_l_Lean_Elab_Rewrites_evalExact___lam__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Rewrites_evalExact___lam__1___closed__1);
l_Lean_Elab_Rewrites_evalExact___lam__1___closed__2 = _init_l_Lean_Elab_Rewrites_evalExact___lam__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Rewrites_evalExact___lam__1___closed__2);
l_Lean_Elab_Rewrites_evalExact___lam__1___closed__3 = _init_l_Lean_Elab_Rewrites_evalExact___lam__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Rewrites_evalExact___lam__1___closed__3);
l_Lean_Elab_Rewrites_evalExact___lam__2___closed__0 = _init_l_Lean_Elab_Rewrites_evalExact___lam__2___closed__0();
lean_mark_persistent(l_Lean_Elab_Rewrites_evalExact___lam__2___closed__0);
l_Lean_Elab_Rewrites_evalExact___lam__2___closed__1 = _init_l_Lean_Elab_Rewrites_evalExact___lam__2___closed__1();
lean_mark_persistent(l_Lean_Elab_Rewrites_evalExact___lam__2___closed__1);
l_Lean_Elab_Rewrites_evalExact___lam__2___closed__2 = _init_l_Lean_Elab_Rewrites_evalExact___lam__2___closed__2();
lean_mark_persistent(l_Lean_Elab_Rewrites_evalExact___lam__2___closed__2);
l_Lean_Elab_Rewrites_evalExact___lam__2___closed__3 = _init_l_Lean_Elab_Rewrites_evalExact___lam__2___closed__3();
lean_mark_persistent(l_Lean_Elab_Rewrites_evalExact___lam__2___closed__3);
l_Lean_Elab_Rewrites_evalExact___lam__2___closed__4 = _init_l_Lean_Elab_Rewrites_evalExact___lam__2___closed__4();
lean_mark_persistent(l_Lean_Elab_Rewrites_evalExact___lam__2___closed__4);
l_Lean_Elab_Rewrites_evalExact___lam__2___closed__5 = _init_l_Lean_Elab_Rewrites_evalExact___lam__2___closed__5();
lean_mark_persistent(l_Lean_Elab_Rewrites_evalExact___lam__2___closed__5);
l_Lean_Elab_Rewrites_evalExact___lam__2___closed__6 = _init_l_Lean_Elab_Rewrites_evalExact___lam__2___closed__6();
lean_mark_persistent(l_Lean_Elab_Rewrites_evalExact___lam__2___closed__6);
l_Lean_Elab_Rewrites_evalExact___lam__2___closed__7 = _init_l_Lean_Elab_Rewrites_evalExact___lam__2___closed__7();
lean_mark_persistent(l_Lean_Elab_Rewrites_evalExact___lam__2___closed__7);
l_Lean_Elab_Rewrites_evalExact___lam__2___closed__8 = _init_l_Lean_Elab_Rewrites_evalExact___lam__2___closed__8();
lean_mark_persistent(l_Lean_Elab_Rewrites_evalExact___lam__2___closed__8);
l_Lean_Elab_Rewrites_evalExact___lam__2___closed__9 = _init_l_Lean_Elab_Rewrites_evalExact___lam__2___closed__9();
lean_mark_persistent(l_Lean_Elab_Rewrites_evalExact___lam__2___closed__9);
l_Lean_Elab_Rewrites_evalExact___closed__0 = _init_l_Lean_Elab_Rewrites_evalExact___closed__0();
lean_mark_persistent(l_Lean_Elab_Rewrites_evalExact___closed__0);
l_Lean_Elab_Rewrites_evalExact___closed__1 = _init_l_Lean_Elab_Rewrites_evalExact___closed__1();
lean_mark_persistent(l_Lean_Elab_Rewrites_evalExact___closed__1);
l_Lean_Elab_Rewrites_evalExact___closed__2 = _init_l_Lean_Elab_Rewrites_evalExact___closed__2();
lean_mark_persistent(l_Lean_Elab_Rewrites_evalExact___closed__2);
l_Lean_Elab_Rewrites_evalExact___closed__3 = _init_l_Lean_Elab_Rewrites_evalExact___closed__3();
lean_mark_persistent(l_Lean_Elab_Rewrites_evalExact___closed__3);
l_Lean_Elab_Rewrites_evalExact___closed__4 = _init_l_Lean_Elab_Rewrites_evalExact___closed__4();
lean_mark_persistent(l_Lean_Elab_Rewrites_evalExact___closed__4);
l_Lean_Elab_Rewrites_evalExact___closed__5 = _init_l_Lean_Elab_Rewrites_evalExact___closed__5();
lean_mark_persistent(l_Lean_Elab_Rewrites_evalExact___closed__5);
l_Lean_Elab_Rewrites_evalExact___closed__6 = _init_l_Lean_Elab_Rewrites_evalExact___closed__6();
lean_mark_persistent(l_Lean_Elab_Rewrites_evalExact___closed__6);
l_Lean_Elab_Rewrites_evalExact___closed__7 = _init_l_Lean_Elab_Rewrites_evalExact___closed__7();
lean_mark_persistent(l_Lean_Elab_Rewrites_evalExact___closed__7);
l_Lean_Elab_Rewrites_evalExact___closed__8 = _init_l_Lean_Elab_Rewrites_evalExact___closed__8();
lean_mark_persistent(l_Lean_Elab_Rewrites_evalExact___closed__8);
l_Lean_Elab_Rewrites_evalExact___closed__9 = _init_l_Lean_Elab_Rewrites_evalExact___closed__9();
lean_mark_persistent(l_Lean_Elab_Rewrites_evalExact___closed__9);
l_Lean_Elab_Rewrites_evalExact___closed__10 = _init_l_Lean_Elab_Rewrites_evalExact___closed__10();
lean_mark_persistent(l_Lean_Elab_Rewrites_evalExact___closed__10);
l_Lean_Elab_Rewrites_evalExact___closed__11 = _init_l_Lean_Elab_Rewrites_evalExact___closed__11();
lean_mark_persistent(l_Lean_Elab_Rewrites_evalExact___closed__11);
l_Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___closed__0 = _init_l_Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___closed__0();
lean_mark_persistent(l_Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___closed__0);
l_Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___closed__1 = _init_l_Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___closed__1);
l_Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___closed__2 = _init_l_Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___closed__2);
l_Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___closed__3 = _init_l_Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___closed__3);
l_Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___closed__4 = _init_l_Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___closed__4();
lean_mark_persistent(l_Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___closed__4);
if (builtin) {res = l_Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__0 = _init_l_Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__0();
lean_mark_persistent(l_Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__0);
l_Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__1 = _init_l_Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__1();
lean_mark_persistent(l_Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__1);
l_Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__2 = _init_l_Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__2();
lean_mark_persistent(l_Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__2);
l_Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__3 = _init_l_Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__3();
lean_mark_persistent(l_Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__3);
l_Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__4 = _init_l_Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__4();
lean_mark_persistent(l_Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__4);
l_Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__5 = _init_l_Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__5();
lean_mark_persistent(l_Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__5);
l_Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__6 = _init_l_Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__6();
lean_mark_persistent(l_Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__6);
if (builtin) {res = l_Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
