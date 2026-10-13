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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_saveState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMCtxImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_mkOptionalNode(lean_object*);
lean_object* l_Lean_Elab_Tactic_expandOptLocation(lean_object*);
lean_object* l_Lean_Elab_Tactic_withLocation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_reportOutOfHeartbeats(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_findDecl_x3f___redArg(lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isImplementationDetail(lean_object*);
lean_object* l_Lean_FVarId_getType___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Rewrites_localHypotheses(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Rewrites_findRewrites(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_get_x3fInternal___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_Meta_mkEqMP(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_replace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_FVarId_getUserName___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_replaceTargetEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Rewrites_RewriteResult_addSuggestion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Rewrites_createModuleTreeRef(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__1___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Rewrites_evalExact_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Rewrites_evalExact_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Rewrites_evalExact_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Rewrites_evalExact_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Elab_Rewrites_evalExact_spec__4___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Elab_Rewrites_evalExact_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Elab_Rewrites_evalExact_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Elab_Rewrites_evalExact_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Elab_Rewrites_evalExact_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Elab_Rewrites_evalExact_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Rewrites_evalExact_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Rewrites_evalExact_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Rewrites_evalExact_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Rewrites_evalExact_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Rewrites_evalExact___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "Failed to find a rewrite for some location"};
static const lean_object* l_Lean_Elab_Rewrites_evalExact___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Rewrites_evalExact___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Rewrites_evalExact___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Rewrites_evalExact___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__5___redArg___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Rewrites_evalExact___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "rewrites"};
static const lean_object* l_Lean_Elab_Rewrites_evalExact___lam__2___closed__0 = (const lean_object*)&l_Lean_Elab_Rewrites_evalExact___lam__2___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Rewrites_evalExact___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Rewrites_evalExact___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 174, 121, 91, 16, 171, 72, 14)}};
static const lean_object* l_Lean_Elab_Rewrites_evalExact___lam__2___closed__1 = (const lean_object*)&l_Lean_Elab_Rewrites_evalExact___lam__2___closed__1_value;
static const lean_string_object l_Lean_Elab_Rewrites_evalExact___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 60, .m_capacity = 60, .m_length = 59, .m_data = "Could not find any lemmas which can rewrite the hypothesis "};
static const lean_object* l_Lean_Elab_Rewrites_evalExact___lam__2___closed__2 = (const lean_object*)&l_Lean_Elab_Rewrites_evalExact___lam__2___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Rewrites_evalExact___lam__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Rewrites_evalExact___lam__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_Rewrites_evalExact_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_Rewrites_evalExact_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Rewrites_evalExact___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "tacticTry_"};
static const lean_object* l_Lean_Elab_Rewrites_evalExact___lam__3___closed__0 = (const lean_object*)&l_Lean_Elab_Rewrites_evalExact___lam__3___closed__0_value;
static const lean_string_object l_Lean_Elab_Rewrites_evalExact___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "try"};
static const lean_object* l_Lean_Elab_Rewrites_evalExact___lam__3___closed__1 = (const lean_object*)&l_Lean_Elab_Rewrites_evalExact___lam__3___closed__1_value;
static const lean_string_object l_Lean_Elab_Rewrites_evalExact___lam__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Lean_Elab_Rewrites_evalExact___lam__3___closed__2 = (const lean_object*)&l_Lean_Elab_Rewrites_evalExact___lam__3___closed__2_value;
static const lean_string_object l_Lean_Elab_Rewrites_evalExact___lam__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Lean_Elab_Rewrites_evalExact___lam__3___closed__3 = (const lean_object*)&l_Lean_Elab_Rewrites_evalExact___lam__3___closed__3_value;
static const lean_string_object l_Lean_Elab_Rewrites_evalExact___lam__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Elab_Rewrites_evalExact___lam__3___closed__4 = (const lean_object*)&l_Lean_Elab_Rewrites_evalExact___lam__3___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Rewrites_evalExact___lam__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Rewrites_evalExact___lam__3___closed__4_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Elab_Rewrites_evalExact___lam__3___closed__5 = (const lean_object*)&l_Lean_Elab_Rewrites_evalExact___lam__3___closed__5_value;
static const lean_string_object l_Lean_Elab_Rewrites_evalExact___lam__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticRfl"};
static const lean_object* l_Lean_Elab_Rewrites_evalExact___lam__3___closed__6 = (const lean_object*)&l_Lean_Elab_Rewrites_evalExact___lam__3___closed__6_value;
static const lean_string_object l_Lean_Elab_Rewrites_evalExact___lam__3___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rfl"};
static const lean_object* l_Lean_Elab_Rewrites_evalExact___lam__3___closed__7 = (const lean_object*)&l_Lean_Elab_Rewrites_evalExact___lam__3___closed__7_value;
static const lean_string_object l_Lean_Elab_Rewrites_evalExact___lam__3___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 53, .m_capacity = 53, .m_length = 52, .m_data = "Could not find any lemmas which can rewrite the goal"};
static const lean_object* l_Lean_Elab_Rewrites_evalExact___lam__3___closed__8 = (const lean_object*)&l_Lean_Elab_Rewrites_evalExact___lam__3___closed__8_value;
static lean_once_cell_t l_Lean_Elab_Rewrites_evalExact___lam__3___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Rewrites_evalExact___lam__3___closed__9;
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact___lam__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact___lam__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__7(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Rewrites_evalExact_spec__10(uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Rewrites_evalExact_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Rewrites_evalExact_spec__8(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Rewrites_evalExact_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "group"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__9___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__9___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__9___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__9___closed__0_value),LEAN_SCALAR_PTR_LITERAL(206, 113, 20, 57, 188, 177, 187, 30)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__9___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__9___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__9(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__9___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Rewrites_evalExact___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Rewrites_evalExact___closed__0 = (const lean_object*)&l_Lean_Elab_Rewrites_evalExact___closed__0_value;
static const lean_string_object l_Lean_Elab_Rewrites_evalExact___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Rewrites_evalExact___closed__1 = (const lean_object*)&l_Lean_Elab_Rewrites_evalExact___closed__1_value;
static const lean_string_object l_Lean_Elab_Rewrites_evalExact___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Elab_Rewrites_evalExact___closed__2 = (const lean_object*)&l_Lean_Elab_Rewrites_evalExact___closed__2_value;
static const lean_string_object l_Lean_Elab_Rewrites_evalExact___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "rewrites\?"};
static const lean_object* l_Lean_Elab_Rewrites_evalExact___closed__3 = (const lean_object*)&l_Lean_Elab_Rewrites_evalExact___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Rewrites_evalExact___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Rewrites_evalExact___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Rewrites_evalExact___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Rewrites_evalExact___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Rewrites_evalExact___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Rewrites_evalExact___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Rewrites_evalExact___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Rewrites_evalExact___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Rewrites_evalExact___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Rewrites_evalExact___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Rewrites_evalExact___closed__3_value),LEAN_SCALAR_PTR_LITERAL(79, 182, 174, 62, 133, 253, 245, 70)}};
static const lean_object* l_Lean_Elab_Rewrites_evalExact___closed__4 = (const lean_object*)&l_Lean_Elab_Rewrites_evalExact___closed__4_value;
static const lean_closure_object l_Lean_Elab_Rewrites_evalExact___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Rewrites_evalExact___lam__0___boxed, .m_arity = 10, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Rewrites_evalExact___closed__5 = (const lean_object*)&l_Lean_Elab_Rewrites_evalExact___closed__5_value;
static const lean_string_object l_Lean_Elab_Rewrites_evalExact___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "findRewrites"};
static const lean_object* l_Lean_Elab_Rewrites_evalExact___closed__6 = (const lean_object*)&l_Lean_Elab_Rewrites_evalExact___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Rewrites_evalExact___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Rewrites_evalExact___closed__6_value),LEAN_SCALAR_PTR_LITERAL(252, 187, 157, 192, 16, 26, 228, 233)}};
static const lean_object* l_Lean_Elab_Rewrites_evalExact___closed__7 = (const lean_object*)&l_Lean_Elab_Rewrites_evalExact___closed__7_value;
static const lean_array_object l_Lean_Elab_Rewrites_evalExact___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Rewrites_evalExact___closed__8 = (const lean_object*)&l_Lean_Elab_Rewrites_evalExact___closed__8_value;
static const lean_string_object l_Lean_Elab_Rewrites_evalExact___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "rewrites_forbidden"};
static const lean_object* l_Lean_Elab_Rewrites_evalExact___closed__9 = (const lean_object*)&l_Lean_Elab_Rewrites_evalExact___closed__9_value;
static const lean_ctor_object l_Lean_Elab_Rewrites_evalExact___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Rewrites_evalExact___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Rewrites_evalExact___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Rewrites_evalExact___closed__10_value_aux_0),((lean_object*)&l_Lean_Elab_Rewrites_evalExact___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Rewrites_evalExact___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Rewrites_evalExact___closed__10_value_aux_1),((lean_object*)&l_Lean_Elab_Rewrites_evalExact___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Rewrites_evalExact___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Rewrites_evalExact___closed__10_value_aux_2),((lean_object*)&l_Lean_Elab_Rewrites_evalExact___closed__9_value),LEAN_SCALAR_PTR_LITERAL(183, 172, 63, 220, 170, 172, 94, 32)}};
static const lean_object* l_Lean_Elab_Rewrites_evalExact___closed__10 = (const lean_object*)&l_Lean_Elab_Rewrites_evalExact___closed__10_value;
static const lean_array_object l_Lean_Elab_Rewrites_evalExact___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Rewrites_evalExact___closed__11 = (const lean_object*)&l_Lean_Elab_Rewrites_evalExact___closed__11_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Rewrites"};
static const lean_object* l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "evalExact"};
static const lean_object* l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Rewrites_evalExact___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 208, 246, 230, 136, 19, 52, 73)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(252, 168, 146, 156, 30, 84, 49, 93)}};
static const lean_object* l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(29) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(67) << 1) | 1)),((lean_object*)(((size_t)(70) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__1_value),((lean_object*)(((size_t)(70) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(29) << 1) | 1)),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(29) << 1) | 1)),((lean_object*)(((size_t)(13) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__3_value),((lean_object*)(((size_t)(4) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__4_value),((lean_object*)(((size_t)(13) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___boxed(lean_object*);
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_1_ = lean_box(0);
v___x_2_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_3_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3_, 0, v___x_2_);
lean_ctor_set(v___x_3_, 1, v___x_1_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__1___redArg(){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__1___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__1___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__1___redArg___closed__0);
v___x_6_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__1___redArg___boxed(lean_object* v___y_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__1___redArg();
return v_res_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__1(lean_object* v_00_u03b1_9_, lean_object* v___y_10_, lean_object* v___y_11_, lean_object* v___y_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__1___redArg();
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__1___boxed(lean_object* v_00_u03b1_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__1(v_00_u03b1_20_, v___y_21_, v___y_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_, v___y_27_, v___y_28_);
lean_dec(v___y_28_);
lean_dec_ref(v___y_27_);
lean_dec(v___y_26_);
lean_dec_ref(v___y_25_);
lean_dec(v___y_24_);
lean_dec_ref(v___y_23_);
lean_dec(v___y_22_);
lean_dec_ref(v___y_21_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Rewrites_evalExact_spec__2___redArg(lean_object* v_e_31_, lean_object* v___y_32_){
_start:
{
uint8_t v___x_34_; 
v___x_34_ = l_Lean_Expr_hasMVar(v_e_31_);
if (v___x_34_ == 0)
{
lean_object* v___x_35_; 
v___x_35_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_35_, 0, v_e_31_);
return v___x_35_;
}
else
{
lean_object* v___x_36_; lean_object* v_mctx_37_; lean_object* v___x_38_; lean_object* v_fst_39_; lean_object* v_snd_40_; lean_object* v___x_41_; lean_object* v_cache_42_; lean_object* v_zetaDeltaFVarIds_43_; lean_object* v_postponed_44_; lean_object* v_diag_45_; lean_object* v___x_47_; uint8_t v_isShared_48_; uint8_t v_isSharedCheck_54_; 
v___x_36_ = lean_st_ref_get(v___y_32_);
v_mctx_37_ = lean_ctor_get(v___x_36_, 0);
lean_inc_ref(v_mctx_37_);
lean_dec(v___x_36_);
v___x_38_ = l_Lean_instantiateMVarsCore(v_mctx_37_, v_e_31_);
v_fst_39_ = lean_ctor_get(v___x_38_, 0);
lean_inc(v_fst_39_);
v_snd_40_ = lean_ctor_get(v___x_38_, 1);
lean_inc(v_snd_40_);
lean_dec_ref(v___x_38_);
v___x_41_ = lean_st_ref_take(v___y_32_);
v_cache_42_ = lean_ctor_get(v___x_41_, 1);
v_zetaDeltaFVarIds_43_ = lean_ctor_get(v___x_41_, 2);
v_postponed_44_ = lean_ctor_get(v___x_41_, 3);
v_diag_45_ = lean_ctor_get(v___x_41_, 4);
v_isSharedCheck_54_ = !lean_is_exclusive(v___x_41_);
if (v_isSharedCheck_54_ == 0)
{
lean_object* v_unused_55_; 
v_unused_55_ = lean_ctor_get(v___x_41_, 0);
lean_dec(v_unused_55_);
v___x_47_ = v___x_41_;
v_isShared_48_ = v_isSharedCheck_54_;
goto v_resetjp_46_;
}
else
{
lean_inc(v_diag_45_);
lean_inc(v_postponed_44_);
lean_inc(v_zetaDeltaFVarIds_43_);
lean_inc(v_cache_42_);
lean_dec(v___x_41_);
v___x_47_ = lean_box(0);
v_isShared_48_ = v_isSharedCheck_54_;
goto v_resetjp_46_;
}
v_resetjp_46_:
{
lean_object* v___x_50_; 
if (v_isShared_48_ == 0)
{
lean_ctor_set(v___x_47_, 0, v_snd_40_);
v___x_50_ = v___x_47_;
goto v_reusejp_49_;
}
else
{
lean_object* v_reuseFailAlloc_53_; 
v_reuseFailAlloc_53_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_53_, 0, v_snd_40_);
lean_ctor_set(v_reuseFailAlloc_53_, 1, v_cache_42_);
lean_ctor_set(v_reuseFailAlloc_53_, 2, v_zetaDeltaFVarIds_43_);
lean_ctor_set(v_reuseFailAlloc_53_, 3, v_postponed_44_);
lean_ctor_set(v_reuseFailAlloc_53_, 4, v_diag_45_);
v___x_50_ = v_reuseFailAlloc_53_;
goto v_reusejp_49_;
}
v_reusejp_49_:
{
lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_51_ = lean_st_ref_put(v___y_32_, v___x_50_);
v___x_52_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_52_, 0, v_fst_39_);
return v___x_52_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Rewrites_evalExact_spec__2___redArg___boxed(lean_object* v_e_56_, lean_object* v___y_57_, lean_object* v___y_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l_Lean_instantiateMVars___at___00Lean_Elab_Rewrites_evalExact_spec__2___redArg(v_e_56_, v___y_57_);
lean_dec(v___y_57_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Rewrites_evalExact_spec__2(lean_object* v_e_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_){
_start:
{
lean_object* v___x_70_; 
v___x_70_ = l_Lean_instantiateMVars___at___00Lean_Elab_Rewrites_evalExact_spec__2___redArg(v_e_60_, v___y_66_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Rewrites_evalExact_spec__2___boxed(lean_object* v_e_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l_Lean_instantiateMVars___at___00Lean_Elab_Rewrites_evalExact_spec__2(v_e_71_, v___y_72_, v___y_73_, v___y_74_, v___y_75_, v___y_76_, v___y_77_, v___y_78_, v___y_79_);
lean_dec(v___y_79_);
lean_dec_ref(v___y_78_);
lean_dec(v___y_77_);
lean_dec_ref(v___y_76_);
lean_dec(v___y_75_);
lean_dec_ref(v___y_74_);
lean_dec(v___y_73_);
lean_dec_ref(v___y_72_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Elab_Rewrites_evalExact_spec__4___redArg___lam__0(lean_object* v_x_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_){
_start:
{
lean_object* v___x_92_; 
lean_inc(v___y_86_);
lean_inc_ref(v___y_85_);
lean_inc(v___y_84_);
lean_inc_ref(v___y_83_);
v___x_92_ = lean_apply_9(v_x_82_, v___y_83_, v___y_84_, v___y_85_, v___y_86_, v___y_87_, v___y_88_, v___y_89_, v___y_90_, lean_box(0));
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Elab_Rewrites_evalExact_spec__4___redArg___lam__0___boxed(lean_object* v_x_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_){
_start:
{
lean_object* v_res_103_; 
v_res_103_ = l_Lean_Meta_withMCtx___at___00Lean_Elab_Rewrites_evalExact_spec__4___redArg___lam__0(v_x_93_, v___y_94_, v___y_95_, v___y_96_, v___y_97_, v___y_98_, v___y_99_, v___y_100_, v___y_101_);
lean_dec(v___y_97_);
lean_dec_ref(v___y_96_);
lean_dec(v___y_95_);
lean_dec_ref(v___y_94_);
return v_res_103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Elab_Rewrites_evalExact_spec__4___redArg(lean_object* v_mctx_104_, lean_object* v_x_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_){
_start:
{
lean_object* v___f_115_; lean_object* v___x_116_; 
lean_inc(v___y_109_);
lean_inc_ref(v___y_108_);
lean_inc(v___y_107_);
lean_inc_ref(v___y_106_);
v___f_115_ = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at___00Lean_Elab_Rewrites_evalExact_spec__4___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_115_, 0, v_x_105_);
lean_closure_set(v___f_115_, 1, v___y_106_);
lean_closure_set(v___f_115_, 2, v___y_107_);
lean_closure_set(v___f_115_, 3, v___y_108_);
lean_closure_set(v___f_115_, 4, v___y_109_);
v___x_116_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMCtxImp(lean_box(0), v_mctx_104_, v___f_115_, v___y_110_, v___y_111_, v___y_112_, v___y_113_);
if (lean_obj_tag(v___x_116_) == 0)
{
return v___x_116_;
}
else
{
lean_object* v_a_117_; lean_object* v___x_119_; uint8_t v_isShared_120_; uint8_t v_isSharedCheck_124_; 
v_a_117_ = lean_ctor_get(v___x_116_, 0);
v_isSharedCheck_124_ = !lean_is_exclusive(v___x_116_);
if (v_isSharedCheck_124_ == 0)
{
v___x_119_ = v___x_116_;
v_isShared_120_ = v_isSharedCheck_124_;
goto v_resetjp_118_;
}
else
{
lean_inc(v_a_117_);
lean_dec(v___x_116_);
v___x_119_ = lean_box(0);
v_isShared_120_ = v_isSharedCheck_124_;
goto v_resetjp_118_;
}
v_resetjp_118_:
{
lean_object* v___x_122_; 
if (v_isShared_120_ == 0)
{
v___x_122_ = v___x_119_;
goto v_reusejp_121_;
}
else
{
lean_object* v_reuseFailAlloc_123_; 
v_reuseFailAlloc_123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_123_, 0, v_a_117_);
v___x_122_ = v_reuseFailAlloc_123_;
goto v_reusejp_121_;
}
v_reusejp_121_:
{
return v___x_122_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Elab_Rewrites_evalExact_spec__4___redArg___boxed(lean_object* v_mctx_125_, lean_object* v_x_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_){
_start:
{
lean_object* v_res_136_; 
v_res_136_ = l_Lean_Meta_withMCtx___at___00Lean_Elab_Rewrites_evalExact_spec__4___redArg(v_mctx_125_, v_x_126_, v___y_127_, v___y_128_, v___y_129_, v___y_130_, v___y_131_, v___y_132_, v___y_133_, v___y_134_);
lean_dec(v___y_134_);
lean_dec_ref(v___y_133_);
lean_dec(v___y_132_);
lean_dec_ref(v___y_131_);
lean_dec(v___y_130_);
lean_dec_ref(v___y_129_);
lean_dec(v___y_128_);
lean_dec_ref(v___y_127_);
return v_res_136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Elab_Rewrites_evalExact_spec__4(lean_object* v_00_u03b1_137_, lean_object* v_mctx_138_, lean_object* v_x_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_){
_start:
{
lean_object* v___x_149_; 
v___x_149_ = l_Lean_Meta_withMCtx___at___00Lean_Elab_Rewrites_evalExact_spec__4___redArg(v_mctx_138_, v_x_139_, v___y_140_, v___y_141_, v___y_142_, v___y_143_, v___y_144_, v___y_145_, v___y_146_, v___y_147_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Elab_Rewrites_evalExact_spec__4___boxed(lean_object* v_00_u03b1_150_, lean_object* v_mctx_151_, lean_object* v_x_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l_Lean_Meta_withMCtx___at___00Lean_Elab_Rewrites_evalExact_spec__4(v_00_u03b1_150_, v_mctx_151_, v_x_152_, v___y_153_, v___y_154_, v___y_155_, v___y_156_, v___y_157_, v___y_158_, v___y_159_, v___y_160_);
lean_dec(v___y_160_);
lean_dec_ref(v___y_159_);
lean_dec(v___y_158_);
lean_dec_ref(v___y_157_);
lean_dec(v___y_156_);
lean_dec_ref(v___y_155_);
lean_dec(v___y_154_);
lean_dec_ref(v___y_153_);
return v_res_162_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Rewrites_evalExact_spec__6___redArg(lean_object* v_mvarId_163_, lean_object* v_x_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_){
_start:
{
lean_object* v___x_170_; 
v___x_170_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_163_, v_x_164_, v___y_165_, v___y_166_, v___y_167_, v___y_168_);
if (lean_obj_tag(v___x_170_) == 0)
{
lean_object* v_a_171_; lean_object* v___x_173_; uint8_t v_isShared_174_; uint8_t v_isSharedCheck_178_; 
v_a_171_ = lean_ctor_get(v___x_170_, 0);
v_isSharedCheck_178_ = !lean_is_exclusive(v___x_170_);
if (v_isSharedCheck_178_ == 0)
{
v___x_173_ = v___x_170_;
v_isShared_174_ = v_isSharedCheck_178_;
goto v_resetjp_172_;
}
else
{
lean_inc(v_a_171_);
lean_dec(v___x_170_);
v___x_173_ = lean_box(0);
v_isShared_174_ = v_isSharedCheck_178_;
goto v_resetjp_172_;
}
v_resetjp_172_:
{
lean_object* v___x_176_; 
if (v_isShared_174_ == 0)
{
v___x_176_ = v___x_173_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v_a_171_);
v___x_176_ = v_reuseFailAlloc_177_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
return v___x_176_;
}
}
}
else
{
lean_object* v_a_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_186_; 
v_a_179_ = lean_ctor_get(v___x_170_, 0);
v_isSharedCheck_186_ = !lean_is_exclusive(v___x_170_);
if (v_isSharedCheck_186_ == 0)
{
v___x_181_ = v___x_170_;
v_isShared_182_ = v_isSharedCheck_186_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_a_179_);
lean_dec(v___x_170_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_186_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v___x_184_; 
if (v_isShared_182_ == 0)
{
v___x_184_ = v___x_181_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v_a_179_);
v___x_184_ = v_reuseFailAlloc_185_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
return v___x_184_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Rewrites_evalExact_spec__6___redArg___boxed(lean_object* v_mvarId_187_, lean_object* v_x_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Rewrites_evalExact_spec__6___redArg(v_mvarId_187_, v_x_188_, v___y_189_, v___y_190_, v___y_191_, v___y_192_);
lean_dec(v___y_192_);
lean_dec_ref(v___y_191_);
lean_dec(v___y_190_);
lean_dec_ref(v___y_189_);
return v_res_194_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Rewrites_evalExact_spec__6(lean_object* v_00_u03b1_195_, lean_object* v_mvarId_196_, lean_object* v_x_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_){
_start:
{
lean_object* v___x_203_; 
v___x_203_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Rewrites_evalExact_spec__6___redArg(v_mvarId_196_, v_x_197_, v___y_198_, v___y_199_, v___y_200_, v___y_201_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Rewrites_evalExact_spec__6___boxed(lean_object* v_00_u03b1_204_, lean_object* v_mvarId_205_, lean_object* v_x_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_){
_start:
{
lean_object* v_res_212_; 
v_res_212_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Rewrites_evalExact_spec__6(v_00_u03b1_204_, v_mvarId_205_, v_x_206_, v___y_207_, v___y_208_, v___y_209_, v___y_210_);
lean_dec(v___y_210_);
lean_dec_ref(v___y_209_);
lean_dec(v___y_208_);
lean_dec_ref(v___y_207_);
return v_res_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__0_spec__0(lean_object* v_msgData_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_){
_start:
{
lean_object* v___x_219_; lean_object* v_env_220_; uint8_t v___x_221_; lean_object* v_env_222_; lean_object* v___x_223_; lean_object* v_toCold_224_; lean_object* v_mctx_225_; lean_object* v_lctx_226_; lean_object* v_options_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; 
v___x_219_ = lean_st_ref_get(v___y_217_);
v_env_220_ = lean_ctor_get(v___x_219_, 0);
lean_inc_ref(v_env_220_);
lean_dec(v___x_219_);
v___x_221_ = 0;
v_env_222_ = l_Lean_Environment_setRecordingDeps(v_env_220_, v___x_221_);
v___x_223_ = lean_st_ref_get(v___y_215_);
v_toCold_224_ = lean_ctor_get(v___y_216_, 0);
v_mctx_225_ = lean_ctor_get(v___x_223_, 0);
lean_inc_ref(v_mctx_225_);
lean_dec(v___x_223_);
v_lctx_226_ = lean_ctor_get(v___y_214_, 2);
v_options_227_ = lean_ctor_get(v_toCold_224_, 2);
lean_inc_ref(v_options_227_);
lean_inc_ref(v_lctx_226_);
v___x_228_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_228_, 0, v_env_222_);
lean_ctor_set(v___x_228_, 1, v_mctx_225_);
lean_ctor_set(v___x_228_, 2, v_lctx_226_);
lean_ctor_set(v___x_228_, 3, v_options_227_);
v___x_229_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_229_, 0, v___x_228_);
lean_ctor_set(v___x_229_, 1, v_msgData_213_);
v___x_230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_230_, 0, v___x_229_);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__0_spec__0___boxed(lean_object* v_msgData_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__0_spec__0(v_msgData_231_, v___y_232_, v___y_233_, v___y_234_, v___y_235_);
lean_dec(v___y_235_);
lean_dec_ref(v___y_234_);
lean_dec(v___y_233_);
lean_dec_ref(v___y_232_);
return v_res_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__0___redArg(lean_object* v_msg_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_){
_start:
{
lean_object* v_ref_244_; lean_object* v___x_245_; lean_object* v_a_246_; lean_object* v___x_248_; uint8_t v_isShared_249_; uint8_t v_isSharedCheck_254_; 
v_ref_244_ = lean_ctor_get(v___y_241_, 2);
v___x_245_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__0_spec__0(v_msg_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_);
v_a_246_ = lean_ctor_get(v___x_245_, 0);
v_isSharedCheck_254_ = !lean_is_exclusive(v___x_245_);
if (v_isSharedCheck_254_ == 0)
{
v___x_248_ = v___x_245_;
v_isShared_249_ = v_isSharedCheck_254_;
goto v_resetjp_247_;
}
else
{
lean_inc(v_a_246_);
lean_dec(v___x_245_);
v___x_248_ = lean_box(0);
v_isShared_249_ = v_isSharedCheck_254_;
goto v_resetjp_247_;
}
v_resetjp_247_:
{
lean_object* v___x_250_; lean_object* v___x_252_; 
lean_inc(v_ref_244_);
v___x_250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_250_, 0, v_ref_244_);
lean_ctor_set(v___x_250_, 1, v_a_246_);
if (v_isShared_249_ == 0)
{
lean_ctor_set_tag(v___x_248_, 1);
lean_ctor_set(v___x_248_, 0, v___x_250_);
v___x_252_ = v___x_248_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v___x_250_);
v___x_252_ = v_reuseFailAlloc_253_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
return v___x_252_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__0___redArg___boxed(lean_object* v_msg_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l_Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__0___redArg(v_msg_255_, v___y_256_, v___y_257_, v___y_258_, v___y_259_);
lean_dec(v___y_259_);
lean_dec_ref(v___y_258_);
lean_dec(v___y_257_);
lean_dec_ref(v___y_256_);
return v_res_261_;
}
}
static lean_object* _init_l_Lean_Elab_Rewrites_evalExact___lam__0___closed__1(void){
_start:
{
lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_263_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___lam__0___closed__0));
v___x_264_ = l_Lean_stringToMessageData(v___x_263_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact___lam__0(lean_object* v_x_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_){
_start:
{
lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_275_ = lean_obj_once(&l_Lean_Elab_Rewrites_evalExact___lam__0___closed__1, &l_Lean_Elab_Rewrites_evalExact___lam__0___closed__1_once, _init_l_Lean_Elab_Rewrites_evalExact___lam__0___closed__1);
v___x_276_ = l_Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__0___redArg(v___x_275_, v___y_270_, v___y_271_, v___y_272_, v___y_273_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact___lam__0___boxed(lean_object* v_x_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l_Lean_Elab_Rewrites_evalExact___lam__0(v_x_277_, v___y_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_);
lean_dec(v___y_285_);
lean_dec_ref(v___y_284_);
lean_dec(v___y_283_);
lean_dec_ref(v___y_282_);
lean_dec(v___y_281_);
lean_dec_ref(v___y_280_);
lean_dec(v___y_279_);
lean_dec_ref(v___y_278_);
lean_dec(v_x_277_);
return v_res_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact___lam__1(lean_object* v_eqProof_288_, lean_object* v___x_289_, lean_object* v_eNew_290_, lean_object* v_a_291_, lean_object* v_f_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_){
_start:
{
lean_object* v___x_298_; 
v___x_298_ = l_Lean_Meta_mkEqMP(v_eqProof_288_, v___x_289_, v___y_293_, v___y_294_, v___y_295_, v___y_296_);
if (lean_obj_tag(v___x_298_) == 0)
{
lean_object* v_a_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v_a_299_ = lean_ctor_get(v___x_298_, 0);
lean_inc(v_a_299_);
lean_dec_ref_known(v___x_298_, 1);
v___x_300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_300_, 0, v_eNew_290_);
v___x_301_ = lean_box(0);
v___x_302_ = l_Lean_MVarId_replace(v_a_291_, v_f_292_, v_a_299_, v___x_300_, v___x_301_, v___y_293_, v___y_294_, v___y_295_, v___y_296_);
return v___x_302_;
}
else
{
lean_object* v_a_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_310_; 
lean_dec(v_f_292_);
lean_dec(v_a_291_);
lean_dec_ref(v_eNew_290_);
v_a_303_ = lean_ctor_get(v___x_298_, 0);
v_isSharedCheck_310_ = !lean_is_exclusive(v___x_298_);
if (v_isSharedCheck_310_ == 0)
{
v___x_305_ = v___x_298_;
v_isShared_306_ = v_isSharedCheck_310_;
goto v_resetjp_304_;
}
else
{
lean_inc(v_a_303_);
lean_dec(v___x_298_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_310_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
lean_object* v___x_308_; 
if (v_isShared_306_ == 0)
{
v___x_308_ = v___x_305_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v_a_303_);
v___x_308_ = v_reuseFailAlloc_309_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
return v___x_308_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact___lam__1___boxed(lean_object* v_eqProof_311_, lean_object* v___x_312_, lean_object* v_eNew_313_, lean_object* v_a_314_, lean_object* v_f_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_){
_start:
{
lean_object* v_res_321_; 
v_res_321_ = l_Lean_Elab_Rewrites_evalExact___lam__1(v_eqProof_311_, v___x_312_, v_eNew_313_, v_a_314_, v_f_315_, v___y_316_, v___y_317_, v___y_318_, v___y_319_);
lean_dec(v___y_319_);
lean_dec_ref(v___y_318_);
lean_dec(v___y_317_);
lean_dec_ref(v___y_316_);
return v_res_321_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__5___redArg___lam__0(lean_object* v_result_322_, lean_object* v_expr_323_, uint8_t v_symm_324_, lean_object* v_f_325_, lean_object* v_tk_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_){
_start:
{
lean_object* v_ref_336_; lean_object* v___x_337_; 
v_ref_336_ = lean_ctor_get(v___y_333_, 2);
v___x_337_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_328_, v___y_330_, v___y_332_, v___y_334_);
if (lean_obj_tag(v___x_337_) == 0)
{
lean_object* v_a_338_; lean_object* v_eNew_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v_a_338_ = lean_ctor_get(v___x_337_, 0);
lean_inc(v_a_338_);
lean_dec_ref_known(v___x_337_, 1);
v_eNew_339_ = lean_ctor_get(v_result_322_, 0);
v___x_340_ = lean_box(v_symm_324_);
v___x_341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_341_, 0, v_expr_323_);
lean_ctor_set(v___x_341_, 1, v___x_340_);
v___x_342_ = lean_box(0);
v___x_343_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_343_, 0, v___x_341_);
lean_ctor_set(v___x_343_, 1, v___x_342_);
lean_inc_ref(v_eNew_339_);
v___x_344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_344_, 0, v_eNew_339_);
v___x_345_ = l_Lean_Expr_fvar___override(v_f_325_);
v___x_346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_346_, 0, v___x_345_);
lean_inc(v_ref_336_);
v___x_347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_347_, 0, v_ref_336_);
v___x_348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_348_, 0, v_a_338_);
v___x_349_ = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion(v_tk_326_, v___x_343_, v___x_344_, v___x_346_, v___x_347_, v___x_348_, v___y_327_, v___y_328_, v___y_329_, v___y_330_, v___y_331_, v___y_332_, v___y_333_, v___y_334_);
return v___x_349_;
}
else
{
lean_object* v_a_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_357_; 
lean_dec(v_tk_326_);
lean_dec(v_f_325_);
lean_dec_ref(v_expr_323_);
v_a_350_ = lean_ctor_get(v___x_337_, 0);
v_isSharedCheck_357_ = !lean_is_exclusive(v___x_337_);
if (v_isSharedCheck_357_ == 0)
{
v___x_352_ = v___x_337_;
v_isShared_353_ = v_isSharedCheck_357_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_a_350_);
lean_dec(v___x_337_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_357_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v___x_355_; 
if (v_isShared_353_ == 0)
{
v___x_355_ = v___x_352_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v_a_350_);
v___x_355_ = v_reuseFailAlloc_356_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
return v___x_355_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__5___redArg___lam__0___boxed(lean_object* v_result_358_, lean_object* v_expr_359_, lean_object* v_symm_360_, lean_object* v_f_361_, lean_object* v_tk_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_){
_start:
{
uint8_t v_symm_boxed_372_; lean_object* v_res_373_; 
v_symm_boxed_372_ = lean_unbox(v_symm_360_);
v_res_373_ = l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__5___redArg___lam__0(v_result_358_, v_expr_359_, v_symm_boxed_372_, v_f_361_, v_tk_362_, v___y_363_, v___y_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_, v___y_370_);
lean_dec(v___y_370_);
lean_dec_ref(v___y_369_);
lean_dec(v___y_368_);
lean_dec_ref(v___y_367_);
lean_dec(v___y_366_);
lean_dec_ref(v___y_365_);
lean_dec(v___y_364_);
lean_dec_ref(v___y_363_);
lean_dec_ref(v_result_358_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__5___redArg(lean_object* v_f_374_, lean_object* v_tk_375_, lean_object* v_as_x27_376_, lean_object* v_b_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_){
_start:
{
if (lean_obj_tag(v_as_x27_376_) == 0)
{
lean_object* v___x_387_; 
lean_dec(v_tk_375_);
lean_dec(v_f_374_);
v___x_387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_387_, 0, v_b_377_);
return v___x_387_;
}
else
{
lean_object* v_head_388_; lean_object* v_tail_389_; lean_object* v_expr_390_; uint8_t v_symm_391_; lean_object* v_result_392_; lean_object* v_mctx_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___f_396_; lean_object* v___x_397_; 
v_head_388_ = lean_ctor_get(v_as_x27_376_, 0);
v_tail_389_ = lean_ctor_get(v_as_x27_376_, 1);
v_expr_390_ = lean_ctor_get(v_head_388_, 0);
v_symm_391_ = lean_ctor_get_uint8(v_head_388_, sizeof(void*)*4);
v_result_392_ = lean_ctor_get(v_head_388_, 2);
v_mctx_393_ = lean_ctor_get(v_head_388_, 3);
v___x_394_ = lean_box(0);
v___x_395_ = lean_box(v_symm_391_);
lean_inc(v_tk_375_);
lean_inc(v_f_374_);
lean_inc_ref(v_expr_390_);
lean_inc_ref(v_result_392_);
v___f_396_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__5___redArg___lam__0___boxed), 14, 5);
lean_closure_set(v___f_396_, 0, v_result_392_);
lean_closure_set(v___f_396_, 1, v_expr_390_);
lean_closure_set(v___f_396_, 2, v___x_395_);
lean_closure_set(v___f_396_, 3, v_f_374_);
lean_closure_set(v___f_396_, 4, v_tk_375_);
lean_inc_ref(v_mctx_393_);
v___x_397_ = l_Lean_Meta_withMCtx___at___00Lean_Elab_Rewrites_evalExact_spec__4___redArg(v_mctx_393_, v___f_396_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_);
if (lean_obj_tag(v___x_397_) == 0)
{
lean_dec_ref_known(v___x_397_, 1);
v_as_x27_376_ = v_tail_389_;
v_b_377_ = v___x_394_;
goto _start;
}
else
{
lean_dec(v_tk_375_);
lean_dec(v_f_374_);
return v___x_397_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__5___redArg___boxed(lean_object* v_f_399_, lean_object* v_tk_400_, lean_object* v_as_x27_401_, lean_object* v_b_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__5___redArg(v_f_399_, v_tk_400_, v_as_x27_401_, v_b_402_, v___y_403_, v___y_404_, v___y_405_, v___y_406_, v___y_407_, v___y_408_, v___y_409_, v___y_410_);
lean_dec(v___y_410_);
lean_dec_ref(v___y_409_);
lean_dec(v___y_408_);
lean_dec_ref(v___y_407_);
lean_dec(v___y_406_);
lean_dec_ref(v___y_405_);
lean_dec(v___y_404_);
lean_dec_ref(v___y_403_);
lean_dec(v_as_x27_401_);
return v_res_412_;
}
}
static lean_object* _init_l_Lean_Elab_Rewrites_evalExact___lam__2___closed__3(void){
_start:
{
lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_417_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___lam__2___closed__2));
v___x_418_ = l_Lean_stringToMessageData(v___x_417_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact___lam__2(lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v___y_421_, lean_object* v_tk_422_, lean_object* v___x_423_, lean_object* v___x_424_, lean_object* v_f_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_){
_start:
{
lean_object* v___x_435_; 
lean_inc(v_f_425_);
v___x_435_ = l_Lean_FVarId_findDecl_x3f___redArg(v_f_425_, v___y_430_);
if (lean_obj_tag(v___x_435_) == 0)
{
lean_object* v_a_436_; lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_559_; 
v_a_436_ = lean_ctor_get(v___x_435_, 0);
v_isSharedCheck_559_ = !lean_is_exclusive(v___x_435_);
if (v_isSharedCheck_559_ == 0)
{
v___x_438_ = v___x_435_;
v_isShared_439_ = v_isSharedCheck_559_;
goto v_resetjp_437_;
}
else
{
lean_inc(v_a_436_);
lean_dec(v___x_435_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_559_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
if (lean_obj_tag(v_a_436_) == 1)
{
lean_object* v_val_440_; uint8_t v___x_441_; 
v_val_440_ = lean_ctor_get(v_a_436_, 0);
lean_inc(v_val_440_);
lean_dec_ref_known(v_a_436_, 1);
v___x_441_ = l_Lean_LocalDecl_isImplementationDetail(v_val_440_);
lean_dec(v_val_440_);
if (v___x_441_ == 0)
{
lean_object* v___x_442_; 
lean_del_object(v___x_438_);
lean_inc(v_f_425_);
v___x_442_ = l_Lean_FVarId_getType___redArg(v_f_425_, v___y_430_, v___y_432_, v___y_433_);
if (lean_obj_tag(v___x_442_) == 0)
{
lean_object* v_a_443_; lean_object* v___x_444_; lean_object* v_a_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; 
v_a_443_ = lean_ctor_get(v___x_442_, 0);
lean_inc(v_a_443_);
lean_dec_ref_known(v___x_442_, 1);
v___x_444_ = l_Lean_instantiateMVars___at___00Lean_Elab_Rewrites_evalExact_spec__2___redArg(v_a_443_, v___y_431_);
v_a_445_ = lean_ctor_get(v___x_444_, 0);
lean_inc(v_a_445_);
lean_dec_ref(v___x_444_);
v___x_446_ = lean_box(0);
lean_inc(v_f_425_);
v___x_447_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_447_, 0, v_f_425_);
lean_ctor_set(v___x_447_, 1, v___x_446_);
v___x_448_ = l_Lean_Meta_Rewrites_localHypotheses(v___x_447_, v___y_430_, v___y_431_, v___y_432_, v___y_433_);
lean_dec_ref_known(v___x_447_, 2);
if (lean_obj_tag(v___x_448_) == 0)
{
lean_object* v_a_449_; uint8_t v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; 
v_a_449_ = lean_ctor_get(v___x_448_, 0);
lean_inc(v_a_449_);
lean_dec_ref_known(v___x_448_, 1);
v___x_450_ = 2;
v___x_451_ = lean_unsigned_to_nat(20u);
v___x_452_ = lean_unsigned_to_nat(10u);
lean_inc(v_a_420_);
v___x_453_ = l_Lean_Meta_Rewrites_findRewrites(v_a_449_, v_a_419_, v_a_420_, v_a_445_, v___y_421_, v___x_450_, v___x_441_, v___x_451_, v___x_452_, v___y_430_, v___y_431_, v___y_432_, v___y_433_);
if (lean_obj_tag(v___x_453_) == 0)
{
lean_object* v_a_454_; lean_object* v___y_456_; lean_object* v___y_457_; lean_object* v___y_458_; lean_object* v___y_459_; lean_object* v___y_460_; lean_object* v___y_461_; lean_object* v___y_462_; lean_object* v___y_463_; lean_object* v___x_510_; lean_object* v___x_511_; 
v_a_454_ = lean_ctor_get(v___x_453_, 0);
lean_inc(v_a_454_);
lean_dec_ref_known(v___x_453_, 1);
v___x_510_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___lam__2___closed__1));
v___x_511_ = l_Lean_reportOutOfHeartbeats(v___x_510_, v_tk_422_, v___x_424_, v___y_432_, v___y_433_);
if (lean_obj_tag(v___x_511_) == 0)
{
uint8_t v___x_512_; 
lean_dec_ref_known(v___x_511_, 1);
v___x_512_ = l_List_isEmpty___redArg(v_a_454_);
if (v___x_512_ == 0)
{
v___y_456_ = v___y_426_;
v___y_457_ = v___y_427_;
v___y_458_ = v___y_428_;
v___y_459_ = v___y_429_;
v___y_460_ = v___y_430_;
v___y_461_ = v___y_431_;
v___y_462_ = v___y_432_;
v___y_463_ = v___y_433_;
goto v___jp_455_;
}
else
{
lean_object* v___x_513_; 
lean_dec(v_a_454_);
lean_dec(v___x_423_);
lean_dec(v_tk_422_);
lean_dec(v_a_420_);
v___x_513_ = l_Lean_FVarId_getUserName___redArg(v_f_425_, v___y_430_, v___y_432_, v___y_433_);
if (lean_obj_tag(v___x_513_) == 0)
{
lean_object* v_a_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; 
v_a_514_ = lean_ctor_get(v___x_513_, 0);
lean_inc(v_a_514_);
lean_dec_ref_known(v___x_513_, 1);
v___x_515_ = lean_obj_once(&l_Lean_Elab_Rewrites_evalExact___lam__2___closed__3, &l_Lean_Elab_Rewrites_evalExact___lam__2___closed__3_once, _init_l_Lean_Elab_Rewrites_evalExact___lam__2___closed__3);
v___x_516_ = l_Lean_MessageData_ofName(v_a_514_);
v___x_517_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_517_, 0, v___x_515_);
lean_ctor_set(v___x_517_, 1, v___x_516_);
v___x_518_ = l_Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__0___redArg(v___x_517_, v___y_430_, v___y_431_, v___y_432_, v___y_433_);
return v___x_518_;
}
else
{
lean_object* v_a_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_526_; 
v_a_519_ = lean_ctor_get(v___x_513_, 0);
v_isSharedCheck_526_ = !lean_is_exclusive(v___x_513_);
if (v_isSharedCheck_526_ == 0)
{
v___x_521_ = v___x_513_;
v_isShared_522_ = v_isSharedCheck_526_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_a_519_);
lean_dec(v___x_513_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_526_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v___x_524_; 
if (v_isShared_522_ == 0)
{
v___x_524_ = v___x_521_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v_a_519_);
v___x_524_ = v_reuseFailAlloc_525_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
return v___x_524_;
}
}
}
}
}
else
{
lean_dec(v_a_454_);
lean_dec(v_f_425_);
lean_dec(v___x_423_);
lean_dec(v_tk_422_);
lean_dec(v_a_420_);
return v___x_511_;
}
v___jp_455_:
{
lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_464_ = lean_box(0);
lean_inc(v_f_425_);
v___x_465_ = l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__5___redArg(v_f_425_, v_tk_422_, v_a_454_, v___x_464_, v___y_456_, v___y_457_, v___y_458_, v___y_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_);
if (lean_obj_tag(v___x_465_) == 0)
{
lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_508_; 
v_isSharedCheck_508_ = !lean_is_exclusive(v___x_465_);
if (v_isSharedCheck_508_ == 0)
{
lean_object* v_unused_509_; 
v_unused_509_ = lean_ctor_get(v___x_465_, 0);
lean_dec(v_unused_509_);
v___x_467_ = v___x_465_;
v_isShared_468_ = v_isSharedCheck_508_;
goto v_resetjp_466_;
}
else
{
lean_dec(v___x_465_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_508_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
lean_object* v___x_469_; 
v___x_469_ = l_List_get_x3fInternal___redArg(v_a_454_, v___x_423_);
lean_dec(v_a_454_);
if (lean_obj_tag(v___x_469_) == 1)
{
lean_object* v_val_470_; lean_object* v_result_471_; lean_object* v_mctx_472_; lean_object* v___x_473_; lean_object* v_cache_474_; lean_object* v_zetaDeltaFVarIds_475_; lean_object* v_postponed_476_; lean_object* v_diag_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_503_; 
lean_del_object(v___x_467_);
v_val_470_ = lean_ctor_get(v___x_469_, 0);
lean_inc(v_val_470_);
lean_dec_ref_known(v___x_469_, 1);
v_result_471_ = lean_ctor_get(v_val_470_, 2);
lean_inc_ref(v_result_471_);
v_mctx_472_ = lean_ctor_get(v_val_470_, 3);
lean_inc_ref(v_mctx_472_);
lean_dec(v_val_470_);
v___x_473_ = lean_st_ref_take(v___y_461_);
v_cache_474_ = lean_ctor_get(v___x_473_, 1);
v_zetaDeltaFVarIds_475_ = lean_ctor_get(v___x_473_, 2);
v_postponed_476_ = lean_ctor_get(v___x_473_, 3);
v_diag_477_ = lean_ctor_get(v___x_473_, 4);
v_isSharedCheck_503_ = !lean_is_exclusive(v___x_473_);
if (v_isSharedCheck_503_ == 0)
{
lean_object* v_unused_504_; 
v_unused_504_ = lean_ctor_get(v___x_473_, 0);
lean_dec(v_unused_504_);
v___x_479_ = v___x_473_;
v_isShared_480_ = v_isSharedCheck_503_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_diag_477_);
lean_inc(v_postponed_476_);
lean_inc(v_zetaDeltaFVarIds_475_);
lean_inc(v_cache_474_);
lean_dec(v___x_473_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_503_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
lean_object* v___x_482_; 
if (v_isShared_480_ == 0)
{
lean_ctor_set(v___x_479_, 0, v_mctx_472_);
v___x_482_ = v___x_479_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v_mctx_472_);
lean_ctor_set(v_reuseFailAlloc_502_, 1, v_cache_474_);
lean_ctor_set(v_reuseFailAlloc_502_, 2, v_zetaDeltaFVarIds_475_);
lean_ctor_set(v_reuseFailAlloc_502_, 3, v_postponed_476_);
lean_ctor_set(v_reuseFailAlloc_502_, 4, v_diag_477_);
v___x_482_ = v_reuseFailAlloc_502_;
goto v_reusejp_481_;
}
v_reusejp_481_:
{
lean_object* v___x_483_; lean_object* v_eNew_484_; lean_object* v_eqProof_485_; lean_object* v_mvarIds_486_; lean_object* v___x_487_; lean_object* v___f_488_; lean_object* v___x_489_; 
v___x_483_ = lean_st_ref_put(v___y_461_, v___x_482_);
v_eNew_484_ = lean_ctor_get(v_result_471_, 0);
lean_inc_ref(v_eNew_484_);
v_eqProof_485_ = lean_ctor_get(v_result_471_, 1);
lean_inc_ref(v_eqProof_485_);
v_mvarIds_486_ = lean_ctor_get(v_result_471_, 2);
lean_inc(v_mvarIds_486_);
lean_dec_ref(v_result_471_);
lean_inc(v_f_425_);
v___x_487_ = l_Lean_mkFVar(v_f_425_);
lean_inc(v_a_420_);
v___f_488_ = lean_alloc_closure((void*)(l_Lean_Elab_Rewrites_evalExact___lam__1___boxed), 10, 5);
lean_closure_set(v___f_488_, 0, v_eqProof_485_);
lean_closure_set(v___f_488_, 1, v___x_487_);
lean_closure_set(v___f_488_, 2, v_eNew_484_);
lean_closure_set(v___f_488_, 3, v_a_420_);
lean_closure_set(v___f_488_, 4, v_f_425_);
v___x_489_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Rewrites_evalExact_spec__6___redArg(v_a_420_, v___f_488_, v___y_460_, v___y_461_, v___y_462_, v___y_463_);
if (lean_obj_tag(v___x_489_) == 0)
{
lean_object* v_a_490_; lean_object* v_mvarId_491_; lean_object* v___x_492_; lean_object* v___x_493_; 
v_a_490_ = lean_ctor_get(v___x_489_, 0);
lean_inc(v_a_490_);
lean_dec_ref_known(v___x_489_, 1);
v_mvarId_491_ = lean_ctor_get(v_a_490_, 1);
lean_inc(v_mvarId_491_);
lean_dec(v_a_490_);
v___x_492_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_492_, 0, v_mvarId_491_);
lean_ctor_set(v___x_492_, 1, v_mvarIds_486_);
v___x_493_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_492_, v___y_457_, v___y_460_, v___y_461_, v___y_462_, v___y_463_);
return v___x_493_;
}
else
{
lean_object* v_a_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_501_; 
lean_dec(v_mvarIds_486_);
v_a_494_ = lean_ctor_get(v___x_489_, 0);
v_isSharedCheck_501_ = !lean_is_exclusive(v___x_489_);
if (v_isSharedCheck_501_ == 0)
{
v___x_496_ = v___x_489_;
v_isShared_497_ = v_isSharedCheck_501_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_a_494_);
lean_dec(v___x_489_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_501_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v___x_499_; 
if (v_isShared_497_ == 0)
{
v___x_499_ = v___x_496_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v_a_494_);
v___x_499_ = v_reuseFailAlloc_500_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
return v___x_499_;
}
}
}
}
}
}
else
{
lean_object* v___x_506_; 
lean_dec(v___x_469_);
lean_dec(v_f_425_);
lean_dec(v_a_420_);
if (v_isShared_468_ == 0)
{
lean_ctor_set(v___x_467_, 0, v___x_464_);
v___x_506_ = v___x_467_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v___x_464_);
v___x_506_ = v_reuseFailAlloc_507_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
return v___x_506_;
}
}
}
}
else
{
lean_dec(v_a_454_);
lean_dec(v_f_425_);
lean_dec(v___x_423_);
lean_dec(v_a_420_);
return v___x_465_;
}
}
}
else
{
lean_object* v_a_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_534_; 
lean_dec(v_f_425_);
lean_dec(v___x_423_);
lean_dec(v_tk_422_);
lean_dec(v_a_420_);
v_a_527_ = lean_ctor_get(v___x_453_, 0);
v_isSharedCheck_534_ = !lean_is_exclusive(v___x_453_);
if (v_isSharedCheck_534_ == 0)
{
v___x_529_ = v___x_453_;
v_isShared_530_ = v_isSharedCheck_534_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_a_527_);
lean_dec(v___x_453_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_534_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
lean_object* v___x_532_; 
if (v_isShared_530_ == 0)
{
v___x_532_ = v___x_529_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v_a_527_);
v___x_532_ = v_reuseFailAlloc_533_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
return v___x_532_;
}
}
}
}
else
{
lean_object* v_a_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_542_; 
lean_dec(v_a_445_);
lean_dec(v_f_425_);
lean_dec(v___x_423_);
lean_dec(v_tk_422_);
lean_dec(v_a_420_);
lean_dec(v_a_419_);
v_a_535_ = lean_ctor_get(v___x_448_, 0);
v_isSharedCheck_542_ = !lean_is_exclusive(v___x_448_);
if (v_isSharedCheck_542_ == 0)
{
v___x_537_ = v___x_448_;
v_isShared_538_ = v_isSharedCheck_542_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_a_535_);
lean_dec(v___x_448_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_542_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
lean_object* v___x_540_; 
if (v_isShared_538_ == 0)
{
v___x_540_ = v___x_537_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v_a_535_);
v___x_540_ = v_reuseFailAlloc_541_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
return v___x_540_;
}
}
}
}
else
{
lean_object* v_a_543_; lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_550_; 
lean_dec(v_f_425_);
lean_dec(v___x_423_);
lean_dec(v_tk_422_);
lean_dec(v_a_420_);
lean_dec(v_a_419_);
v_a_543_ = lean_ctor_get(v___x_442_, 0);
v_isSharedCheck_550_ = !lean_is_exclusive(v___x_442_);
if (v_isSharedCheck_550_ == 0)
{
v___x_545_ = v___x_442_;
v_isShared_546_ = v_isSharedCheck_550_;
goto v_resetjp_544_;
}
else
{
lean_inc(v_a_543_);
lean_dec(v___x_442_);
v___x_545_ = lean_box(0);
v_isShared_546_ = v_isSharedCheck_550_;
goto v_resetjp_544_;
}
v_resetjp_544_:
{
lean_object* v___x_548_; 
if (v_isShared_546_ == 0)
{
v___x_548_ = v___x_545_;
goto v_reusejp_547_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v_a_543_);
v___x_548_ = v_reuseFailAlloc_549_;
goto v_reusejp_547_;
}
v_reusejp_547_:
{
return v___x_548_;
}
}
}
}
else
{
lean_object* v___x_551_; lean_object* v___x_553_; 
lean_dec(v_f_425_);
lean_dec(v___x_423_);
lean_dec(v_tk_422_);
lean_dec(v_a_420_);
lean_dec(v_a_419_);
v___x_551_ = lean_box(0);
if (v_isShared_439_ == 0)
{
lean_ctor_set(v___x_438_, 0, v___x_551_);
v___x_553_ = v___x_438_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v___x_551_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
return v___x_553_;
}
}
}
else
{
lean_object* v___x_555_; lean_object* v___x_557_; 
lean_dec(v_a_436_);
lean_dec(v_f_425_);
lean_dec(v___x_423_);
lean_dec(v_tk_422_);
lean_dec(v_a_420_);
lean_dec(v_a_419_);
v___x_555_ = lean_box(0);
if (v_isShared_439_ == 0)
{
lean_ctor_set(v___x_438_, 0, v___x_555_);
v___x_557_ = v___x_438_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v___x_555_);
v___x_557_ = v_reuseFailAlloc_558_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
return v___x_557_;
}
}
}
}
else
{
lean_object* v_a_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_567_; 
lean_dec(v_f_425_);
lean_dec(v___x_423_);
lean_dec(v_tk_422_);
lean_dec(v_a_420_);
lean_dec(v_a_419_);
v_a_560_ = lean_ctor_get(v___x_435_, 0);
v_isSharedCheck_567_ = !lean_is_exclusive(v___x_435_);
if (v_isSharedCheck_567_ == 0)
{
v___x_562_ = v___x_435_;
v_isShared_563_ = v_isSharedCheck_567_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_a_560_);
lean_dec(v___x_435_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_567_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v___x_565_; 
if (v_isShared_563_ == 0)
{
v___x_565_ = v___x_562_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v_a_560_);
v___x_565_ = v_reuseFailAlloc_566_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
return v___x_565_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact___lam__2___boxed(lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v___y_570_, lean_object* v_tk_571_, lean_object* v___x_572_, lean_object* v___x_573_, lean_object* v_f_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_){
_start:
{
lean_object* v_res_584_; 
v_res_584_ = l_Lean_Elab_Rewrites_evalExact___lam__2(v_a_568_, v_a_569_, v___y_570_, v_tk_571_, v___x_572_, v___x_573_, v_f_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_);
lean_dec(v___y_582_);
lean_dec_ref(v___y_581_);
lean_dec(v___y_580_);
lean_dec_ref(v___y_579_);
lean_dec(v___y_578_);
lean_dec_ref(v___y_577_);
lean_dec(v___y_576_);
lean_dec_ref(v___y_575_);
lean_dec(v___x_573_);
lean_dec(v___y_570_);
return v_res_584_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_Rewrites_evalExact_spec__3(lean_object* v_state_585_, lean_object* v_tk_586_, lean_object* v_as_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_){
_start:
{
if (lean_obj_tag(v_as_587_) == 0)
{
lean_object* v___x_597_; lean_object* v___x_598_; 
lean_dec(v_tk_586_);
lean_dec_ref(v_state_585_);
v___x_597_ = lean_box(0);
v___x_598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_598_, 0, v___x_597_);
return v___x_598_;
}
else
{
lean_object* v_head_599_; lean_object* v_tail_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
v_head_599_ = lean_ctor_get(v_as_587_, 0);
lean_inc(v_head_599_);
v_tail_600_ = lean_ctor_get(v_as_587_, 1);
lean_inc(v_tail_600_);
lean_dec_ref_known(v_as_587_, 2);
lean_inc_ref(v_state_585_);
v___x_601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_601_, 0, v_state_585_);
lean_inc(v_tk_586_);
v___x_602_ = l_Lean_Meta_Rewrites_RewriteResult_addSuggestion(v_tk_586_, v_head_599_, v___x_601_, v___y_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_);
if (lean_obj_tag(v___x_602_) == 0)
{
lean_dec_ref_known(v___x_602_, 1);
v_as_587_ = v_tail_600_;
goto _start;
}
else
{
lean_dec(v_tail_600_);
lean_dec(v_tk_586_);
lean_dec_ref(v_state_585_);
return v___x_602_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_Rewrites_evalExact_spec__3___boxed(lean_object* v_state_604_, lean_object* v_tk_605_, lean_object* v_as_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_){
_start:
{
lean_object* v_res_616_; 
v_res_616_ = l_List_forM___at___00Lean_Elab_Rewrites_evalExact_spec__3(v_state_604_, v_tk_605_, v_as_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_);
lean_dec(v___y_614_);
lean_dec_ref(v___y_613_);
lean_dec(v___y_612_);
lean_dec_ref(v___y_611_);
lean_dec(v___y_610_);
lean_dec_ref(v___y_609_);
lean_dec(v___y_608_);
lean_dec_ref(v___y_607_);
return v_res_616_;
}
}
static lean_object* _init_l_Lean_Elab_Rewrites_evalExact___lam__3___closed__9(void){
_start:
{
lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_627_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___lam__3___closed__8));
v___x_628_ = l_Lean_stringToMessageData(v___x_627_);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact___lam__3(lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v___y_631_, uint8_t v___x_632_, lean_object* v___x_633_, lean_object* v___x_634_, lean_object* v___x_635_, lean_object* v___x_636_, lean_object* v_tk_637_, lean_object* v___x_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_){
_start:
{
lean_object* v___x_648_; 
lean_inc(v_a_629_);
v___x_648_ = l_Lean_MVarId_getType(v_a_629_, v___y_643_, v___y_644_, v___y_645_, v___y_646_);
if (lean_obj_tag(v___x_648_) == 0)
{
lean_object* v_a_649_; lean_object* v___x_650_; lean_object* v_a_651_; lean_object* v___x_652_; lean_object* v___x_653_; 
v_a_649_ = lean_ctor_get(v___x_648_, 0);
lean_inc(v_a_649_);
lean_dec_ref_known(v___x_648_, 1);
v___x_650_ = l_Lean_instantiateMVars___at___00Lean_Elab_Rewrites_evalExact_spec__2___redArg(v_a_649_, v___y_644_);
v_a_651_ = lean_ctor_get(v___x_650_, 0);
lean_inc(v_a_651_);
lean_dec_ref(v___x_650_);
v___x_652_ = lean_box(0);
v___x_653_ = l_Lean_Meta_Rewrites_localHypotheses(v___x_652_, v___y_643_, v___y_644_, v___y_645_, v___y_646_);
if (lean_obj_tag(v___x_653_) == 0)
{
lean_object* v_a_654_; uint8_t v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; 
v_a_654_ = lean_ctor_get(v___x_653_, 0);
lean_inc(v_a_654_);
lean_dec_ref_known(v___x_653_, 1);
v___x_655_ = 2;
v___x_656_ = lean_unsigned_to_nat(20u);
v___x_657_ = lean_unsigned_to_nat(10u);
lean_inc(v_a_629_);
v___x_658_ = l_Lean_Meta_Rewrites_findRewrites(v_a_654_, v_a_630_, v_a_629_, v_a_651_, v___y_631_, v___x_655_, v___x_632_, v___x_656_, v___x_657_, v___y_643_, v___y_644_, v___y_645_, v___y_646_);
if (lean_obj_tag(v___x_658_) == 0)
{
lean_object* v_a_659_; lean_object* v___y_661_; lean_object* v___y_662_; lean_object* v___y_663_; lean_object* v___y_664_; lean_object* v___y_665_; lean_object* v___y_666_; lean_object* v___y_667_; lean_object* v___y_668_; lean_object* v___x_746_; lean_object* v___x_747_; 
v_a_659_ = lean_ctor_get(v___x_658_, 0);
lean_inc(v_a_659_);
lean_dec_ref_known(v___x_658_, 1);
v___x_746_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___lam__2___closed__1));
v___x_747_ = l_Lean_reportOutOfHeartbeats(v___x_746_, v_tk_637_, v___x_638_, v___y_645_, v___y_646_);
if (lean_obj_tag(v___x_747_) == 0)
{
uint8_t v___x_748_; 
lean_dec_ref_known(v___x_747_, 1);
v___x_748_ = l_List_isEmpty___redArg(v_a_659_);
if (v___x_748_ == 0)
{
v___y_661_ = v___y_639_;
v___y_662_ = v___y_640_;
v___y_663_ = v___y_641_;
v___y_664_ = v___y_642_;
v___y_665_ = v___y_643_;
v___y_666_ = v___y_644_;
v___y_667_ = v___y_645_;
v___y_668_ = v___y_646_;
goto v___jp_660_;
}
else
{
lean_object* v___x_749_; lean_object* v___x_750_; 
lean_dec(v_a_659_);
lean_dec(v_tk_637_);
lean_dec_ref(v___x_636_);
lean_dec_ref(v___x_635_);
lean_dec_ref(v___x_634_);
lean_dec(v___x_633_);
lean_dec(v_a_629_);
v___x_749_ = lean_obj_once(&l_Lean_Elab_Rewrites_evalExact___lam__3___closed__9, &l_Lean_Elab_Rewrites_evalExact___lam__3___closed__9_once, _init_l_Lean_Elab_Rewrites_evalExact___lam__3___closed__9);
v___x_750_ = l_Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__0___redArg(v___x_749_, v___y_643_, v___y_644_, v___y_645_, v___y_646_);
return v___x_750_;
}
}
else
{
lean_dec(v_a_659_);
lean_dec(v_tk_637_);
lean_dec_ref(v___x_636_);
lean_dec_ref(v___x_635_);
lean_dec_ref(v___x_634_);
lean_dec(v___x_633_);
lean_dec(v_a_629_);
return v___x_747_;
}
v___jp_660_:
{
lean_object* v___x_669_; 
v___x_669_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_662_, v___y_664_, v___y_666_, v___y_668_);
if (lean_obj_tag(v___x_669_) == 0)
{
lean_object* v_a_670_; lean_object* v___x_671_; 
v_a_670_ = lean_ctor_get(v___x_669_, 0);
lean_inc(v_a_670_);
lean_dec_ref_known(v___x_669_, 1);
v___x_671_ = l_List_get_x3fInternal___redArg(v_a_659_, v___x_633_);
if (lean_obj_tag(v___x_671_) == 1)
{
lean_object* v_val_672_; lean_object* v_result_673_; lean_object* v_mctx_674_; lean_object* v___x_675_; lean_object* v_cache_676_; lean_object* v_zetaDeltaFVarIds_677_; lean_object* v_postponed_678_; lean_object* v_diag_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_735_; 
lean_dec(v_a_670_);
v_val_672_ = lean_ctor_get(v___x_671_, 0);
lean_inc(v_val_672_);
lean_dec_ref_known(v___x_671_, 1);
v_result_673_ = lean_ctor_get(v_val_672_, 2);
lean_inc_ref(v_result_673_);
v_mctx_674_ = lean_ctor_get(v_val_672_, 3);
lean_inc_ref(v_mctx_674_);
lean_dec(v_val_672_);
v___x_675_ = lean_st_ref_take(v___y_666_);
v_cache_676_ = lean_ctor_get(v___x_675_, 1);
v_zetaDeltaFVarIds_677_ = lean_ctor_get(v___x_675_, 2);
v_postponed_678_ = lean_ctor_get(v___x_675_, 3);
v_diag_679_ = lean_ctor_get(v___x_675_, 4);
v_isSharedCheck_735_ = !lean_is_exclusive(v___x_675_);
if (v_isSharedCheck_735_ == 0)
{
lean_object* v_unused_736_; 
v_unused_736_ = lean_ctor_get(v___x_675_, 0);
lean_dec(v_unused_736_);
v___x_681_ = v___x_675_;
v_isShared_682_ = v_isSharedCheck_735_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_diag_679_);
lean_inc(v_postponed_678_);
lean_inc(v_zetaDeltaFVarIds_677_);
lean_inc(v_cache_676_);
lean_dec(v___x_675_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_735_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v___x_684_; 
if (v_isShared_682_ == 0)
{
lean_ctor_set(v___x_681_, 0, v_mctx_674_);
v___x_684_ = v___x_681_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v_mctx_674_);
lean_ctor_set(v_reuseFailAlloc_734_, 1, v_cache_676_);
lean_ctor_set(v_reuseFailAlloc_734_, 2, v_zetaDeltaFVarIds_677_);
lean_ctor_set(v_reuseFailAlloc_734_, 3, v_postponed_678_);
lean_ctor_set(v_reuseFailAlloc_734_, 4, v_diag_679_);
v___x_684_ = v_reuseFailAlloc_734_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_685_ = lean_st_ref_put(v___y_666_, v___x_684_);
v___x_686_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_662_, v___y_664_, v___y_666_, v___y_668_);
if (lean_obj_tag(v___x_686_) == 0)
{
lean_object* v_a_687_; lean_object* v_eNew_688_; lean_object* v_eqProof_689_; lean_object* v_mvarIds_690_; lean_object* v___x_691_; 
v_a_687_ = lean_ctor_get(v___x_686_, 0);
lean_inc(v_a_687_);
lean_dec_ref_known(v___x_686_, 1);
v_eNew_688_ = lean_ctor_get(v_result_673_, 0);
lean_inc_ref(v_eNew_688_);
v_eqProof_689_ = lean_ctor_get(v_result_673_, 1);
lean_inc_ref(v_eqProof_689_);
v_mvarIds_690_ = lean_ctor_get(v_result_673_, 2);
lean_inc(v_mvarIds_690_);
lean_dec_ref(v_result_673_);
v___x_691_ = l_Lean_MVarId_replaceTargetEq(v_a_629_, v_eNew_688_, v_eqProof_689_, v___y_665_, v___y_666_, v___y_667_, v___y_668_);
if (lean_obj_tag(v___x_691_) == 0)
{
lean_object* v_a_692_; lean_object* v___x_693_; lean_object* v___x_694_; 
v_a_692_ = lean_ctor_get(v___x_691_, 0);
lean_inc(v_a_692_);
lean_dec_ref_known(v___x_691_, 1);
v___x_693_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_693_, 0, v_a_692_);
lean_ctor_set(v___x_693_, 1, v_mvarIds_690_);
v___x_694_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_693_, v___y_662_, v___y_665_, v___y_666_, v___y_667_, v___y_668_);
if (lean_obj_tag(v___x_694_) == 0)
{
lean_object* v_ref_695_; uint8_t v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; 
lean_dec_ref_known(v___x_694_, 1);
v_ref_695_ = lean_ctor_get(v___y_667_, 2);
v___x_696_ = 0;
v___x_697_ = l_Lean_SourceInfo_fromRef(v_ref_695_, v___x_696_);
v___x_698_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___lam__3___closed__0));
lean_inc_ref_n(v___x_636_, 3);
lean_inc_ref_n(v___x_635_, 3);
lean_inc_ref_n(v___x_634_, 3);
v___x_699_ = l_Lean_Name_mkStr4(v___x_634_, v___x_635_, v___x_636_, v___x_698_);
v___x_700_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___lam__3___closed__1));
lean_inc_n(v___x_697_, 6);
v___x_701_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_701_, 0, v___x_697_);
lean_ctor_set(v___x_701_, 1, v___x_700_);
v___x_702_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___lam__3___closed__2));
v___x_703_ = l_Lean_Name_mkStr4(v___x_634_, v___x_635_, v___x_636_, v___x_702_);
v___x_704_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___lam__3___closed__3));
v___x_705_ = l_Lean_Name_mkStr4(v___x_634_, v___x_635_, v___x_636_, v___x_704_);
v___x_706_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___lam__3___closed__5));
v___x_707_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___lam__3___closed__6));
v___x_708_ = l_Lean_Name_mkStr4(v___x_634_, v___x_635_, v___x_636_, v___x_707_);
v___x_709_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___lam__3___closed__7));
v___x_710_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_710_, 0, v___x_697_);
lean_ctor_set(v___x_710_, 1, v___x_709_);
v___x_711_ = l_Lean_Syntax_node1(v___x_697_, v___x_708_, v___x_710_);
v___x_712_ = l_Lean_Syntax_node1(v___x_697_, v___x_706_, v___x_711_);
v___x_713_ = l_Lean_Syntax_node1(v___x_697_, v___x_705_, v___x_712_);
v___x_714_ = l_Lean_Syntax_node1(v___x_697_, v___x_703_, v___x_713_);
v___x_715_ = l_Lean_Syntax_node2(v___x_697_, v___x_699_, v___x_701_, v___x_714_);
v___x_716_ = l_Lean_Elab_Tactic_evalTactic(v___x_715_, v___y_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_);
if (lean_obj_tag(v___x_716_) == 0)
{
lean_object* v___x_717_; 
lean_dec_ref_known(v___x_716_, 1);
v___x_717_ = l_List_forM___at___00Lean_Elab_Rewrites_evalExact_spec__3(v_a_687_, v_tk_637_, v_a_659_, v___y_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_);
return v___x_717_;
}
else
{
lean_dec(v_a_687_);
lean_dec(v_a_659_);
lean_dec(v_tk_637_);
return v___x_716_;
}
}
else
{
lean_dec(v_a_687_);
lean_dec(v_a_659_);
lean_dec(v_tk_637_);
lean_dec_ref(v___x_636_);
lean_dec_ref(v___x_635_);
lean_dec_ref(v___x_634_);
return v___x_694_;
}
}
else
{
lean_object* v_a_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_725_; 
lean_dec(v_mvarIds_690_);
lean_dec(v_a_687_);
lean_dec(v_a_659_);
lean_dec(v_tk_637_);
lean_dec_ref(v___x_636_);
lean_dec_ref(v___x_635_);
lean_dec_ref(v___x_634_);
v_a_718_ = lean_ctor_get(v___x_691_, 0);
v_isSharedCheck_725_ = !lean_is_exclusive(v___x_691_);
if (v_isSharedCheck_725_ == 0)
{
v___x_720_ = v___x_691_;
v_isShared_721_ = v_isSharedCheck_725_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_a_718_);
lean_dec(v___x_691_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_725_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v___x_723_; 
if (v_isShared_721_ == 0)
{
v___x_723_ = v___x_720_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v_a_718_);
v___x_723_ = v_reuseFailAlloc_724_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
return v___x_723_;
}
}
}
}
else
{
lean_object* v_a_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_733_; 
lean_dec_ref(v_result_673_);
lean_dec(v_a_659_);
lean_dec(v_tk_637_);
lean_dec_ref(v___x_636_);
lean_dec_ref(v___x_635_);
lean_dec_ref(v___x_634_);
lean_dec(v_a_629_);
v_a_726_ = lean_ctor_get(v___x_686_, 0);
v_isSharedCheck_733_ = !lean_is_exclusive(v___x_686_);
if (v_isSharedCheck_733_ == 0)
{
v___x_728_ = v___x_686_;
v_isShared_729_ = v_isSharedCheck_733_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_a_726_);
lean_dec(v___x_686_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_733_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
lean_object* v___x_731_; 
if (v_isShared_729_ == 0)
{
v___x_731_ = v___x_728_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v_a_726_);
v___x_731_ = v_reuseFailAlloc_732_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
return v___x_731_;
}
}
}
}
}
}
else
{
lean_object* v___x_737_; 
lean_dec(v___x_671_);
lean_dec_ref(v___x_636_);
lean_dec_ref(v___x_635_);
lean_dec_ref(v___x_634_);
lean_dec(v_a_629_);
v___x_737_ = l_List_forM___at___00Lean_Elab_Rewrites_evalExact_spec__3(v_a_670_, v_tk_637_, v_a_659_, v___y_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_);
return v___x_737_;
}
}
else
{
lean_object* v_a_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_745_; 
lean_dec(v_a_659_);
lean_dec(v_tk_637_);
lean_dec_ref(v___x_636_);
lean_dec_ref(v___x_635_);
lean_dec_ref(v___x_634_);
lean_dec(v___x_633_);
lean_dec(v_a_629_);
v_a_738_ = lean_ctor_get(v___x_669_, 0);
v_isSharedCheck_745_ = !lean_is_exclusive(v___x_669_);
if (v_isSharedCheck_745_ == 0)
{
v___x_740_ = v___x_669_;
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_a_738_);
lean_dec(v___x_669_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___x_743_; 
if (v_isShared_741_ == 0)
{
v___x_743_ = v___x_740_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_a_738_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
return v___x_743_;
}
}
}
}
}
else
{
lean_object* v_a_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_758_; 
lean_dec(v_tk_637_);
lean_dec_ref(v___x_636_);
lean_dec_ref(v___x_635_);
lean_dec_ref(v___x_634_);
lean_dec(v___x_633_);
lean_dec(v_a_629_);
v_a_751_ = lean_ctor_get(v___x_658_, 0);
v_isSharedCheck_758_ = !lean_is_exclusive(v___x_658_);
if (v_isSharedCheck_758_ == 0)
{
v___x_753_ = v___x_658_;
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_a_751_);
lean_dec(v___x_658_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v___x_756_; 
if (v_isShared_754_ == 0)
{
v___x_756_ = v___x_753_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v_a_751_);
v___x_756_ = v_reuseFailAlloc_757_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
return v___x_756_;
}
}
}
}
else
{
lean_object* v_a_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_766_; 
lean_dec(v_a_651_);
lean_dec(v_tk_637_);
lean_dec_ref(v___x_636_);
lean_dec_ref(v___x_635_);
lean_dec_ref(v___x_634_);
lean_dec(v___x_633_);
lean_dec(v_a_630_);
lean_dec(v_a_629_);
v_a_759_ = lean_ctor_get(v___x_653_, 0);
v_isSharedCheck_766_ = !lean_is_exclusive(v___x_653_);
if (v_isSharedCheck_766_ == 0)
{
v___x_761_ = v___x_653_;
v_isShared_762_ = v_isSharedCheck_766_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_a_759_);
lean_dec(v___x_653_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_766_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v___x_764_; 
if (v_isShared_762_ == 0)
{
v___x_764_ = v___x_761_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v_a_759_);
v___x_764_ = v_reuseFailAlloc_765_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
return v___x_764_;
}
}
}
}
else
{
lean_object* v_a_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_774_; 
lean_dec(v_tk_637_);
lean_dec_ref(v___x_636_);
lean_dec_ref(v___x_635_);
lean_dec_ref(v___x_634_);
lean_dec(v___x_633_);
lean_dec(v_a_630_);
lean_dec(v_a_629_);
v_a_767_ = lean_ctor_get(v___x_648_, 0);
v_isSharedCheck_774_ = !lean_is_exclusive(v___x_648_);
if (v_isSharedCheck_774_ == 0)
{
v___x_769_ = v___x_648_;
v_isShared_770_ = v_isSharedCheck_774_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_a_767_);
lean_dec(v___x_648_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_774_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v___x_772_; 
if (v_isShared_770_ == 0)
{
v___x_772_ = v___x_769_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v_a_767_);
v___x_772_ = v_reuseFailAlloc_773_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
return v___x_772_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact___lam__3___boxed(lean_object** _args){
lean_object* v_a_775_ = _args[0];
lean_object* v_a_776_ = _args[1];
lean_object* v___y_777_ = _args[2];
lean_object* v___x_778_ = _args[3];
lean_object* v___x_779_ = _args[4];
lean_object* v___x_780_ = _args[5];
lean_object* v___x_781_ = _args[6];
lean_object* v___x_782_ = _args[7];
lean_object* v_tk_783_ = _args[8];
lean_object* v___x_784_ = _args[9];
lean_object* v___y_785_ = _args[10];
lean_object* v___y_786_ = _args[11];
lean_object* v___y_787_ = _args[12];
lean_object* v___y_788_ = _args[13];
lean_object* v___y_789_ = _args[14];
lean_object* v___y_790_ = _args[15];
lean_object* v___y_791_ = _args[16];
lean_object* v___y_792_ = _args[17];
lean_object* v___y_793_ = _args[18];
_start:
{
uint8_t v___x_22132__boxed_794_; lean_object* v_res_795_; 
v___x_22132__boxed_794_ = lean_unbox(v___x_778_);
v_res_795_ = l_Lean_Elab_Rewrites_evalExact___lam__3(v_a_775_, v_a_776_, v___y_777_, v___x_22132__boxed_794_, v___x_779_, v___x_780_, v___x_781_, v___x_782_, v_tk_783_, v___x_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_, v___y_789_, v___y_790_, v___y_791_, v___y_792_);
lean_dec(v___y_792_);
lean_dec_ref(v___y_791_);
lean_dec(v___y_790_);
lean_dec_ref(v___y_789_);
lean_dec(v___y_788_);
lean_dec_ref(v___y_787_);
lean_dec(v___y_786_);
lean_dec_ref(v___y_785_);
lean_dec(v___x_784_);
lean_dec(v___y_777_);
return v_res_795_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__7(size_t v_sz_796_, size_t v_i_797_, lean_object* v_bs_798_){
_start:
{
uint8_t v___x_799_; 
v___x_799_ = lean_usize_dec_lt(v_i_797_, v_sz_796_);
if (v___x_799_ == 0)
{
return v_bs_798_;
}
else
{
lean_object* v_v_800_; lean_object* v___x_801_; lean_object* v_bs_x27_802_; lean_object* v___x_803_; size_t v___x_804_; size_t v___x_805_; lean_object* v___x_806_; 
v_v_800_ = lean_array_uget(v_bs_798_, v_i_797_);
v___x_801_ = lean_unsigned_to_nat(0u);
v_bs_x27_802_ = lean_array_uset(v_bs_798_, v_i_797_, v___x_801_);
v___x_803_ = l_Lean_Syntax_getId(v_v_800_);
lean_dec(v_v_800_);
v___x_804_ = ((size_t)1ULL);
v___x_805_ = lean_usize_add(v_i_797_, v___x_804_);
v___x_806_ = lean_array_uset(v_bs_x27_802_, v_i_797_, v___x_803_);
v_i_797_ = v___x_805_;
v_bs_798_ = v___x_806_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__7___boxed(lean_object* v_sz_808_, lean_object* v_i_809_, lean_object* v_bs_810_){
_start:
{
size_t v_sz_boxed_811_; size_t v_i_boxed_812_; lean_object* v_res_813_; 
v_sz_boxed_811_ = lean_unbox_usize(v_sz_808_);
lean_dec(v_sz_808_);
v_i_boxed_812_ = lean_unbox_usize(v_i_809_);
lean_dec(v_i_809_);
v_res_813_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__7(v_sz_boxed_811_, v_i_boxed_812_, v_bs_810_);
return v_res_813_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Rewrites_evalExact_spec__10(uint8_t v___x_814_, uint8_t v___x_815_, lean_object* v_as_816_, size_t v_i_817_, size_t v_stop_818_, lean_object* v_b_819_){
_start:
{
lean_object* v___y_821_; uint8_t v___x_825_; 
v___x_825_ = lean_usize_dec_eq(v_i_817_, v_stop_818_);
if (v___x_825_ == 0)
{
lean_object* v_fst_826_; uint8_t v___x_827_; 
v_fst_826_ = lean_ctor_get(v_b_819_, 0);
v___x_827_ = lean_unbox(v_fst_826_);
if (v___x_827_ == 0)
{
lean_object* v_snd_828_; lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_836_; 
v_snd_828_ = lean_ctor_get(v_b_819_, 1);
v_isSharedCheck_836_ = !lean_is_exclusive(v_b_819_);
if (v_isSharedCheck_836_ == 0)
{
lean_object* v_unused_837_; 
v_unused_837_ = lean_ctor_get(v_b_819_, 0);
lean_dec(v_unused_837_);
v___x_830_ = v_b_819_;
v_isShared_831_ = v_isSharedCheck_836_;
goto v_resetjp_829_;
}
else
{
lean_inc(v_snd_828_);
lean_dec(v_b_819_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_836_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
lean_object* v___x_832_; lean_object* v___x_834_; 
v___x_832_ = lean_box(v___x_814_);
if (v_isShared_831_ == 0)
{
lean_ctor_set(v___x_830_, 0, v___x_832_);
v___x_834_ = v___x_830_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v___x_832_);
lean_ctor_set(v_reuseFailAlloc_835_, 1, v_snd_828_);
v___x_834_ = v_reuseFailAlloc_835_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
v___y_821_ = v___x_834_;
goto v___jp_820_;
}
}
}
else
{
lean_object* v_snd_838_; lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_848_; 
v_snd_838_ = lean_ctor_get(v_b_819_, 1);
v_isSharedCheck_848_ = !lean_is_exclusive(v_b_819_);
if (v_isSharedCheck_848_ == 0)
{
lean_object* v_unused_849_; 
v_unused_849_ = lean_ctor_get(v_b_819_, 0);
lean_dec(v_unused_849_);
v___x_840_ = v_b_819_;
v_isShared_841_ = v_isSharedCheck_848_;
goto v_resetjp_839_;
}
else
{
lean_inc(v_snd_838_);
lean_dec(v_b_819_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_848_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_846_; 
v___x_842_ = lean_array_uget_borrowed(v_as_816_, v_i_817_);
lean_inc(v___x_842_);
v___x_843_ = lean_array_push(v_snd_838_, v___x_842_);
v___x_844_ = lean_box(v___x_815_);
if (v_isShared_841_ == 0)
{
lean_ctor_set(v___x_840_, 1, v___x_843_);
lean_ctor_set(v___x_840_, 0, v___x_844_);
v___x_846_ = v___x_840_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v___x_844_);
lean_ctor_set(v_reuseFailAlloc_847_, 1, v___x_843_);
v___x_846_ = v_reuseFailAlloc_847_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
v___y_821_ = v___x_846_;
goto v___jp_820_;
}
}
}
}
else
{
return v_b_819_;
}
v___jp_820_:
{
size_t v___x_822_; size_t v___x_823_; 
v___x_822_ = ((size_t)1ULL);
v___x_823_ = lean_usize_add(v_i_817_, v___x_822_);
v_i_817_ = v___x_823_;
v_b_819_ = v___y_821_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Rewrites_evalExact_spec__10___boxed(lean_object* v___x_850_, lean_object* v___x_851_, lean_object* v_as_852_, lean_object* v_i_853_, lean_object* v_stop_854_, lean_object* v_b_855_){
_start:
{
uint8_t v___x_22451__boxed_856_; uint8_t v___x_22452__boxed_857_; size_t v_i_boxed_858_; size_t v_stop_boxed_859_; lean_object* v_res_860_; 
v___x_22451__boxed_856_ = lean_unbox(v___x_850_);
v___x_22452__boxed_857_ = lean_unbox(v___x_851_);
v_i_boxed_858_ = lean_unbox_usize(v_i_853_);
lean_dec(v_i_853_);
v_stop_boxed_859_ = lean_unbox_usize(v_stop_854_);
lean_dec(v_stop_854_);
v_res_860_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Rewrites_evalExact_spec__10(v___x_22451__boxed_856_, v___x_22452__boxed_857_, v_as_852_, v_i_boxed_858_, v_stop_boxed_859_, v_b_855_);
lean_dec_ref(v_as_852_);
return v_res_860_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Rewrites_evalExact_spec__8(lean_object* v_as_861_, size_t v_i_862_, size_t v_stop_863_, lean_object* v_b_864_){
_start:
{
uint8_t v___x_865_; 
v___x_865_ = lean_usize_dec_eq(v_i_862_, v_stop_863_);
if (v___x_865_ == 0)
{
lean_object* v___x_866_; lean_object* v___x_867_; size_t v___x_868_; size_t v___x_869_; 
v___x_866_ = lean_array_uget_borrowed(v_as_861_, v_i_862_);
lean_inc(v___x_866_);
v___x_867_ = l_Lean_NameSet_insert(v_b_864_, v___x_866_);
v___x_868_ = ((size_t)1ULL);
v___x_869_ = lean_usize_add(v_i_862_, v___x_868_);
v_i_862_ = v___x_869_;
v_b_864_ = v___x_867_;
goto _start;
}
else
{
return v_b_864_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Rewrites_evalExact_spec__8___boxed(lean_object* v_as_871_, lean_object* v_i_872_, lean_object* v_stop_873_, lean_object* v_b_874_){
_start:
{
size_t v_i_boxed_875_; size_t v_stop_boxed_876_; lean_object* v_res_877_; 
v_i_boxed_875_ = lean_unbox_usize(v_i_872_);
lean_dec(v_i_872_);
v_stop_boxed_876_ = lean_unbox_usize(v_stop_873_);
lean_dec(v_stop_873_);
v_res_877_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Rewrites_evalExact_spec__8(v_as_871_, v_i_boxed_875_, v_stop_boxed_876_, v_b_874_);
lean_dec_ref(v_as_871_);
return v_res_877_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__9(size_t v_sz_881_, size_t v_i_882_, lean_object* v_bs_883_){
_start:
{
uint8_t v___x_884_; 
v___x_884_ = lean_usize_dec_lt(v_i_882_, v_sz_881_);
if (v___x_884_ == 0)
{
lean_object* v___x_885_; 
v___x_885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_885_, 0, v_bs_883_);
return v___x_885_;
}
else
{
lean_object* v_v_886_; lean_object* v___x_887_; uint8_t v___x_888_; 
v_v_886_ = lean_array_uget(v_bs_883_, v_i_882_);
v___x_887_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__9___closed__1));
lean_inc(v_v_886_);
v___x_888_ = l_Lean_Syntax_isOfKind(v_v_886_, v___x_887_);
if (v___x_888_ == 0)
{
lean_object* v___x_889_; 
lean_dec(v_v_886_);
lean_dec_ref(v_bs_883_);
v___x_889_ = lean_box(0);
return v___x_889_;
}
else
{
lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v_bs_x27_892_; lean_object* v_forbidden_893_; size_t v___x_894_; size_t v___x_895_; lean_object* v___x_896_; 
v___x_890_ = lean_unsigned_to_nat(1u);
v___x_891_ = lean_unsigned_to_nat(0u);
v_bs_x27_892_ = lean_array_uset(v_bs_883_, v_i_882_, v___x_891_);
v_forbidden_893_ = l_Lean_Syntax_getArg(v_v_886_, v___x_890_);
lean_dec(v_v_886_);
v___x_894_ = ((size_t)1ULL);
v___x_895_ = lean_usize_add(v_i_882_, v___x_894_);
v___x_896_ = lean_array_uset(v_bs_x27_892_, v_i_882_, v_forbidden_893_);
v_i_882_ = v___x_895_;
v_bs_883_ = v___x_896_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__9___boxed(lean_object* v_sz_898_, lean_object* v_i_899_, lean_object* v_bs_900_){
_start:
{
size_t v_sz_boxed_901_; size_t v_i_boxed_902_; lean_object* v_res_903_; 
v_sz_boxed_901_ = lean_unbox_usize(v_sz_898_);
lean_dec(v_sz_898_);
v_i_boxed_902_ = lean_unbox_usize(v_i_899_);
lean_dec(v_i_899_);
v_res_903_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__9(v_sz_boxed_901_, v_i_boxed_902_, v_bs_900_);
return v_res_903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact(lean_object* v_stx_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_){
_start:
{
lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; uint8_t v___x_941_; 
v___x_937_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___closed__0));
v___x_938_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___closed__1));
v___x_939_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___closed__2));
v___x_940_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___closed__4));
lean_inc(v_stx_927_);
v___x_941_ = l_Lean_Syntax_isOfKind(v_stx_927_, v___x_940_);
if (v___x_941_ == 0)
{
lean_object* v___x_942_; 
lean_dec(v_stx_927_);
v___x_942_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__1___redArg();
return v___x_942_;
}
else
{
lean_object* v___f_943_; lean_object* v___y_945_; lean_object* v___y_946_; lean_object* v___y_947_; lean_object* v___y_948_; lean_object* v___y_949_; lean_object* v___y_950_; lean_object* v___y_951_; lean_object* v___y_952_; lean_object* v___y_953_; lean_object* v___y_954_; lean_object* v___y_955_; lean_object* v___x_959_; lean_object* v_tk_960_; lean_object* v___y_962_; lean_object* v___y_963_; lean_object* v___y_964_; lean_object* v___y_965_; lean_object* v___y_966_; lean_object* v___y_967_; lean_object* v___y_968_; lean_object* v___y_969_; lean_object* v___y_970_; lean_object* v___y_971_; lean_object* v___y_972_; lean_object* v___y_999_; lean_object* v___y_1000_; lean_object* v___y_1001_; lean_object* v___y_1002_; lean_object* v___y_1003_; lean_object* v___y_1004_; lean_object* v___y_1005_; lean_object* v___y_1006_; lean_object* v___y_1007_; lean_object* v___y_1008_; lean_object* v___y_1009_; lean_object* v___y_1010_; lean_object* v___y_1022_; lean_object* v_forbidden_1023_; lean_object* v___y_1024_; lean_object* v___y_1025_; lean_object* v___y_1026_; lean_object* v___y_1027_; lean_object* v___y_1028_; lean_object* v___y_1029_; lean_object* v___y_1030_; lean_object* v___y_1031_; lean_object* v___y_1046_; lean_object* v___y_1047_; lean_object* v___y_1048_; lean_object* v___y_1049_; lean_object* v___y_1050_; lean_object* v___y_1051_; lean_object* v___y_1052_; lean_object* v___y_1053_; lean_object* v___y_1054_; lean_object* v___y_1055_; lean_object* v___x_1060_; lean_object* v_loc_1062_; lean_object* v___y_1063_; lean_object* v___y_1064_; lean_object* v___y_1065_; lean_object* v___y_1066_; lean_object* v___y_1067_; lean_object* v___y_1068_; lean_object* v___y_1069_; lean_object* v___y_1070_; lean_object* v___x_1092_; uint8_t v___x_1093_; 
v___f_943_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___closed__5));
v___x_959_ = lean_unsigned_to_nat(0u);
v_tk_960_ = l_Lean_Syntax_getArg(v_stx_927_, v___x_959_);
v___x_1060_ = lean_unsigned_to_nat(1u);
v___x_1092_ = l_Lean_Syntax_getArg(v_stx_927_, v___x_1060_);
v___x_1093_ = l_Lean_Syntax_isNone(v___x_1092_);
if (v___x_1093_ == 0)
{
uint8_t v___x_1094_; 
lean_inc(v___x_1092_);
v___x_1094_ = l_Lean_Syntax_matchesNull(v___x_1092_, v___x_1060_);
if (v___x_1094_ == 0)
{
lean_object* v___x_1095_; 
lean_dec(v___x_1092_);
lean_dec(v_tk_960_);
lean_dec(v_stx_927_);
v___x_1095_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__1___redArg();
return v___x_1095_;
}
else
{
lean_object* v_loc_1096_; lean_object* v___x_1097_; 
v_loc_1096_ = l_Lean_Syntax_getArg(v___x_1092_, v___x_959_);
lean_dec(v___x_1092_);
v___x_1097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1097_, 0, v_loc_1096_);
v_loc_1062_ = v___x_1097_;
v___y_1063_ = v_a_928_;
v___y_1064_ = v_a_929_;
v___y_1065_ = v_a_930_;
v___y_1066_ = v_a_931_;
v___y_1067_ = v_a_932_;
v___y_1068_ = v_a_933_;
v___y_1069_ = v_a_934_;
v___y_1070_ = v_a_935_;
goto v___jp_1061_;
}
}
else
{
lean_object* v___x_1098_; 
lean_dec(v___x_1092_);
v___x_1098_ = lean_box(0);
v_loc_1062_ = v___x_1098_;
v___y_1063_ = v_a_928_;
v___y_1064_ = v_a_929_;
v___y_1065_ = v_a_930_;
v___y_1066_ = v_a_931_;
v___y_1067_ = v_a_932_;
v___y_1068_ = v_a_933_;
v___y_1069_ = v_a_934_;
v___y_1070_ = v_a_935_;
goto v___jp_1061_;
}
v___jp_944_:
{
lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; 
v___x_956_ = l_Lean_mkOptionalNode(v___y_955_);
v___x_957_ = l_Lean_Elab_Tactic_expandOptLocation(v___x_956_);
lean_dec(v___x_956_);
v___x_958_ = l_Lean_Elab_Tactic_withLocation(v___x_957_, v___y_949_, v___y_952_, v___f_943_, v___y_948_, v___y_951_, v___y_946_, v___y_947_, v___y_953_, v___y_950_, v___y_954_, v___y_945_);
lean_dec(v___x_957_);
return v___x_958_;
}
v___jp_961_:
{
lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_973_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___closed__7));
v___x_974_ = lean_unsigned_to_nat(90u);
v___x_975_ = l_Lean_reportOutOfHeartbeats(v___x_973_, v_tk_960_, v___x_974_, v___y_971_, v___y_963_);
if (lean_obj_tag(v___x_975_) == 0)
{
lean_object* v___x_976_; 
lean_dec_ref_known(v___x_975_, 1);
v___x_976_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_969_, v___y_970_, v___y_968_, v___y_971_, v___y_963_);
if (lean_obj_tag(v___x_976_) == 0)
{
lean_object* v_a_977_; lean_object* v___f_978_; lean_object* v___x_979_; lean_object* v___f_980_; 
v_a_977_ = lean_ctor_get(v___x_976_, 0);
lean_inc_n(v_a_977_, 2);
lean_dec_ref_known(v___x_976_, 1);
lean_inc(v_tk_960_);
lean_inc(v___y_972_);
lean_inc(v___y_962_);
v___f_978_ = lean_alloc_closure((void*)(l_Lean_Elab_Rewrites_evalExact___lam__2___boxed), 16, 6);
lean_closure_set(v___f_978_, 0, v___y_962_);
lean_closure_set(v___f_978_, 1, v_a_977_);
lean_closure_set(v___f_978_, 2, v___y_972_);
lean_closure_set(v___f_978_, 3, v_tk_960_);
lean_closure_set(v___f_978_, 4, v___x_959_);
lean_closure_set(v___f_978_, 5, v___x_974_);
v___x_979_ = lean_box(v___x_941_);
v___f_980_ = lean_alloc_closure((void*)(l_Lean_Elab_Rewrites_evalExact___lam__3___boxed), 19, 10);
lean_closure_set(v___f_980_, 0, v_a_977_);
lean_closure_set(v___f_980_, 1, v___y_962_);
lean_closure_set(v___f_980_, 2, v___y_972_);
lean_closure_set(v___f_980_, 3, v___x_979_);
lean_closure_set(v___f_980_, 4, v___x_959_);
lean_closure_set(v___f_980_, 5, v___x_937_);
lean_closure_set(v___f_980_, 6, v___x_938_);
lean_closure_set(v___f_980_, 7, v___x_939_);
lean_closure_set(v___f_980_, 8, v_tk_960_);
lean_closure_set(v___f_980_, 9, v___x_974_);
if (lean_obj_tag(v___y_966_) == 0)
{
lean_object* v___x_981_; 
v___x_981_ = lean_box(0);
v___y_945_ = v___y_963_;
v___y_946_ = v___y_964_;
v___y_947_ = v___y_965_;
v___y_948_ = v___y_967_;
v___y_949_ = v___f_978_;
v___y_950_ = v___y_968_;
v___y_951_ = v___y_969_;
v___y_952_ = v___f_980_;
v___y_953_ = v___y_970_;
v___y_954_ = v___y_971_;
v___y_955_ = v___x_981_;
goto v___jp_944_;
}
else
{
lean_object* v_val_982_; lean_object* v___x_984_; uint8_t v_isShared_985_; uint8_t v_isSharedCheck_989_; 
v_val_982_ = lean_ctor_get(v___y_966_, 0);
v_isSharedCheck_989_ = !lean_is_exclusive(v___y_966_);
if (v_isSharedCheck_989_ == 0)
{
v___x_984_ = v___y_966_;
v_isShared_985_ = v_isSharedCheck_989_;
goto v_resetjp_983_;
}
else
{
lean_inc(v_val_982_);
lean_dec(v___y_966_);
v___x_984_ = lean_box(0);
v_isShared_985_ = v_isSharedCheck_989_;
goto v_resetjp_983_;
}
v_resetjp_983_:
{
lean_object* v___x_987_; 
if (v_isShared_985_ == 0)
{
v___x_987_ = v___x_984_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v_val_982_);
v___x_987_ = v_reuseFailAlloc_988_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
v___y_945_ = v___y_963_;
v___y_946_ = v___y_964_;
v___y_947_ = v___y_965_;
v___y_948_ = v___y_967_;
v___y_949_ = v___f_978_;
v___y_950_ = v___y_968_;
v___y_951_ = v___y_969_;
v___y_952_ = v___f_980_;
v___y_953_ = v___y_970_;
v___y_954_ = v___y_971_;
v___y_955_ = v___x_987_;
goto v___jp_944_;
}
}
}
}
else
{
lean_object* v_a_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_997_; 
lean_dec(v___y_972_);
lean_dec(v___y_966_);
lean_dec(v___y_962_);
lean_dec(v_tk_960_);
v_a_990_ = lean_ctor_get(v___x_976_, 0);
v_isSharedCheck_997_ = !lean_is_exclusive(v___x_976_);
if (v_isSharedCheck_997_ == 0)
{
v___x_992_ = v___x_976_;
v_isShared_993_ = v_isSharedCheck_997_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_a_990_);
lean_dec(v___x_976_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_997_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
lean_object* v___x_995_; 
if (v_isShared_993_ == 0)
{
v___x_995_ = v___x_992_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v_a_990_);
v___x_995_ = v_reuseFailAlloc_996_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
return v___x_995_;
}
}
}
}
else
{
lean_dec(v___y_972_);
lean_dec(v___y_966_);
lean_dec(v___y_962_);
lean_dec(v_tk_960_);
return v___x_975_;
}
}
v___jp_998_:
{
size_t v_sz_1011_; size_t v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; uint8_t v___x_1015_; 
v_sz_1011_ = lean_array_size(v___y_1010_);
v___x_1012_ = ((size_t)0ULL);
v___x_1013_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__7(v_sz_1011_, v___x_1012_, v___y_1010_);
v___x_1014_ = lean_array_get_size(v___x_1013_);
v___x_1015_ = lean_nat_dec_lt(v___x_959_, v___x_1014_);
if (v___x_1015_ == 0)
{
lean_dec_ref(v___x_1013_);
lean_inc(v___y_1008_);
v___y_962_ = v___y_999_;
v___y_963_ = v___y_1000_;
v___y_964_ = v___y_1001_;
v___y_965_ = v___y_1002_;
v___y_966_ = v___y_1003_;
v___y_967_ = v___y_1004_;
v___y_968_ = v___y_1006_;
v___y_969_ = v___y_1005_;
v___y_970_ = v___y_1007_;
v___y_971_ = v___y_1009_;
v___y_972_ = v___y_1008_;
goto v___jp_961_;
}
else
{
uint8_t v___x_1016_; 
v___x_1016_ = lean_nat_dec_le(v___x_1014_, v___x_1014_);
if (v___x_1016_ == 0)
{
if (v___x_1015_ == 0)
{
lean_dec_ref(v___x_1013_);
lean_inc(v___y_1008_);
v___y_962_ = v___y_999_;
v___y_963_ = v___y_1000_;
v___y_964_ = v___y_1001_;
v___y_965_ = v___y_1002_;
v___y_966_ = v___y_1003_;
v___y_967_ = v___y_1004_;
v___y_968_ = v___y_1006_;
v___y_969_ = v___y_1005_;
v___y_970_ = v___y_1007_;
v___y_971_ = v___y_1009_;
v___y_972_ = v___y_1008_;
goto v___jp_961_;
}
else
{
size_t v___x_1017_; lean_object* v___x_1018_; 
v___x_1017_ = lean_usize_of_nat(v___x_1014_);
lean_inc(v___y_1008_);
v___x_1018_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Rewrites_evalExact_spec__8(v___x_1013_, v___x_1012_, v___x_1017_, v___y_1008_);
lean_dec_ref(v___x_1013_);
v___y_962_ = v___y_999_;
v___y_963_ = v___y_1000_;
v___y_964_ = v___y_1001_;
v___y_965_ = v___y_1002_;
v___y_966_ = v___y_1003_;
v___y_967_ = v___y_1004_;
v___y_968_ = v___y_1006_;
v___y_969_ = v___y_1005_;
v___y_970_ = v___y_1007_;
v___y_971_ = v___y_1009_;
v___y_972_ = v___x_1018_;
goto v___jp_961_;
}
}
else
{
size_t v___x_1019_; lean_object* v___x_1020_; 
v___x_1019_ = lean_usize_of_nat(v___x_1014_);
lean_inc(v___y_1008_);
v___x_1020_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Rewrites_evalExact_spec__8(v___x_1013_, v___x_1012_, v___x_1019_, v___y_1008_);
lean_dec_ref(v___x_1013_);
v___y_962_ = v___y_999_;
v___y_963_ = v___y_1000_;
v___y_964_ = v___y_1001_;
v___y_965_ = v___y_1002_;
v___y_966_ = v___y_1003_;
v___y_967_ = v___y_1004_;
v___y_968_ = v___y_1006_;
v___y_969_ = v___y_1005_;
v___y_970_ = v___y_1007_;
v___y_971_ = v___y_1009_;
v___y_972_ = v___x_1020_;
goto v___jp_961_;
}
}
}
v___jp_1021_:
{
lean_object* v___x_1032_; 
v___x_1032_ = l_Lean_Meta_Rewrites_createModuleTreeRef(v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_);
if (lean_obj_tag(v___x_1032_) == 0)
{
lean_object* v_a_1033_; lean_object* v___x_1034_; 
v_a_1033_ = lean_ctor_get(v___x_1032_, 0);
lean_inc(v_a_1033_);
lean_dec_ref_known(v___x_1032_, 1);
v___x_1034_ = l_Lean_NameSet_empty;
if (lean_obj_tag(v_forbidden_1023_) == 0)
{
lean_object* v___x_1035_; 
v___x_1035_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___closed__8));
v___y_999_ = v_a_1033_;
v___y_1000_ = v___y_1031_;
v___y_1001_ = v___y_1026_;
v___y_1002_ = v___y_1027_;
v___y_1003_ = v___y_1022_;
v___y_1004_ = v___y_1024_;
v___y_1005_ = v___y_1025_;
v___y_1006_ = v___y_1029_;
v___y_1007_ = v___y_1028_;
v___y_1008_ = v___x_1034_;
v___y_1009_ = v___y_1030_;
v___y_1010_ = v___x_1035_;
goto v___jp_998_;
}
else
{
lean_object* v_val_1036_; 
v_val_1036_ = lean_ctor_get(v_forbidden_1023_, 0);
lean_inc(v_val_1036_);
lean_dec_ref_known(v_forbidden_1023_, 1);
v___y_999_ = v_a_1033_;
v___y_1000_ = v___y_1031_;
v___y_1001_ = v___y_1026_;
v___y_1002_ = v___y_1027_;
v___y_1003_ = v___y_1022_;
v___y_1004_ = v___y_1024_;
v___y_1005_ = v___y_1025_;
v___y_1006_ = v___y_1029_;
v___y_1007_ = v___y_1028_;
v___y_1008_ = v___x_1034_;
v___y_1009_ = v___y_1030_;
v___y_1010_ = v_val_1036_;
goto v___jp_998_;
}
}
else
{
lean_object* v_a_1037_; lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1044_; 
lean_dec(v_forbidden_1023_);
lean_dec(v___y_1022_);
lean_dec(v_tk_960_);
v_a_1037_ = lean_ctor_get(v___x_1032_, 0);
v_isSharedCheck_1044_ = !lean_is_exclusive(v___x_1032_);
if (v_isSharedCheck_1044_ == 0)
{
v___x_1039_ = v___x_1032_;
v_isShared_1040_ = v_isSharedCheck_1044_;
goto v_resetjp_1038_;
}
else
{
lean_inc(v_a_1037_);
lean_dec(v___x_1032_);
v___x_1039_ = lean_box(0);
v_isShared_1040_ = v_isSharedCheck_1044_;
goto v_resetjp_1038_;
}
v_resetjp_1038_:
{
lean_object* v___x_1042_; 
if (v_isShared_1040_ == 0)
{
v___x_1042_ = v___x_1039_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v_a_1037_);
v___x_1042_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
return v___x_1042_;
}
}
}
}
v___jp_1045_:
{
size_t v_sz_1056_; size_t v___x_1057_; lean_object* v___x_1058_; 
v_sz_1056_ = lean_array_size(v___y_1055_);
v___x_1057_ = ((size_t)0ULL);
v___x_1058_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__9(v_sz_1056_, v___x_1057_, v___y_1055_);
if (lean_obj_tag(v___x_1058_) == 0)
{
lean_object* v___x_1059_; 
lean_dec(v___y_1048_);
lean_dec(v_tk_960_);
v___x_1059_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__1___redArg();
return v___x_1059_;
}
else
{
v___y_1022_ = v___y_1048_;
v_forbidden_1023_ = v___x_1058_;
v___y_1024_ = v___y_1054_;
v___y_1025_ = v___y_1047_;
v___y_1026_ = v___y_1051_;
v___y_1027_ = v___y_1050_;
v___y_1028_ = v___y_1052_;
v___y_1029_ = v___y_1049_;
v___y_1030_ = v___y_1046_;
v___y_1031_ = v___y_1053_;
goto v___jp_1021_;
}
}
v___jp_1061_:
{
lean_object* v___x_1071_; lean_object* v___x_1072_; uint8_t v___x_1073_; 
v___x_1071_ = lean_unsigned_to_nat(2u);
v___x_1072_ = l_Lean_Syntax_getArg(v_stx_927_, v___x_1071_);
lean_dec(v_stx_927_);
v___x_1073_ = l_Lean_Syntax_isNone(v___x_1072_);
if (v___x_1073_ == 0)
{
uint8_t v___x_1074_; 
lean_inc(v___x_1072_);
v___x_1074_ = l_Lean_Syntax_matchesNull(v___x_1072_, v___x_1060_);
if (v___x_1074_ == 0)
{
lean_object* v___x_1075_; 
lean_dec(v___x_1072_);
lean_dec(v_loc_1062_);
lean_dec(v_tk_960_);
v___x_1075_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__1___redArg();
return v___x_1075_;
}
else
{
lean_object* v___x_1076_; lean_object* v___x_1077_; uint8_t v___x_1078_; 
v___x_1076_ = l_Lean_Syntax_getArg(v___x_1072_, v___x_959_);
lean_dec(v___x_1072_);
v___x_1077_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___closed__10));
lean_inc(v___x_1076_);
v___x_1078_ = l_Lean_Syntax_isOfKind(v___x_1076_, v___x_1077_);
if (v___x_1078_ == 0)
{
lean_object* v___x_1079_; 
lean_dec(v___x_1076_);
lean_dec(v_loc_1062_);
lean_dec(v_tk_960_);
v___x_1079_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__1___redArg();
return v___x_1079_;
}
else
{
lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; uint8_t v___x_1084_; 
v___x_1080_ = l_Lean_Syntax_getArg(v___x_1076_, v___x_1060_);
lean_dec(v___x_1076_);
v___x_1081_ = l_Lean_Syntax_getArgs(v___x_1080_);
lean_dec(v___x_1080_);
v___x_1082_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___closed__11));
v___x_1083_ = lean_array_get_size(v___x_1081_);
v___x_1084_ = lean_nat_dec_lt(v___x_959_, v___x_1083_);
if (v___x_1084_ == 0)
{
lean_dec_ref(v___x_1081_);
v___y_1046_ = v___y_1069_;
v___y_1047_ = v___y_1064_;
v___y_1048_ = v_loc_1062_;
v___y_1049_ = v___y_1068_;
v___y_1050_ = v___y_1066_;
v___y_1051_ = v___y_1065_;
v___y_1052_ = v___y_1067_;
v___y_1053_ = v___y_1070_;
v___y_1054_ = v___y_1063_;
v___y_1055_ = v___x_1082_;
goto v___jp_1045_;
}
else
{
lean_object* v___x_1085_; lean_object* v___x_1086_; size_t v___x_1087_; size_t v___x_1088_; lean_object* v___x_1089_; lean_object* v_snd_1090_; 
v___x_1085_ = lean_box(v___x_1084_);
v___x_1086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1086_, 0, v___x_1085_);
lean_ctor_set(v___x_1086_, 1, v___x_1082_);
v___x_1087_ = ((size_t)0ULL);
v___x_1088_ = lean_usize_of_nat(v___x_1083_);
v___x_1089_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Rewrites_evalExact_spec__10(v___x_1078_, v___x_1073_, v___x_1081_, v___x_1087_, v___x_1088_, v___x_1086_);
lean_dec_ref(v___x_1081_);
v_snd_1090_ = lean_ctor_get(v___x_1089_, 1);
lean_inc(v_snd_1090_);
lean_dec_ref(v___x_1089_);
v___y_1046_ = v___y_1069_;
v___y_1047_ = v___y_1064_;
v___y_1048_ = v_loc_1062_;
v___y_1049_ = v___y_1068_;
v___y_1050_ = v___y_1066_;
v___y_1051_ = v___y_1065_;
v___y_1052_ = v___y_1067_;
v___y_1053_ = v___y_1070_;
v___y_1054_ = v___y_1063_;
v___y_1055_ = v_snd_1090_;
goto v___jp_1045_;
}
}
}
}
else
{
lean_object* v___x_1091_; 
lean_dec(v___x_1072_);
v___x_1091_ = lean_box(0);
v___y_1022_ = v_loc_1062_;
v_forbidden_1023_ = v___x_1091_;
v___y_1024_ = v___y_1063_;
v___y_1025_ = v___y_1064_;
v___y_1026_ = v___y_1065_;
v___y_1027_ = v___y_1066_;
v___y_1028_ = v___y_1067_;
v___y_1029_ = v___y_1068_;
v___y_1030_ = v___y_1069_;
v___y_1031_ = v___y_1070_;
goto v___jp_1021_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact___boxed(lean_object* v_stx_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_){
_start:
{
lean_object* v_res_1109_; 
v_res_1109_ = l_Lean_Elab_Rewrites_evalExact(v_stx_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_);
lean_dec(v_a_1107_);
lean_dec_ref(v_a_1106_);
lean_dec(v_a_1105_);
lean_dec_ref(v_a_1104_);
lean_dec(v_a_1103_);
lean_dec_ref(v_a_1102_);
lean_dec(v_a_1101_);
lean_dec_ref(v_a_1100_);
return v_res_1109_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__0(lean_object* v_00_u03b1_1110_, lean_object* v_msg_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_){
_start:
{
lean_object* v___x_1121_; 
v___x_1121_ = l_Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__0___redArg(v_msg_1111_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_);
return v___x_1121_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__0___boxed(lean_object* v_00_u03b1_1122_, lean_object* v_msg_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_){
_start:
{
lean_object* v_res_1133_; 
v_res_1133_ = l_Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__0(v_00_u03b1_1122_, v_msg_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_);
lean_dec(v___y_1131_);
lean_dec_ref(v___y_1130_);
lean_dec(v___y_1129_);
lean_dec_ref(v___y_1128_);
lean_dec(v___y_1127_);
lean_dec_ref(v___y_1126_);
lean_dec(v___y_1125_);
lean_dec_ref(v___y_1124_);
return v_res_1133_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__5(lean_object* v_f_1134_, lean_object* v_tk_1135_, lean_object* v_as_1136_, lean_object* v_as_x27_1137_, lean_object* v_b_1138_, lean_object* v_a_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_){
_start:
{
lean_object* v___x_1149_; 
v___x_1149_ = l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__5___redArg(v_f_1134_, v_tk_1135_, v_as_x27_1137_, v_b_1138_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_);
return v___x_1149_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__5___boxed(lean_object* v_f_1150_, lean_object* v_tk_1151_, lean_object* v_as_1152_, lean_object* v_as_x27_1153_, lean_object* v_b_1154_, lean_object* v_a_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_){
_start:
{
lean_object* v_res_1165_; 
v_res_1165_ = l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__5(v_f_1150_, v_tk_1151_, v_as_1152_, v_as_x27_1153_, v_b_1154_, v_a_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_);
lean_dec(v___y_1163_);
lean_dec_ref(v___y_1162_);
lean_dec(v___y_1161_);
lean_dec_ref(v___y_1160_);
lean_dec(v___y_1159_);
lean_dec_ref(v___y_1158_);
lean_dec(v___y_1157_);
lean_dec_ref(v___y_1156_);
lean_dec(v_as_x27_1153_);
lean_dec(v_as_1152_);
return v_res_1165_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1(){
_start:
{
lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; 
v___x_1175_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1176_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___closed__4));
v___x_1177_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___closed__3));
v___x_1178_ = lean_alloc_closure((void*)(l_Lean_Elab_Rewrites_evalExact___boxed), 10, 0);
v___x_1179_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1175_, v___x_1176_, v___x_1177_, v___x_1178_);
return v___x_1179_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___boxed(lean_object* v_a_1180_){
_start:
{
lean_object* v_res_1181_; 
v_res_1181_ = l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1();
return v_res_1181_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3(){
_start:
{
lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; 
v___x_1208_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___closed__3));
v___x_1209_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__6));
v___x_1210_ = l_Lean_addBuiltinDeclarationRanges(v___x_1208_, v___x_1209_);
return v___x_1210_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___boxed(lean_object* v_a_1211_){
_start:
{
lean_object* v_res_1212_; 
v_res_1212_ = l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3();
return v_res_1212_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Location(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Replace(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Rewrites(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Rewrites(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Tactic_Location(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Replace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Rewrites(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Rewrites(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
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
res = runtime_initialize_Lean_Elab_Tactic_Rewrites(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Rewrites(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Rewrites(builtin);
}
#ifdef __cplusplus
}
#endif
