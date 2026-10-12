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
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__1___redArg(){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__1___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__1___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__1___redArg___closed__0);
v___x_6_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_7_;
v_res_7_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__1___redArg();
stack->m_obj
 = v_res_7_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__1___redArg___boxed(lean_object* v___y_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__1___redArg();
return v_res_9_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__1(lean_object* v_00_u03b1_10_, lean_object* v___y_11_, lean_object* v___y_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__1___redArg();
return v___x_20_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_11_ = stack[1].m_obj;
lean_object* v___y_12_ = stack[2].m_obj;
lean_object* v___y_13_ = stack[3].m_obj;
lean_object* v___y_14_ = stack[4].m_obj;
lean_object* v___y_15_ = stack[5].m_obj;
lean_object* v___y_16_ = stack[6].m_obj;
lean_object* v___y_17_ = stack[7].m_obj;
lean_object* v___y_18_ = stack[8].m_obj;
lean_object* v_res_21_;
v_res_21_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__1(lean_box(0), v___y_11_, v___y_12_, v___y_13_, v___y_14_, v___y_15_, v___y_16_, v___y_17_, v___y_18_);
stack->m_obj
 = v_res_21_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__1___boxed(lean_object* v_00_u03b1_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_, lean_object* v___y_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__1(v_00_u03b1_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_, v___y_27_, v___y_28_, v___y_29_, v___y_30_);
lean_dec(v___y_30_);
lean_dec_ref(v___y_29_);
lean_dec(v___y_28_);
lean_dec_ref(v___y_27_);
lean_dec(v___y_26_);
lean_dec_ref(v___y_25_);
lean_dec(v___y_24_);
lean_dec_ref(v___y_23_);
return v_res_32_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Rewrites_evalExact_spec__2___redArg(lean_object* v_e_33_, lean_object* v___y_34_){
_start:
{
uint8_t v___x_36_; 
v___x_36_ = l_Lean_Expr_hasMVar(v_e_33_);
if (v___x_36_ == 0)
{
lean_object* v___x_37_; 
v___x_37_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_37_, 0, v_e_33_);
return v___x_37_;
}
else
{
lean_object* v___x_38_; lean_object* v_mctx_39_; lean_object* v___x_40_; lean_object* v_fst_41_; lean_object* v_snd_42_; lean_object* v___x_43_; lean_object* v_cache_44_; lean_object* v_zetaDeltaFVarIds_45_; lean_object* v_postponed_46_; lean_object* v_diag_47_; lean_object* v___x_49_; uint8_t v_isShared_50_; uint8_t v_isSharedCheck_56_; 
v___x_38_ = lean_st_ref_get(v___y_34_);
v_mctx_39_ = lean_ctor_get(v___x_38_, 0);
lean_inc_ref(v_mctx_39_);
lean_dec(v___x_38_);
v___x_40_ = l_Lean_instantiateMVarsCore(v_mctx_39_, v_e_33_);
v_fst_41_ = lean_ctor_get(v___x_40_, 0);
lean_inc(v_fst_41_);
v_snd_42_ = lean_ctor_get(v___x_40_, 1);
lean_inc(v_snd_42_);
lean_dec_ref(v___x_40_);
v___x_43_ = lean_st_ref_take(v___y_34_);
v_cache_44_ = lean_ctor_get(v___x_43_, 1);
v_zetaDeltaFVarIds_45_ = lean_ctor_get(v___x_43_, 2);
v_postponed_46_ = lean_ctor_get(v___x_43_, 3);
v_diag_47_ = lean_ctor_get(v___x_43_, 4);
v_isSharedCheck_56_ = !lean_is_exclusive(v___x_43_);
if (v_isSharedCheck_56_ == 0)
{
lean_object* v_unused_57_; 
v_unused_57_ = lean_ctor_get(v___x_43_, 0);
lean_dec(v_unused_57_);
v___x_49_ = v___x_43_;
v_isShared_50_ = v_isSharedCheck_56_;
goto v_resetjp_48_;
}
else
{
lean_inc(v_diag_47_);
lean_inc(v_postponed_46_);
lean_inc(v_zetaDeltaFVarIds_45_);
lean_inc(v_cache_44_);
lean_dec(v___x_43_);
v___x_49_ = lean_box(0);
v_isShared_50_ = v_isSharedCheck_56_;
goto v_resetjp_48_;
}
v_resetjp_48_:
{
lean_object* v___x_52_; 
if (v_isShared_50_ == 0)
{
lean_ctor_set(v___x_49_, 0, v_snd_42_);
v___x_52_ = v___x_49_;
goto v_reusejp_51_;
}
else
{
lean_object* v_reuseFailAlloc_55_; 
v_reuseFailAlloc_55_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_55_, 0, v_snd_42_);
lean_ctor_set(v_reuseFailAlloc_55_, 1, v_cache_44_);
lean_ctor_set(v_reuseFailAlloc_55_, 2, v_zetaDeltaFVarIds_45_);
lean_ctor_set(v_reuseFailAlloc_55_, 3, v_postponed_46_);
lean_ctor_set(v_reuseFailAlloc_55_, 4, v_diag_47_);
v___x_52_ = v_reuseFailAlloc_55_;
goto v_reusejp_51_;
}
v_reusejp_51_:
{
lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_53_ = lean_st_ref_put(v___y_34_, v___x_52_);
v___x_54_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_54_, 0, v_fst_41_);
return v___x_54_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Elab_Rewrites_evalExact_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_33_ = stack[0].m_obj;
lean_object* v___y_34_ = stack[1].m_obj;
lean_object* v_res_58_;
v_res_58_ = l_Lean_instantiateMVars___at___00Lean_Elab_Rewrites_evalExact_spec__2___redArg(v_e_33_, v___y_34_);
stack->m_obj
 = v_res_58_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Rewrites_evalExact_spec__2___redArg___boxed(lean_object* v_e_59_, lean_object* v___y_60_, lean_object* v___y_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l_Lean_instantiateMVars___at___00Lean_Elab_Rewrites_evalExact_spec__2___redArg(v_e_59_, v___y_60_);
lean_dec(v___y_60_);
return v_res_62_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Rewrites_evalExact_spec__2(lean_object* v_e_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = l_Lean_instantiateMVars___at___00Lean_Elab_Rewrites_evalExact_spec__2___redArg(v_e_63_, v___y_69_);
return v___x_73_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Elab_Rewrites_evalExact_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_63_ = stack[0].m_obj;
lean_object* v___y_64_ = stack[1].m_obj;
lean_object* v___y_65_ = stack[2].m_obj;
lean_object* v___y_66_ = stack[3].m_obj;
lean_object* v___y_67_ = stack[4].m_obj;
lean_object* v___y_68_ = stack[5].m_obj;
lean_object* v___y_69_ = stack[6].m_obj;
lean_object* v___y_70_ = stack[7].m_obj;
lean_object* v___y_71_ = stack[8].m_obj;
lean_object* v_res_74_;
v_res_74_ = l_Lean_instantiateMVars___at___00Lean_Elab_Rewrites_evalExact_spec__2(v_e_63_, v___y_64_, v___y_65_, v___y_66_, v___y_67_, v___y_68_, v___y_69_, v___y_70_, v___y_71_);
stack->m_obj
 = v_res_74_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Rewrites_evalExact_spec__2___boxed(lean_object* v_e_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = l_Lean_instantiateMVars___at___00Lean_Elab_Rewrites_evalExact_spec__2(v_e_75_, v___y_76_, v___y_77_, v___y_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_);
lean_dec(v___y_83_);
lean_dec_ref(v___y_82_);
lean_dec(v___y_81_);
lean_dec_ref(v___y_80_);
lean_dec(v___y_79_);
lean_dec_ref(v___y_78_);
lean_dec(v___y_77_);
lean_dec_ref(v___y_76_);
return v_res_85_;
}
}
lean_object* l_Lean_Meta_withMCtx___at___00Lean_Elab_Rewrites_evalExact_spec__4___redArg___lam__0(lean_object* v_x_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_){
_start:
{
lean_object* v___x_96_; 
lean_inc(v___y_90_);
lean_inc_ref(v___y_89_);
lean_inc(v___y_88_);
lean_inc_ref(v___y_87_);
v___x_96_ = lean_apply_9(v_x_86_, v___y_87_, v___y_88_, v___y_89_, v___y_90_, v___y_91_, v___y_92_, v___y_93_, v___y_94_, lean_box(0));
return v___x_96_;
}
}
LEAN_EXPORT void l_Lean_Meta_withMCtx___at___00Lean_Elab_Rewrites_evalExact_spec__4___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_86_ = stack[0].m_obj;
lean_object* v___y_87_ = stack[1].m_obj;
lean_object* v___y_88_ = stack[2].m_obj;
lean_object* v___y_89_ = stack[3].m_obj;
lean_object* v___y_90_ = stack[4].m_obj;
lean_object* v___y_91_ = stack[5].m_obj;
lean_object* v___y_92_ = stack[6].m_obj;
lean_object* v___y_93_ = stack[7].m_obj;
lean_object* v___y_94_ = stack[8].m_obj;
lean_object* v_res_97_;
v_res_97_ = l_Lean_Meta_withMCtx___at___00Lean_Elab_Rewrites_evalExact_spec__4___redArg___lam__0(v_x_86_, v___y_87_, v___y_88_, v___y_89_, v___y_90_, v___y_91_, v___y_92_, v___y_93_, v___y_94_);
stack->m_obj
 = v_res_97_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Elab_Rewrites_evalExact_spec__4___redArg___lam__0___boxed(lean_object* v_x_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l_Lean_Meta_withMCtx___at___00Lean_Elab_Rewrites_evalExact_spec__4___redArg___lam__0(v_x_98_, v___y_99_, v___y_100_, v___y_101_, v___y_102_, v___y_103_, v___y_104_, v___y_105_, v___y_106_);
lean_dec(v___y_102_);
lean_dec_ref(v___y_101_);
lean_dec(v___y_100_);
lean_dec_ref(v___y_99_);
return v_res_108_;
}
}
lean_object* l_Lean_Meta_withMCtx___at___00Lean_Elab_Rewrites_evalExact_spec__4___redArg(lean_object* v_mctx_109_, lean_object* v_x_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_){
_start:
{
lean_object* v___f_120_; lean_object* v___x_121_; 
lean_inc(v___y_114_);
lean_inc_ref(v___y_113_);
lean_inc(v___y_112_);
lean_inc_ref(v___y_111_);
v___f_120_ = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at___00Lean_Elab_Rewrites_evalExact_spec__4___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_120_, 0, v_x_110_);
lean_closure_set(v___f_120_, 1, v___y_111_);
lean_closure_set(v___f_120_, 2, v___y_112_);
lean_closure_set(v___f_120_, 3, v___y_113_);
lean_closure_set(v___f_120_, 4, v___y_114_);
v___x_121_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMCtxImp(lean_box(0), v_mctx_109_, v___f_120_, v___y_115_, v___y_116_, v___y_117_, v___y_118_);
if (lean_obj_tag(v___x_121_) == 0)
{
return v___x_121_;
}
else
{
lean_object* v_a_122_; lean_object* v___x_124_; uint8_t v_isShared_125_; uint8_t v_isSharedCheck_129_; 
v_a_122_ = lean_ctor_get(v___x_121_, 0);
v_isSharedCheck_129_ = !lean_is_exclusive(v___x_121_);
if (v_isSharedCheck_129_ == 0)
{
v___x_124_ = v___x_121_;
v_isShared_125_ = v_isSharedCheck_129_;
goto v_resetjp_123_;
}
else
{
lean_inc(v_a_122_);
lean_dec(v___x_121_);
v___x_124_ = lean_box(0);
v_isShared_125_ = v_isSharedCheck_129_;
goto v_resetjp_123_;
}
v_resetjp_123_:
{
lean_object* v___x_127_; 
if (v_isShared_125_ == 0)
{
v___x_127_ = v___x_124_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v_a_122_);
v___x_127_ = v_reuseFailAlloc_128_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
return v___x_127_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withMCtx___at___00Lean_Elab_Rewrites_evalExact_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mctx_109_ = stack[0].m_obj;
lean_object* v_x_110_ = stack[1].m_obj;
lean_object* v___y_111_ = stack[2].m_obj;
lean_object* v___y_112_ = stack[3].m_obj;
lean_object* v___y_113_ = stack[4].m_obj;
lean_object* v___y_114_ = stack[5].m_obj;
lean_object* v___y_115_ = stack[6].m_obj;
lean_object* v___y_116_ = stack[7].m_obj;
lean_object* v___y_117_ = stack[8].m_obj;
lean_object* v___y_118_ = stack[9].m_obj;
lean_object* v_res_130_;
v_res_130_ = l_Lean_Meta_withMCtx___at___00Lean_Elab_Rewrites_evalExact_spec__4___redArg(v_mctx_109_, v_x_110_, v___y_111_, v___y_112_, v___y_113_, v___y_114_, v___y_115_, v___y_116_, v___y_117_, v___y_118_);
stack->m_obj
 = v_res_130_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Elab_Rewrites_evalExact_spec__4___redArg___boxed(lean_object* v_mctx_131_, lean_object* v_x_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = l_Lean_Meta_withMCtx___at___00Lean_Elab_Rewrites_evalExact_spec__4___redArg(v_mctx_131_, v_x_132_, v___y_133_, v___y_134_, v___y_135_, v___y_136_, v___y_137_, v___y_138_, v___y_139_, v___y_140_);
lean_dec(v___y_140_);
lean_dec_ref(v___y_139_);
lean_dec(v___y_138_);
lean_dec_ref(v___y_137_);
lean_dec(v___y_136_);
lean_dec_ref(v___y_135_);
lean_dec(v___y_134_);
lean_dec_ref(v___y_133_);
return v_res_142_;
}
}
lean_object* l_Lean_Meta_withMCtx___at___00Lean_Elab_Rewrites_evalExact_spec__4(lean_object* v_00_u03b1_143_, lean_object* v_mctx_144_, lean_object* v_x_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_){
_start:
{
lean_object* v___x_155_; 
v___x_155_ = l_Lean_Meta_withMCtx___at___00Lean_Elab_Rewrites_evalExact_spec__4___redArg(v_mctx_144_, v_x_145_, v___y_146_, v___y_147_, v___y_148_, v___y_149_, v___y_150_, v___y_151_, v___y_152_, v___y_153_);
return v___x_155_;
}
}
LEAN_EXPORT void l_Lean_Meta_withMCtx___at___00Lean_Elab_Rewrites_evalExact_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_mctx_144_ = stack[1].m_obj;
lean_object* v_x_145_ = stack[2].m_obj;
lean_object* v___y_146_ = stack[3].m_obj;
lean_object* v___y_147_ = stack[4].m_obj;
lean_object* v___y_148_ = stack[5].m_obj;
lean_object* v___y_149_ = stack[6].m_obj;
lean_object* v___y_150_ = stack[7].m_obj;
lean_object* v___y_151_ = stack[8].m_obj;
lean_object* v___y_152_ = stack[9].m_obj;
lean_object* v___y_153_ = stack[10].m_obj;
lean_object* v_res_156_;
v_res_156_ = l_Lean_Meta_withMCtx___at___00Lean_Elab_Rewrites_evalExact_spec__4(lean_box(0), v_mctx_144_, v_x_145_, v___y_146_, v___y_147_, v___y_148_, v___y_149_, v___y_150_, v___y_151_, v___y_152_, v___y_153_);
stack->m_obj
 = v_res_156_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Elab_Rewrites_evalExact_spec__4___boxed(lean_object* v_00_u03b1_157_, lean_object* v_mctx_158_, lean_object* v_x_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l_Lean_Meta_withMCtx___at___00Lean_Elab_Rewrites_evalExact_spec__4(v_00_u03b1_157_, v_mctx_158_, v_x_159_, v___y_160_, v___y_161_, v___y_162_, v___y_163_, v___y_164_, v___y_165_, v___y_166_, v___y_167_);
lean_dec(v___y_167_);
lean_dec_ref(v___y_166_);
lean_dec(v___y_165_);
lean_dec_ref(v___y_164_);
lean_dec(v___y_163_);
lean_dec_ref(v___y_162_);
lean_dec(v___y_161_);
lean_dec_ref(v___y_160_);
return v_res_169_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Rewrites_evalExact_spec__6___redArg(lean_object* v_mvarId_170_, lean_object* v_x_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_){
_start:
{
lean_object* v___x_177_; 
v___x_177_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_170_, v_x_171_, v___y_172_, v___y_173_, v___y_174_, v___y_175_);
if (lean_obj_tag(v___x_177_) == 0)
{
lean_object* v_a_178_; lean_object* v___x_180_; uint8_t v_isShared_181_; uint8_t v_isSharedCheck_185_; 
v_a_178_ = lean_ctor_get(v___x_177_, 0);
v_isSharedCheck_185_ = !lean_is_exclusive(v___x_177_);
if (v_isSharedCheck_185_ == 0)
{
v___x_180_ = v___x_177_;
v_isShared_181_ = v_isSharedCheck_185_;
goto v_resetjp_179_;
}
else
{
lean_inc(v_a_178_);
lean_dec(v___x_177_);
v___x_180_ = lean_box(0);
v_isShared_181_ = v_isSharedCheck_185_;
goto v_resetjp_179_;
}
v_resetjp_179_:
{
lean_object* v___x_183_; 
if (v_isShared_181_ == 0)
{
v___x_183_ = v___x_180_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v_a_178_);
v___x_183_ = v_reuseFailAlloc_184_;
goto v_reusejp_182_;
}
v_reusejp_182_:
{
return v___x_183_;
}
}
}
else
{
lean_object* v_a_186_; lean_object* v___x_188_; uint8_t v_isShared_189_; uint8_t v_isSharedCheck_193_; 
v_a_186_ = lean_ctor_get(v___x_177_, 0);
v_isSharedCheck_193_ = !lean_is_exclusive(v___x_177_);
if (v_isSharedCheck_193_ == 0)
{
v___x_188_ = v___x_177_;
v_isShared_189_ = v_isSharedCheck_193_;
goto v_resetjp_187_;
}
else
{
lean_inc(v_a_186_);
lean_dec(v___x_177_);
v___x_188_ = lean_box(0);
v_isShared_189_ = v_isSharedCheck_193_;
goto v_resetjp_187_;
}
v_resetjp_187_:
{
lean_object* v___x_191_; 
if (v_isShared_189_ == 0)
{
v___x_191_ = v___x_188_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v_a_186_);
v___x_191_ = v_reuseFailAlloc_192_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
return v___x_191_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Elab_Rewrites_evalExact_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_170_ = stack[0].m_obj;
lean_object* v_x_171_ = stack[1].m_obj;
lean_object* v___y_172_ = stack[2].m_obj;
lean_object* v___y_173_ = stack[3].m_obj;
lean_object* v___y_174_ = stack[4].m_obj;
lean_object* v___y_175_ = stack[5].m_obj;
lean_object* v_res_194_;
v_res_194_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Rewrites_evalExact_spec__6___redArg(v_mvarId_170_, v_x_171_, v___y_172_, v___y_173_, v___y_174_, v___y_175_);
stack->m_obj
 = v_res_194_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Rewrites_evalExact_spec__6___redArg___boxed(lean_object* v_mvarId_195_, lean_object* v_x_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Rewrites_evalExact_spec__6___redArg(v_mvarId_195_, v_x_196_, v___y_197_, v___y_198_, v___y_199_, v___y_200_);
lean_dec(v___y_200_);
lean_dec_ref(v___y_199_);
lean_dec(v___y_198_);
lean_dec_ref(v___y_197_);
return v_res_202_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Rewrites_evalExact_spec__6(lean_object* v_00_u03b1_203_, lean_object* v_mvarId_204_, lean_object* v_x_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_){
_start:
{
lean_object* v___x_211_; 
v___x_211_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Rewrites_evalExact_spec__6___redArg(v_mvarId_204_, v_x_205_, v___y_206_, v___y_207_, v___y_208_, v___y_209_);
return v___x_211_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Elab_Rewrites_evalExact_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_204_ = stack[1].m_obj;
lean_object* v_x_205_ = stack[2].m_obj;
lean_object* v___y_206_ = stack[3].m_obj;
lean_object* v___y_207_ = stack[4].m_obj;
lean_object* v___y_208_ = stack[5].m_obj;
lean_object* v___y_209_ = stack[6].m_obj;
lean_object* v_res_212_;
v_res_212_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Rewrites_evalExact_spec__6(lean_box(0), v_mvarId_204_, v_x_205_, v___y_206_, v___y_207_, v___y_208_, v___y_209_);
stack->m_obj
 = v_res_212_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Rewrites_evalExact_spec__6___boxed(lean_object* v_00_u03b1_213_, lean_object* v_mvarId_214_, lean_object* v_x_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Rewrites_evalExact_spec__6(v_00_u03b1_213_, v_mvarId_214_, v_x_215_, v___y_216_, v___y_217_, v___y_218_, v___y_219_);
lean_dec(v___y_219_);
lean_dec_ref(v___y_218_);
lean_dec(v___y_217_);
lean_dec_ref(v___y_216_);
return v_res_221_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__0_spec__0(lean_object* v_msgData_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_){
_start:
{
lean_object* v___x_228_; lean_object* v_env_229_; uint8_t v___x_230_; lean_object* v_env_231_; lean_object* v___x_232_; lean_object* v_toCold_233_; lean_object* v_mctx_234_; lean_object* v_lctx_235_; lean_object* v_options_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_228_ = lean_st_ref_get(v___y_226_);
v_env_229_ = lean_ctor_get(v___x_228_, 0);
lean_inc_ref(v_env_229_);
lean_dec(v___x_228_);
v___x_230_ = 0;
v_env_231_ = l_Lean_Environment_setRecordingDeps(v_env_229_, v___x_230_);
v___x_232_ = lean_st_ref_get(v___y_224_);
v_toCold_233_ = lean_ctor_get(v___y_225_, 0);
v_mctx_234_ = lean_ctor_get(v___x_232_, 0);
lean_inc_ref(v_mctx_234_);
lean_dec(v___x_232_);
v_lctx_235_ = lean_ctor_get(v___y_223_, 2);
v_options_236_ = lean_ctor_get(v_toCold_233_, 2);
lean_inc_ref(v_options_236_);
lean_inc_ref(v_lctx_235_);
v___x_237_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_237_, 0, v_env_231_);
lean_ctor_set(v___x_237_, 1, v_mctx_234_);
lean_ctor_set(v___x_237_, 2, v_lctx_235_);
lean_ctor_set(v___x_237_, 3, v_options_236_);
v___x_238_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_238_, 0, v___x_237_);
lean_ctor_set(v___x_238_, 1, v_msgData_222_);
v___x_239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_239_, 0, v___x_238_);
return v___x_239_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_222_ = stack[0].m_obj;
lean_object* v___y_223_ = stack[1].m_obj;
lean_object* v___y_224_ = stack[2].m_obj;
lean_object* v___y_225_ = stack[3].m_obj;
lean_object* v___y_226_ = stack[4].m_obj;
lean_object* v_res_240_;
v_res_240_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__0_spec__0(v_msgData_222_, v___y_223_, v___y_224_, v___y_225_, v___y_226_);
stack->m_obj
 = v_res_240_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__0_spec__0___boxed(lean_object* v_msgData_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__0_spec__0(v_msgData_241_, v___y_242_, v___y_243_, v___y_244_, v___y_245_);
lean_dec(v___y_245_);
lean_dec_ref(v___y_244_);
lean_dec(v___y_243_);
lean_dec_ref(v___y_242_);
return v_res_247_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__0___redArg(lean_object* v_msg_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_){
_start:
{
lean_object* v_ref_254_; lean_object* v___x_255_; lean_object* v_a_256_; lean_object* v___x_258_; uint8_t v_isShared_259_; uint8_t v_isSharedCheck_264_; 
v_ref_254_ = lean_ctor_get(v___y_251_, 2);
v___x_255_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__0_spec__0(v_msg_248_, v___y_249_, v___y_250_, v___y_251_, v___y_252_);
v_a_256_ = lean_ctor_get(v___x_255_, 0);
v_isSharedCheck_264_ = !lean_is_exclusive(v___x_255_);
if (v_isSharedCheck_264_ == 0)
{
v___x_258_ = v___x_255_;
v_isShared_259_ = v_isSharedCheck_264_;
goto v_resetjp_257_;
}
else
{
lean_inc(v_a_256_);
lean_dec(v___x_255_);
v___x_258_ = lean_box(0);
v_isShared_259_ = v_isSharedCheck_264_;
goto v_resetjp_257_;
}
v_resetjp_257_:
{
lean_object* v___x_260_; lean_object* v___x_262_; 
lean_inc(v_ref_254_);
v___x_260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_260_, 0, v_ref_254_);
lean_ctor_set(v___x_260_, 1, v_a_256_);
if (v_isShared_259_ == 0)
{
lean_ctor_set_tag(v___x_258_, 1);
lean_ctor_set(v___x_258_, 0, v___x_260_);
v___x_262_ = v___x_258_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v___x_260_);
v___x_262_ = v_reuseFailAlloc_263_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
return v___x_262_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_248_ = stack[0].m_obj;
lean_object* v___y_249_ = stack[1].m_obj;
lean_object* v___y_250_ = stack[2].m_obj;
lean_object* v___y_251_ = stack[3].m_obj;
lean_object* v___y_252_ = stack[4].m_obj;
lean_object* v_res_265_;
v_res_265_ = l_Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__0___redArg(v_msg_248_, v___y_249_, v___y_250_, v___y_251_, v___y_252_);
stack->m_obj
 = v_res_265_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__0___redArg___boxed(lean_object* v_msg_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l_Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__0___redArg(v_msg_266_, v___y_267_, v___y_268_, v___y_269_, v___y_270_);
lean_dec(v___y_270_);
lean_dec_ref(v___y_269_);
lean_dec(v___y_268_);
lean_dec_ref(v___y_267_);
return v_res_272_;
}
}
static lean_object* _init_l_Lean_Elab_Rewrites_evalExact___lam__0___closed__1(void){
_start:
{
lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_274_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___lam__0___closed__0));
v___x_275_ = l_Lean_stringToMessageData(v___x_274_);
return v___x_275_;
}
}
lean_object* l_Lean_Elab_Rewrites_evalExact___lam__0(lean_object* v_x_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_){
_start:
{
lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_286_ = lean_obj_once(&l_Lean_Elab_Rewrites_evalExact___lam__0___closed__1, &l_Lean_Elab_Rewrites_evalExact___lam__0___closed__1_once, _init_l_Lean_Elab_Rewrites_evalExact___lam__0___closed__1);
v___x_287_ = l_Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__0___redArg(v___x_286_, v___y_281_, v___y_282_, v___y_283_, v___y_284_);
return v___x_287_;
}
}
LEAN_EXPORT void l_Lean_Elab_Rewrites_evalExact___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_276_ = stack[0].m_obj;
lean_object* v___y_277_ = stack[1].m_obj;
lean_object* v___y_278_ = stack[2].m_obj;
lean_object* v___y_279_ = stack[3].m_obj;
lean_object* v___y_280_ = stack[4].m_obj;
lean_object* v___y_281_ = stack[5].m_obj;
lean_object* v___y_282_ = stack[6].m_obj;
lean_object* v___y_283_ = stack[7].m_obj;
lean_object* v___y_284_ = stack[8].m_obj;
lean_object* v_res_288_;
v_res_288_ = l_Lean_Elab_Rewrites_evalExact___lam__0(v_x_276_, v___y_277_, v___y_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_);
stack->m_obj
 = v_res_288_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact___lam__0___boxed(lean_object* v_x_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_){
_start:
{
lean_object* v_res_299_; 
v_res_299_ = l_Lean_Elab_Rewrites_evalExact___lam__0(v_x_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_, v___y_296_, v___y_297_);
lean_dec(v___y_297_);
lean_dec_ref(v___y_296_);
lean_dec(v___y_295_);
lean_dec_ref(v___y_294_);
lean_dec(v___y_293_);
lean_dec_ref(v___y_292_);
lean_dec(v___y_291_);
lean_dec_ref(v___y_290_);
lean_dec(v_x_289_);
return v_res_299_;
}
}
lean_object* l_Lean_Elab_Rewrites_evalExact___lam__1(lean_object* v_eqProof_300_, lean_object* v___x_301_, lean_object* v_eNew_302_, lean_object* v_a_303_, lean_object* v_f_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_){
_start:
{
lean_object* v___x_310_; 
v___x_310_ = l_Lean_Meta_mkEqMP(v_eqProof_300_, v___x_301_, v___y_305_, v___y_306_, v___y_307_, v___y_308_);
if (lean_obj_tag(v___x_310_) == 0)
{
lean_object* v_a_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v_a_311_ = lean_ctor_get(v___x_310_, 0);
lean_inc(v_a_311_);
lean_dec_ref_known(v___x_310_, 1);
v___x_312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_312_, 0, v_eNew_302_);
v___x_313_ = lean_box(0);
v___x_314_ = l_Lean_MVarId_replace(v_a_303_, v_f_304_, v_a_311_, v___x_312_, v___x_313_, v___y_305_, v___y_306_, v___y_307_, v___y_308_);
return v___x_314_;
}
else
{
lean_object* v_a_315_; lean_object* v___x_317_; uint8_t v_isShared_318_; uint8_t v_isSharedCheck_322_; 
lean_dec(v_f_304_);
lean_dec(v_a_303_);
lean_dec_ref(v_eNew_302_);
v_a_315_ = lean_ctor_get(v___x_310_, 0);
v_isSharedCheck_322_ = !lean_is_exclusive(v___x_310_);
if (v_isSharedCheck_322_ == 0)
{
v___x_317_ = v___x_310_;
v_isShared_318_ = v_isSharedCheck_322_;
goto v_resetjp_316_;
}
else
{
lean_inc(v_a_315_);
lean_dec(v___x_310_);
v___x_317_ = lean_box(0);
v_isShared_318_ = v_isSharedCheck_322_;
goto v_resetjp_316_;
}
v_resetjp_316_:
{
lean_object* v___x_320_; 
if (v_isShared_318_ == 0)
{
v___x_320_ = v___x_317_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v_a_315_);
v___x_320_ = v_reuseFailAlloc_321_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
return v___x_320_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Rewrites_evalExact___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_eqProof_300_ = stack[0].m_obj;
lean_object* v___x_301_ = stack[1].m_obj;
lean_object* v_eNew_302_ = stack[2].m_obj;
lean_object* v_a_303_ = stack[3].m_obj;
lean_object* v_f_304_ = stack[4].m_obj;
lean_object* v___y_305_ = stack[5].m_obj;
lean_object* v___y_306_ = stack[6].m_obj;
lean_object* v___y_307_ = stack[7].m_obj;
lean_object* v___y_308_ = stack[8].m_obj;
lean_object* v_res_323_;
v_res_323_ = l_Lean_Elab_Rewrites_evalExact___lam__1(v_eqProof_300_, v___x_301_, v_eNew_302_, v_a_303_, v_f_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_);
stack->m_obj
 = v_res_323_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact___lam__1___boxed(lean_object* v_eqProof_324_, lean_object* v___x_325_, lean_object* v_eNew_326_, lean_object* v_a_327_, lean_object* v_f_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l_Lean_Elab_Rewrites_evalExact___lam__1(v_eqProof_324_, v___x_325_, v_eNew_326_, v_a_327_, v_f_328_, v___y_329_, v___y_330_, v___y_331_, v___y_332_);
lean_dec(v___y_332_);
lean_dec_ref(v___y_331_);
lean_dec(v___y_330_);
lean_dec_ref(v___y_329_);
return v_res_334_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__5___redArg___lam__0(lean_object* v_result_335_, lean_object* v_expr_336_, uint8_t v_symm_337_, lean_object* v_f_338_, lean_object* v_tk_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_){
_start:
{
lean_object* v_ref_349_; lean_object* v___x_350_; 
v_ref_349_ = lean_ctor_get(v___y_346_, 2);
v___x_350_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_341_, v___y_343_, v___y_345_, v___y_347_);
if (lean_obj_tag(v___x_350_) == 0)
{
lean_object* v_a_351_; lean_object* v_eNew_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
v_a_351_ = lean_ctor_get(v___x_350_, 0);
lean_inc(v_a_351_);
lean_dec_ref_known(v___x_350_, 1);
v_eNew_352_ = lean_ctor_get(v_result_335_, 0);
v___x_353_ = lean_box(v_symm_337_);
v___x_354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_354_, 0, v_expr_336_);
lean_ctor_set(v___x_354_, 1, v___x_353_);
v___x_355_ = lean_box(0);
v___x_356_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_356_, 0, v___x_354_);
lean_ctor_set(v___x_356_, 1, v___x_355_);
lean_inc_ref(v_eNew_352_);
v___x_357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_357_, 0, v_eNew_352_);
v___x_358_ = l_Lean_Expr_fvar___override(v_f_338_);
v___x_359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_359_, 0, v___x_358_);
lean_inc(v_ref_349_);
v___x_360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_360_, 0, v_ref_349_);
v___x_361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_361_, 0, v_a_351_);
v___x_362_ = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion(v_tk_339_, v___x_356_, v___x_357_, v___x_359_, v___x_360_, v___x_361_, v___y_340_, v___y_341_, v___y_342_, v___y_343_, v___y_344_, v___y_345_, v___y_346_, v___y_347_);
return v___x_362_;
}
else
{
lean_object* v_a_363_; lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_370_; 
lean_dec(v_tk_339_);
lean_dec(v_f_338_);
lean_dec_ref(v_expr_336_);
v_a_363_ = lean_ctor_get(v___x_350_, 0);
v_isSharedCheck_370_ = !lean_is_exclusive(v___x_350_);
if (v_isSharedCheck_370_ == 0)
{
v___x_365_ = v___x_350_;
v_isShared_366_ = v_isSharedCheck_370_;
goto v_resetjp_364_;
}
else
{
lean_inc(v_a_363_);
lean_dec(v___x_350_);
v___x_365_ = lean_box(0);
v_isShared_366_ = v_isSharedCheck_370_;
goto v_resetjp_364_;
}
v_resetjp_364_:
{
lean_object* v___x_368_; 
if (v_isShared_366_ == 0)
{
v___x_368_ = v___x_365_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v_a_363_);
v___x_368_ = v_reuseFailAlloc_369_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
return v___x_368_;
}
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__5___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_result_335_ = stack[0].m_obj;
lean_object* v_expr_336_ = stack[1].m_obj;
uint8_t v_symm_337_ = stack[2].m_num;
lean_object* v_f_338_ = stack[3].m_obj;
lean_object* v_tk_339_ = stack[4].m_obj;
lean_object* v___y_340_ = stack[5].m_obj;
lean_object* v___y_341_ = stack[6].m_obj;
lean_object* v___y_342_ = stack[7].m_obj;
lean_object* v___y_343_ = stack[8].m_obj;
lean_object* v___y_344_ = stack[9].m_obj;
lean_object* v___y_345_ = stack[10].m_obj;
lean_object* v___y_346_ = stack[11].m_obj;
lean_object* v___y_347_ = stack[12].m_obj;
lean_object* v_res_371_;
v_res_371_ = l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__5___redArg___lam__0(v_result_335_, v_expr_336_, v_symm_337_, v_f_338_, v_tk_339_, v___y_340_, v___y_341_, v___y_342_, v___y_343_, v___y_344_, v___y_345_, v___y_346_, v___y_347_);
stack->m_obj
 = v_res_371_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__5___redArg___lam__0___boxed(lean_object* v_result_372_, lean_object* v_expr_373_, lean_object* v_symm_374_, lean_object* v_f_375_, lean_object* v_tk_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_){
_start:
{
uint8_t v_symm_boxed_386_; lean_object* v_res_387_; 
v_symm_boxed_386_ = lean_unbox(v_symm_374_);
v_res_387_ = l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__5___redArg___lam__0(v_result_372_, v_expr_373_, v_symm_boxed_386_, v_f_375_, v_tk_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_);
lean_dec(v___y_384_);
lean_dec_ref(v___y_383_);
lean_dec(v___y_382_);
lean_dec_ref(v___y_381_);
lean_dec(v___y_380_);
lean_dec_ref(v___y_379_);
lean_dec(v___y_378_);
lean_dec_ref(v___y_377_);
lean_dec_ref(v_result_372_);
return v_res_387_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__5___redArg(lean_object* v_f_388_, lean_object* v_tk_389_, lean_object* v_as_x27_390_, lean_object* v_b_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_){
_start:
{
if (lean_obj_tag(v_as_x27_390_) == 0)
{
lean_object* v___x_401_; 
lean_dec(v_tk_389_);
lean_dec(v_f_388_);
v___x_401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_401_, 0, v_b_391_);
return v___x_401_;
}
else
{
lean_object* v_head_402_; lean_object* v_tail_403_; lean_object* v_expr_404_; uint8_t v_symm_405_; lean_object* v_result_406_; lean_object* v_mctx_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___f_410_; lean_object* v___x_411_; 
v_head_402_ = lean_ctor_get(v_as_x27_390_, 0);
v_tail_403_ = lean_ctor_get(v_as_x27_390_, 1);
v_expr_404_ = lean_ctor_get(v_head_402_, 0);
v_symm_405_ = lean_ctor_get_uint8(v_head_402_, sizeof(void*)*4);
v_result_406_ = lean_ctor_get(v_head_402_, 2);
v_mctx_407_ = lean_ctor_get(v_head_402_, 3);
v___x_408_ = lean_box(0);
v___x_409_ = lean_box(v_symm_405_);
lean_inc(v_tk_389_);
lean_inc(v_f_388_);
lean_inc_ref(v_expr_404_);
lean_inc_ref(v_result_406_);
v___f_410_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__5___redArg___lam__0___boxed), 14, 5);
lean_closure_set(v___f_410_, 0, v_result_406_);
lean_closure_set(v___f_410_, 1, v_expr_404_);
lean_closure_set(v___f_410_, 2, v___x_409_);
lean_closure_set(v___f_410_, 3, v_f_388_);
lean_closure_set(v___f_410_, 4, v_tk_389_);
lean_inc_ref(v_mctx_407_);
v___x_411_ = l_Lean_Meta_withMCtx___at___00Lean_Elab_Rewrites_evalExact_spec__4___redArg(v_mctx_407_, v___f_410_, v___y_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_);
if (lean_obj_tag(v___x_411_) == 0)
{
lean_dec_ref_known(v___x_411_, 1);
v_as_x27_390_ = v_tail_403_;
v_b_391_ = v___x_408_;
goto _start;
}
else
{
lean_dec(v_tk_389_);
lean_dec(v_f_388_);
return v___x_411_;
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_388_ = stack[0].m_obj;
lean_object* v_tk_389_ = stack[1].m_obj;
lean_object* v_as_x27_390_ = stack[2].m_obj;
lean_object* v_b_391_ = stack[3].m_obj;
lean_object* v___y_392_ = stack[4].m_obj;
lean_object* v___y_393_ = stack[5].m_obj;
lean_object* v___y_394_ = stack[6].m_obj;
lean_object* v___y_395_ = stack[7].m_obj;
lean_object* v___y_396_ = stack[8].m_obj;
lean_object* v___y_397_ = stack[9].m_obj;
lean_object* v___y_398_ = stack[10].m_obj;
lean_object* v___y_399_ = stack[11].m_obj;
lean_object* v_res_413_;
v_res_413_ = l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__5___redArg(v_f_388_, v_tk_389_, v_as_x27_390_, v_b_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_);
stack->m_obj
 = v_res_413_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__5___redArg___boxed(lean_object* v_f_414_, lean_object* v_tk_415_, lean_object* v_as_x27_416_, lean_object* v_b_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__5___redArg(v_f_414_, v_tk_415_, v_as_x27_416_, v_b_417_, v___y_418_, v___y_419_, v___y_420_, v___y_421_, v___y_422_, v___y_423_, v___y_424_, v___y_425_);
lean_dec(v___y_425_);
lean_dec_ref(v___y_424_);
lean_dec(v___y_423_);
lean_dec_ref(v___y_422_);
lean_dec(v___y_421_);
lean_dec_ref(v___y_420_);
lean_dec(v___y_419_);
lean_dec_ref(v___y_418_);
lean_dec(v_as_x27_416_);
return v_res_427_;
}
}
static lean_object* _init_l_Lean_Elab_Rewrites_evalExact___lam__2___closed__3(void){
_start:
{
lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_432_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___lam__2___closed__2));
v___x_433_ = l_Lean_stringToMessageData(v___x_432_);
return v___x_433_;
}
}
lean_object* l_Lean_Elab_Rewrites_evalExact___lam__2(lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v___y_436_, lean_object* v_tk_437_, lean_object* v___x_438_, lean_object* v___x_439_, lean_object* v_f_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_){
_start:
{
lean_object* v___x_450_; 
lean_inc(v_f_440_);
v___x_450_ = l_Lean_FVarId_findDecl_x3f___redArg(v_f_440_, v___y_445_);
if (lean_obj_tag(v___x_450_) == 0)
{
lean_object* v_a_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_574_; 
v_a_451_ = lean_ctor_get(v___x_450_, 0);
v_isSharedCheck_574_ = !lean_is_exclusive(v___x_450_);
if (v_isSharedCheck_574_ == 0)
{
v___x_453_ = v___x_450_;
v_isShared_454_ = v_isSharedCheck_574_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_a_451_);
lean_dec(v___x_450_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_574_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
if (lean_obj_tag(v_a_451_) == 1)
{
lean_object* v_val_455_; uint8_t v___x_456_; 
v_val_455_ = lean_ctor_get(v_a_451_, 0);
lean_inc(v_val_455_);
lean_dec_ref_known(v_a_451_, 1);
v___x_456_ = l_Lean_LocalDecl_isImplementationDetail(v_val_455_);
lean_dec(v_val_455_);
if (v___x_456_ == 0)
{
lean_object* v___x_457_; 
lean_del_object(v___x_453_);
lean_inc(v_f_440_);
v___x_457_ = l_Lean_FVarId_getType___redArg(v_f_440_, v___y_445_, v___y_447_, v___y_448_);
if (lean_obj_tag(v___x_457_) == 0)
{
lean_object* v_a_458_; lean_object* v___x_459_; lean_object* v_a_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; 
v_a_458_ = lean_ctor_get(v___x_457_, 0);
lean_inc(v_a_458_);
lean_dec_ref_known(v___x_457_, 1);
v___x_459_ = l_Lean_instantiateMVars___at___00Lean_Elab_Rewrites_evalExact_spec__2___redArg(v_a_458_, v___y_446_);
v_a_460_ = lean_ctor_get(v___x_459_, 0);
lean_inc(v_a_460_);
lean_dec_ref(v___x_459_);
v___x_461_ = lean_box(0);
lean_inc(v_f_440_);
v___x_462_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_462_, 0, v_f_440_);
lean_ctor_set(v___x_462_, 1, v___x_461_);
v___x_463_ = l_Lean_Meta_Rewrites_localHypotheses(v___x_462_, v___y_445_, v___y_446_, v___y_447_, v___y_448_);
lean_dec_ref_known(v___x_462_, 2);
if (lean_obj_tag(v___x_463_) == 0)
{
lean_object* v_a_464_; uint8_t v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
v_a_464_ = lean_ctor_get(v___x_463_, 0);
lean_inc(v_a_464_);
lean_dec_ref_known(v___x_463_, 1);
v___x_465_ = 2;
v___x_466_ = lean_unsigned_to_nat(20u);
v___x_467_ = lean_unsigned_to_nat(10u);
lean_inc(v_a_435_);
v___x_468_ = l_Lean_Meta_Rewrites_findRewrites(v_a_464_, v_a_434_, v_a_435_, v_a_460_, v___y_436_, v___x_465_, v___x_456_, v___x_466_, v___x_467_, v___y_445_, v___y_446_, v___y_447_, v___y_448_);
if (lean_obj_tag(v___x_468_) == 0)
{
lean_object* v_a_469_; lean_object* v___y_471_; lean_object* v___y_472_; lean_object* v___y_473_; lean_object* v___y_474_; lean_object* v___y_475_; lean_object* v___y_476_; lean_object* v___y_477_; lean_object* v___y_478_; lean_object* v___x_525_; lean_object* v___x_526_; 
v_a_469_ = lean_ctor_get(v___x_468_, 0);
lean_inc(v_a_469_);
lean_dec_ref_known(v___x_468_, 1);
v___x_525_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___lam__2___closed__1));
v___x_526_ = l_Lean_reportOutOfHeartbeats(v___x_525_, v_tk_437_, v___x_439_, v___y_447_, v___y_448_);
if (lean_obj_tag(v___x_526_) == 0)
{
uint8_t v___x_527_; 
lean_dec_ref_known(v___x_526_, 1);
v___x_527_ = l_List_isEmpty___redArg(v_a_469_);
if (v___x_527_ == 0)
{
v___y_471_ = v___y_441_;
v___y_472_ = v___y_442_;
v___y_473_ = v___y_443_;
v___y_474_ = v___y_444_;
v___y_475_ = v___y_445_;
v___y_476_ = v___y_446_;
v___y_477_ = v___y_447_;
v___y_478_ = v___y_448_;
goto v___jp_470_;
}
else
{
lean_object* v___x_528_; 
lean_dec(v_a_469_);
lean_dec(v___x_438_);
lean_dec(v_tk_437_);
lean_dec(v_a_435_);
v___x_528_ = l_Lean_FVarId_getUserName___redArg(v_f_440_, v___y_445_, v___y_447_, v___y_448_);
if (lean_obj_tag(v___x_528_) == 0)
{
lean_object* v_a_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; 
v_a_529_ = lean_ctor_get(v___x_528_, 0);
lean_inc(v_a_529_);
lean_dec_ref_known(v___x_528_, 1);
v___x_530_ = lean_obj_once(&l_Lean_Elab_Rewrites_evalExact___lam__2___closed__3, &l_Lean_Elab_Rewrites_evalExact___lam__2___closed__3_once, _init_l_Lean_Elab_Rewrites_evalExact___lam__2___closed__3);
v___x_531_ = l_Lean_MessageData_ofName(v_a_529_);
v___x_532_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_532_, 0, v___x_530_);
lean_ctor_set(v___x_532_, 1, v___x_531_);
v___x_533_ = l_Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__0___redArg(v___x_532_, v___y_445_, v___y_446_, v___y_447_, v___y_448_);
return v___x_533_;
}
else
{
lean_object* v_a_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_541_; 
v_a_534_ = lean_ctor_get(v___x_528_, 0);
v_isSharedCheck_541_ = !lean_is_exclusive(v___x_528_);
if (v_isSharedCheck_541_ == 0)
{
v___x_536_ = v___x_528_;
v_isShared_537_ = v_isSharedCheck_541_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_a_534_);
lean_dec(v___x_528_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_541_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v___x_539_; 
if (v_isShared_537_ == 0)
{
v___x_539_ = v___x_536_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v_a_534_);
v___x_539_ = v_reuseFailAlloc_540_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
return v___x_539_;
}
}
}
}
}
else
{
lean_dec(v_a_469_);
lean_dec(v_f_440_);
lean_dec(v___x_438_);
lean_dec(v_tk_437_);
lean_dec(v_a_435_);
return v___x_526_;
}
v___jp_470_:
{
lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_479_ = lean_box(0);
lean_inc(v_f_440_);
v___x_480_ = l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__5___redArg(v_f_440_, v_tk_437_, v_a_469_, v___x_479_, v___y_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_);
if (lean_obj_tag(v___x_480_) == 0)
{
lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_523_; 
v_isSharedCheck_523_ = !lean_is_exclusive(v___x_480_);
if (v_isSharedCheck_523_ == 0)
{
lean_object* v_unused_524_; 
v_unused_524_ = lean_ctor_get(v___x_480_, 0);
lean_dec(v_unused_524_);
v___x_482_ = v___x_480_;
v_isShared_483_ = v_isSharedCheck_523_;
goto v_resetjp_481_;
}
else
{
lean_dec(v___x_480_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_523_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
lean_object* v___x_484_; 
v___x_484_ = l_List_get_x3fInternal___redArg(v_a_469_, v___x_438_);
lean_dec(v_a_469_);
if (lean_obj_tag(v___x_484_) == 1)
{
lean_object* v_val_485_; lean_object* v_result_486_; lean_object* v_mctx_487_; lean_object* v___x_488_; lean_object* v_cache_489_; lean_object* v_zetaDeltaFVarIds_490_; lean_object* v_postponed_491_; lean_object* v_diag_492_; lean_object* v___x_494_; uint8_t v_isShared_495_; uint8_t v_isSharedCheck_518_; 
lean_del_object(v___x_482_);
v_val_485_ = lean_ctor_get(v___x_484_, 0);
lean_inc(v_val_485_);
lean_dec_ref_known(v___x_484_, 1);
v_result_486_ = lean_ctor_get(v_val_485_, 2);
lean_inc_ref(v_result_486_);
v_mctx_487_ = lean_ctor_get(v_val_485_, 3);
lean_inc_ref(v_mctx_487_);
lean_dec(v_val_485_);
v___x_488_ = lean_st_ref_take(v___y_476_);
v_cache_489_ = lean_ctor_get(v___x_488_, 1);
v_zetaDeltaFVarIds_490_ = lean_ctor_get(v___x_488_, 2);
v_postponed_491_ = lean_ctor_get(v___x_488_, 3);
v_diag_492_ = lean_ctor_get(v___x_488_, 4);
v_isSharedCheck_518_ = !lean_is_exclusive(v___x_488_);
if (v_isSharedCheck_518_ == 0)
{
lean_object* v_unused_519_; 
v_unused_519_ = lean_ctor_get(v___x_488_, 0);
lean_dec(v_unused_519_);
v___x_494_ = v___x_488_;
v_isShared_495_ = v_isSharedCheck_518_;
goto v_resetjp_493_;
}
else
{
lean_inc(v_diag_492_);
lean_inc(v_postponed_491_);
lean_inc(v_zetaDeltaFVarIds_490_);
lean_inc(v_cache_489_);
lean_dec(v___x_488_);
v___x_494_ = lean_box(0);
v_isShared_495_ = v_isSharedCheck_518_;
goto v_resetjp_493_;
}
v_resetjp_493_:
{
lean_object* v___x_497_; 
if (v_isShared_495_ == 0)
{
lean_ctor_set(v___x_494_, 0, v_mctx_487_);
v___x_497_ = v___x_494_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v_mctx_487_);
lean_ctor_set(v_reuseFailAlloc_517_, 1, v_cache_489_);
lean_ctor_set(v_reuseFailAlloc_517_, 2, v_zetaDeltaFVarIds_490_);
lean_ctor_set(v_reuseFailAlloc_517_, 3, v_postponed_491_);
lean_ctor_set(v_reuseFailAlloc_517_, 4, v_diag_492_);
v___x_497_ = v_reuseFailAlloc_517_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
lean_object* v___x_498_; lean_object* v_eNew_499_; lean_object* v_eqProof_500_; lean_object* v_mvarIds_501_; lean_object* v___x_502_; lean_object* v___f_503_; lean_object* v___x_504_; 
v___x_498_ = lean_st_ref_put(v___y_476_, v___x_497_);
v_eNew_499_ = lean_ctor_get(v_result_486_, 0);
lean_inc_ref(v_eNew_499_);
v_eqProof_500_ = lean_ctor_get(v_result_486_, 1);
lean_inc_ref(v_eqProof_500_);
v_mvarIds_501_ = lean_ctor_get(v_result_486_, 2);
lean_inc(v_mvarIds_501_);
lean_dec_ref(v_result_486_);
lean_inc(v_f_440_);
v___x_502_ = l_Lean_mkFVar(v_f_440_);
lean_inc(v_a_435_);
v___f_503_ = lean_alloc_closure((void*)(l_Lean_Elab_Rewrites_evalExact___lam__1___boxed), 10, 5);
lean_closure_set(v___f_503_, 0, v_eqProof_500_);
lean_closure_set(v___f_503_, 1, v___x_502_);
lean_closure_set(v___f_503_, 2, v_eNew_499_);
lean_closure_set(v___f_503_, 3, v_a_435_);
lean_closure_set(v___f_503_, 4, v_f_440_);
v___x_504_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Rewrites_evalExact_spec__6___redArg(v_a_435_, v___f_503_, v___y_475_, v___y_476_, v___y_477_, v___y_478_);
if (lean_obj_tag(v___x_504_) == 0)
{
lean_object* v_a_505_; lean_object* v_mvarId_506_; lean_object* v___x_507_; lean_object* v___x_508_; 
v_a_505_ = lean_ctor_get(v___x_504_, 0);
lean_inc(v_a_505_);
lean_dec_ref_known(v___x_504_, 1);
v_mvarId_506_ = lean_ctor_get(v_a_505_, 1);
lean_inc(v_mvarId_506_);
lean_dec(v_a_505_);
v___x_507_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_507_, 0, v_mvarId_506_);
lean_ctor_set(v___x_507_, 1, v_mvarIds_501_);
v___x_508_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_507_, v___y_472_, v___y_475_, v___y_476_, v___y_477_, v___y_478_);
return v___x_508_;
}
else
{
lean_object* v_a_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_516_; 
lean_dec(v_mvarIds_501_);
v_a_509_ = lean_ctor_get(v___x_504_, 0);
v_isSharedCheck_516_ = !lean_is_exclusive(v___x_504_);
if (v_isSharedCheck_516_ == 0)
{
v___x_511_ = v___x_504_;
v_isShared_512_ = v_isSharedCheck_516_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_a_509_);
lean_dec(v___x_504_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_516_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v___x_514_; 
if (v_isShared_512_ == 0)
{
v___x_514_ = v___x_511_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v_a_509_);
v___x_514_ = v_reuseFailAlloc_515_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
return v___x_514_;
}
}
}
}
}
}
else
{
lean_object* v___x_521_; 
lean_dec(v___x_484_);
lean_dec(v_f_440_);
lean_dec(v_a_435_);
if (v_isShared_483_ == 0)
{
lean_ctor_set(v___x_482_, 0, v___x_479_);
v___x_521_ = v___x_482_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v___x_479_);
v___x_521_ = v_reuseFailAlloc_522_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
return v___x_521_;
}
}
}
}
else
{
lean_dec(v_a_469_);
lean_dec(v_f_440_);
lean_dec(v___x_438_);
lean_dec(v_a_435_);
return v___x_480_;
}
}
}
else
{
lean_object* v_a_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_549_; 
lean_dec(v_f_440_);
lean_dec(v___x_438_);
lean_dec(v_tk_437_);
lean_dec(v_a_435_);
v_a_542_ = lean_ctor_get(v___x_468_, 0);
v_isSharedCheck_549_ = !lean_is_exclusive(v___x_468_);
if (v_isSharedCheck_549_ == 0)
{
v___x_544_ = v___x_468_;
v_isShared_545_ = v_isSharedCheck_549_;
goto v_resetjp_543_;
}
else
{
lean_inc(v_a_542_);
lean_dec(v___x_468_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_549_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
lean_object* v___x_547_; 
if (v_isShared_545_ == 0)
{
v___x_547_ = v___x_544_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v_a_542_);
v___x_547_ = v_reuseFailAlloc_548_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
return v___x_547_;
}
}
}
}
else
{
lean_object* v_a_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_557_; 
lean_dec(v_a_460_);
lean_dec(v_f_440_);
lean_dec(v___x_438_);
lean_dec(v_tk_437_);
lean_dec(v_a_435_);
lean_dec(v_a_434_);
v_a_550_ = lean_ctor_get(v___x_463_, 0);
v_isSharedCheck_557_ = !lean_is_exclusive(v___x_463_);
if (v_isSharedCheck_557_ == 0)
{
v___x_552_ = v___x_463_;
v_isShared_553_ = v_isSharedCheck_557_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_a_550_);
lean_dec(v___x_463_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_557_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v___x_555_; 
if (v_isShared_553_ == 0)
{
v___x_555_ = v___x_552_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v_a_550_);
v___x_555_ = v_reuseFailAlloc_556_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
return v___x_555_;
}
}
}
}
else
{
lean_object* v_a_558_; lean_object* v___x_560_; uint8_t v_isShared_561_; uint8_t v_isSharedCheck_565_; 
lean_dec(v_f_440_);
lean_dec(v___x_438_);
lean_dec(v_tk_437_);
lean_dec(v_a_435_);
lean_dec(v_a_434_);
v_a_558_ = lean_ctor_get(v___x_457_, 0);
v_isSharedCheck_565_ = !lean_is_exclusive(v___x_457_);
if (v_isSharedCheck_565_ == 0)
{
v___x_560_ = v___x_457_;
v_isShared_561_ = v_isSharedCheck_565_;
goto v_resetjp_559_;
}
else
{
lean_inc(v_a_558_);
lean_dec(v___x_457_);
v___x_560_ = lean_box(0);
v_isShared_561_ = v_isSharedCheck_565_;
goto v_resetjp_559_;
}
v_resetjp_559_:
{
lean_object* v___x_563_; 
if (v_isShared_561_ == 0)
{
v___x_563_ = v___x_560_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v_a_558_);
v___x_563_ = v_reuseFailAlloc_564_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
return v___x_563_;
}
}
}
}
else
{
lean_object* v___x_566_; lean_object* v___x_568_; 
lean_dec(v_f_440_);
lean_dec(v___x_438_);
lean_dec(v_tk_437_);
lean_dec(v_a_435_);
lean_dec(v_a_434_);
v___x_566_ = lean_box(0);
if (v_isShared_454_ == 0)
{
lean_ctor_set(v___x_453_, 0, v___x_566_);
v___x_568_ = v___x_453_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v___x_566_);
v___x_568_ = v_reuseFailAlloc_569_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
return v___x_568_;
}
}
}
else
{
lean_object* v___x_570_; lean_object* v___x_572_; 
lean_dec(v_a_451_);
lean_dec(v_f_440_);
lean_dec(v___x_438_);
lean_dec(v_tk_437_);
lean_dec(v_a_435_);
lean_dec(v_a_434_);
v___x_570_ = lean_box(0);
if (v_isShared_454_ == 0)
{
lean_ctor_set(v___x_453_, 0, v___x_570_);
v___x_572_ = v___x_453_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v___x_570_);
v___x_572_ = v_reuseFailAlloc_573_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
return v___x_572_;
}
}
}
}
else
{
lean_object* v_a_575_; lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_582_; 
lean_dec(v_f_440_);
lean_dec(v___x_438_);
lean_dec(v_tk_437_);
lean_dec(v_a_435_);
lean_dec(v_a_434_);
v_a_575_ = lean_ctor_get(v___x_450_, 0);
v_isSharedCheck_582_ = !lean_is_exclusive(v___x_450_);
if (v_isSharedCheck_582_ == 0)
{
v___x_577_ = v___x_450_;
v_isShared_578_ = v_isSharedCheck_582_;
goto v_resetjp_576_;
}
else
{
lean_inc(v_a_575_);
lean_dec(v___x_450_);
v___x_577_ = lean_box(0);
v_isShared_578_ = v_isSharedCheck_582_;
goto v_resetjp_576_;
}
v_resetjp_576_:
{
lean_object* v___x_580_; 
if (v_isShared_578_ == 0)
{
v___x_580_ = v___x_577_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v_a_575_);
v___x_580_ = v_reuseFailAlloc_581_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
return v___x_580_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Rewrites_evalExact___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_434_ = stack[0].m_obj;
lean_object* v_a_435_ = stack[1].m_obj;
lean_object* v___y_436_ = stack[2].m_obj;
lean_object* v_tk_437_ = stack[3].m_obj;
lean_object* v___x_438_ = stack[4].m_obj;
lean_object* v___x_439_ = stack[5].m_obj;
lean_object* v_f_440_ = stack[6].m_obj;
lean_object* v___y_441_ = stack[7].m_obj;
lean_object* v___y_442_ = stack[8].m_obj;
lean_object* v___y_443_ = stack[9].m_obj;
lean_object* v___y_444_ = stack[10].m_obj;
lean_object* v___y_445_ = stack[11].m_obj;
lean_object* v___y_446_ = stack[12].m_obj;
lean_object* v___y_447_ = stack[13].m_obj;
lean_object* v___y_448_ = stack[14].m_obj;
lean_object* v_res_583_;
v_res_583_ = l_Lean_Elab_Rewrites_evalExact___lam__2(v_a_434_, v_a_435_, v___y_436_, v_tk_437_, v___x_438_, v___x_439_, v_f_440_, v___y_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_, v___y_448_);
stack->m_obj
 = v_res_583_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact___lam__2___boxed(lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v___y_586_, lean_object* v_tk_587_, lean_object* v___x_588_, lean_object* v___x_589_, lean_object* v_f_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_){
_start:
{
lean_object* v_res_600_; 
v_res_600_ = l_Lean_Elab_Rewrites_evalExact___lam__2(v_a_584_, v_a_585_, v___y_586_, v_tk_587_, v___x_588_, v___x_589_, v_f_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_, v___y_597_, v___y_598_);
lean_dec(v___y_598_);
lean_dec_ref(v___y_597_);
lean_dec(v___y_596_);
lean_dec_ref(v___y_595_);
lean_dec(v___y_594_);
lean_dec_ref(v___y_593_);
lean_dec(v___y_592_);
lean_dec_ref(v___y_591_);
lean_dec(v___x_589_);
lean_dec(v___y_586_);
return v_res_600_;
}
}
lean_object* l_List_forM___at___00Lean_Elab_Rewrites_evalExact_spec__3(lean_object* v_state_601_, lean_object* v_tk_602_, lean_object* v_as_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_){
_start:
{
if (lean_obj_tag(v_as_603_) == 0)
{
lean_object* v___x_613_; lean_object* v___x_614_; 
lean_dec(v_tk_602_);
lean_dec_ref(v_state_601_);
v___x_613_ = lean_box(0);
v___x_614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_614_, 0, v___x_613_);
return v___x_614_;
}
else
{
lean_object* v_head_615_; lean_object* v_tail_616_; lean_object* v___x_617_; lean_object* v___x_618_; 
v_head_615_ = lean_ctor_get(v_as_603_, 0);
lean_inc(v_head_615_);
v_tail_616_ = lean_ctor_get(v_as_603_, 1);
lean_inc(v_tail_616_);
lean_dec_ref_known(v_as_603_, 2);
lean_inc_ref(v_state_601_);
v___x_617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_617_, 0, v_state_601_);
lean_inc(v_tk_602_);
v___x_618_ = l_Lean_Meta_Rewrites_RewriteResult_addSuggestion(v_tk_602_, v_head_615_, v___x_617_, v___y_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_);
if (lean_obj_tag(v___x_618_) == 0)
{
lean_dec_ref_known(v___x_618_, 1);
v_as_603_ = v_tail_616_;
goto _start;
}
else
{
lean_dec(v_tail_616_);
lean_dec(v_tk_602_);
lean_dec_ref(v_state_601_);
return v___x_618_;
}
}
}
}
LEAN_EXPORT void l_List_forM___at___00Lean_Elab_Rewrites_evalExact_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_state_601_ = stack[0].m_obj;
lean_object* v_tk_602_ = stack[1].m_obj;
lean_object* v_as_603_ = stack[2].m_obj;
lean_object* v___y_604_ = stack[3].m_obj;
lean_object* v___y_605_ = stack[4].m_obj;
lean_object* v___y_606_ = stack[5].m_obj;
lean_object* v___y_607_ = stack[6].m_obj;
lean_object* v___y_608_ = stack[7].m_obj;
lean_object* v___y_609_ = stack[8].m_obj;
lean_object* v___y_610_ = stack[9].m_obj;
lean_object* v___y_611_ = stack[10].m_obj;
lean_object* v_res_620_;
v_res_620_ = l_List_forM___at___00Lean_Elab_Rewrites_evalExact_spec__3(v_state_601_, v_tk_602_, v_as_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_);
stack->m_obj
 = v_res_620_;
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_Rewrites_evalExact_spec__3___boxed(lean_object* v_state_621_, lean_object* v_tk_622_, lean_object* v_as_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_){
_start:
{
lean_object* v_res_633_; 
v_res_633_ = l_List_forM___at___00Lean_Elab_Rewrites_evalExact_spec__3(v_state_621_, v_tk_622_, v_as_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_);
lean_dec(v___y_631_);
lean_dec_ref(v___y_630_);
lean_dec(v___y_629_);
lean_dec_ref(v___y_628_);
lean_dec(v___y_627_);
lean_dec_ref(v___y_626_);
lean_dec(v___y_625_);
lean_dec_ref(v___y_624_);
return v_res_633_;
}
}
static lean_object* _init_l_Lean_Elab_Rewrites_evalExact___lam__3___closed__9(void){
_start:
{
lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_644_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___lam__3___closed__8));
v___x_645_ = l_Lean_stringToMessageData(v___x_644_);
return v___x_645_;
}
}
lean_object* l_Lean_Elab_Rewrites_evalExact___lam__3(lean_object* v_a_646_, lean_object* v_a_647_, lean_object* v___y_648_, uint8_t v___x_649_, lean_object* v___x_650_, lean_object* v___x_651_, lean_object* v___x_652_, lean_object* v___x_653_, lean_object* v_tk_654_, lean_object* v___x_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_){
_start:
{
lean_object* v___x_665_; 
lean_inc(v_a_646_);
v___x_665_ = l_Lean_MVarId_getType(v_a_646_, v___y_660_, v___y_661_, v___y_662_, v___y_663_);
if (lean_obj_tag(v___x_665_) == 0)
{
lean_object* v_a_666_; lean_object* v___x_667_; lean_object* v_a_668_; lean_object* v___x_669_; lean_object* v___x_670_; 
v_a_666_ = lean_ctor_get(v___x_665_, 0);
lean_inc(v_a_666_);
lean_dec_ref_known(v___x_665_, 1);
v___x_667_ = l_Lean_instantiateMVars___at___00Lean_Elab_Rewrites_evalExact_spec__2___redArg(v_a_666_, v___y_661_);
v_a_668_ = lean_ctor_get(v___x_667_, 0);
lean_inc(v_a_668_);
lean_dec_ref(v___x_667_);
v___x_669_ = lean_box(0);
v___x_670_ = l_Lean_Meta_Rewrites_localHypotheses(v___x_669_, v___y_660_, v___y_661_, v___y_662_, v___y_663_);
if (lean_obj_tag(v___x_670_) == 0)
{
lean_object* v_a_671_; uint8_t v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
v_a_671_ = lean_ctor_get(v___x_670_, 0);
lean_inc(v_a_671_);
lean_dec_ref_known(v___x_670_, 1);
v___x_672_ = 2;
v___x_673_ = lean_unsigned_to_nat(20u);
v___x_674_ = lean_unsigned_to_nat(10u);
lean_inc(v_a_646_);
v___x_675_ = l_Lean_Meta_Rewrites_findRewrites(v_a_671_, v_a_647_, v_a_646_, v_a_668_, v___y_648_, v___x_672_, v___x_649_, v___x_673_, v___x_674_, v___y_660_, v___y_661_, v___y_662_, v___y_663_);
if (lean_obj_tag(v___x_675_) == 0)
{
lean_object* v_a_676_; lean_object* v___y_678_; lean_object* v___y_679_; lean_object* v___y_680_; lean_object* v___y_681_; lean_object* v___y_682_; lean_object* v___y_683_; lean_object* v___y_684_; lean_object* v___y_685_; lean_object* v___x_763_; lean_object* v___x_764_; 
v_a_676_ = lean_ctor_get(v___x_675_, 0);
lean_inc(v_a_676_);
lean_dec_ref_known(v___x_675_, 1);
v___x_763_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___lam__2___closed__1));
v___x_764_ = l_Lean_reportOutOfHeartbeats(v___x_763_, v_tk_654_, v___x_655_, v___y_662_, v___y_663_);
if (lean_obj_tag(v___x_764_) == 0)
{
uint8_t v___x_765_; 
lean_dec_ref_known(v___x_764_, 1);
v___x_765_ = l_List_isEmpty___redArg(v_a_676_);
if (v___x_765_ == 0)
{
v___y_678_ = v___y_656_;
v___y_679_ = v___y_657_;
v___y_680_ = v___y_658_;
v___y_681_ = v___y_659_;
v___y_682_ = v___y_660_;
v___y_683_ = v___y_661_;
v___y_684_ = v___y_662_;
v___y_685_ = v___y_663_;
goto v___jp_677_;
}
else
{
lean_object* v___x_766_; lean_object* v___x_767_; 
lean_dec(v_a_676_);
lean_dec(v_tk_654_);
lean_dec_ref(v___x_653_);
lean_dec_ref(v___x_652_);
lean_dec_ref(v___x_651_);
lean_dec(v___x_650_);
lean_dec(v_a_646_);
v___x_766_ = lean_obj_once(&l_Lean_Elab_Rewrites_evalExact___lam__3___closed__9, &l_Lean_Elab_Rewrites_evalExact___lam__3___closed__9_once, _init_l_Lean_Elab_Rewrites_evalExact___lam__3___closed__9);
v___x_767_ = l_Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__0___redArg(v___x_766_, v___y_660_, v___y_661_, v___y_662_, v___y_663_);
return v___x_767_;
}
}
else
{
lean_dec(v_a_676_);
lean_dec(v_tk_654_);
lean_dec_ref(v___x_653_);
lean_dec_ref(v___x_652_);
lean_dec_ref(v___x_651_);
lean_dec(v___x_650_);
lean_dec(v_a_646_);
return v___x_764_;
}
v___jp_677_:
{
lean_object* v___x_686_; 
v___x_686_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_679_, v___y_681_, v___y_683_, v___y_685_);
if (lean_obj_tag(v___x_686_) == 0)
{
lean_object* v_a_687_; lean_object* v___x_688_; 
v_a_687_ = lean_ctor_get(v___x_686_, 0);
lean_inc(v_a_687_);
lean_dec_ref_known(v___x_686_, 1);
v___x_688_ = l_List_get_x3fInternal___redArg(v_a_676_, v___x_650_);
if (lean_obj_tag(v___x_688_) == 1)
{
lean_object* v_val_689_; lean_object* v_result_690_; lean_object* v_mctx_691_; lean_object* v___x_692_; lean_object* v_cache_693_; lean_object* v_zetaDeltaFVarIds_694_; lean_object* v_postponed_695_; lean_object* v_diag_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_752_; 
lean_dec(v_a_687_);
v_val_689_ = lean_ctor_get(v___x_688_, 0);
lean_inc(v_val_689_);
lean_dec_ref_known(v___x_688_, 1);
v_result_690_ = lean_ctor_get(v_val_689_, 2);
lean_inc_ref(v_result_690_);
v_mctx_691_ = lean_ctor_get(v_val_689_, 3);
lean_inc_ref(v_mctx_691_);
lean_dec(v_val_689_);
v___x_692_ = lean_st_ref_take(v___y_683_);
v_cache_693_ = lean_ctor_get(v___x_692_, 1);
v_zetaDeltaFVarIds_694_ = lean_ctor_get(v___x_692_, 2);
v_postponed_695_ = lean_ctor_get(v___x_692_, 3);
v_diag_696_ = lean_ctor_get(v___x_692_, 4);
v_isSharedCheck_752_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_752_ == 0)
{
lean_object* v_unused_753_; 
v_unused_753_ = lean_ctor_get(v___x_692_, 0);
lean_dec(v_unused_753_);
v___x_698_ = v___x_692_;
v_isShared_699_ = v_isSharedCheck_752_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_diag_696_);
lean_inc(v_postponed_695_);
lean_inc(v_zetaDeltaFVarIds_694_);
lean_inc(v_cache_693_);
lean_dec(v___x_692_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_752_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_701_; 
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 0, v_mctx_691_);
v___x_701_ = v___x_698_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v_mctx_691_);
lean_ctor_set(v_reuseFailAlloc_751_, 1, v_cache_693_);
lean_ctor_set(v_reuseFailAlloc_751_, 2, v_zetaDeltaFVarIds_694_);
lean_ctor_set(v_reuseFailAlloc_751_, 3, v_postponed_695_);
lean_ctor_set(v_reuseFailAlloc_751_, 4, v_diag_696_);
v___x_701_ = v_reuseFailAlloc_751_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_702_ = lean_st_ref_put(v___y_683_, v___x_701_);
v___x_703_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_679_, v___y_681_, v___y_683_, v___y_685_);
if (lean_obj_tag(v___x_703_) == 0)
{
lean_object* v_a_704_; lean_object* v_eNew_705_; lean_object* v_eqProof_706_; lean_object* v_mvarIds_707_; lean_object* v___x_708_; 
v_a_704_ = lean_ctor_get(v___x_703_, 0);
lean_inc(v_a_704_);
lean_dec_ref_known(v___x_703_, 1);
v_eNew_705_ = lean_ctor_get(v_result_690_, 0);
lean_inc_ref(v_eNew_705_);
v_eqProof_706_ = lean_ctor_get(v_result_690_, 1);
lean_inc_ref(v_eqProof_706_);
v_mvarIds_707_ = lean_ctor_get(v_result_690_, 2);
lean_inc(v_mvarIds_707_);
lean_dec_ref(v_result_690_);
v___x_708_ = l_Lean_MVarId_replaceTargetEq(v_a_646_, v_eNew_705_, v_eqProof_706_, v___y_682_, v___y_683_, v___y_684_, v___y_685_);
if (lean_obj_tag(v___x_708_) == 0)
{
lean_object* v_a_709_; lean_object* v___x_710_; lean_object* v___x_711_; 
v_a_709_ = lean_ctor_get(v___x_708_, 0);
lean_inc(v_a_709_);
lean_dec_ref_known(v___x_708_, 1);
v___x_710_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_710_, 0, v_a_709_);
lean_ctor_set(v___x_710_, 1, v_mvarIds_707_);
v___x_711_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_710_, v___y_679_, v___y_682_, v___y_683_, v___y_684_, v___y_685_);
if (lean_obj_tag(v___x_711_) == 0)
{
lean_object* v_ref_712_; uint8_t v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; 
lean_dec_ref_known(v___x_711_, 1);
v_ref_712_ = lean_ctor_get(v___y_684_, 2);
v___x_713_ = 0;
v___x_714_ = l_Lean_SourceInfo_fromRef(v_ref_712_, v___x_713_);
v___x_715_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___lam__3___closed__0));
lean_inc_ref_n(v___x_653_, 3);
lean_inc_ref_n(v___x_652_, 3);
lean_inc_ref_n(v___x_651_, 3);
v___x_716_ = l_Lean_Name_mkStr4(v___x_651_, v___x_652_, v___x_653_, v___x_715_);
v___x_717_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___lam__3___closed__1));
lean_inc_n(v___x_714_, 6);
v___x_718_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_718_, 0, v___x_714_);
lean_ctor_set(v___x_718_, 1, v___x_717_);
v___x_719_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___lam__3___closed__2));
v___x_720_ = l_Lean_Name_mkStr4(v___x_651_, v___x_652_, v___x_653_, v___x_719_);
v___x_721_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___lam__3___closed__3));
v___x_722_ = l_Lean_Name_mkStr4(v___x_651_, v___x_652_, v___x_653_, v___x_721_);
v___x_723_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___lam__3___closed__5));
v___x_724_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___lam__3___closed__6));
v___x_725_ = l_Lean_Name_mkStr4(v___x_651_, v___x_652_, v___x_653_, v___x_724_);
v___x_726_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___lam__3___closed__7));
v___x_727_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_727_, 0, v___x_714_);
lean_ctor_set(v___x_727_, 1, v___x_726_);
v___x_728_ = l_Lean_Syntax_node1(v___x_714_, v___x_725_, v___x_727_);
v___x_729_ = l_Lean_Syntax_node1(v___x_714_, v___x_723_, v___x_728_);
v___x_730_ = l_Lean_Syntax_node1(v___x_714_, v___x_722_, v___x_729_);
v___x_731_ = l_Lean_Syntax_node1(v___x_714_, v___x_720_, v___x_730_);
v___x_732_ = l_Lean_Syntax_node2(v___x_714_, v___x_716_, v___x_718_, v___x_731_);
v___x_733_ = l_Lean_Elab_Tactic_evalTactic(v___x_732_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_);
if (lean_obj_tag(v___x_733_) == 0)
{
lean_object* v___x_734_; 
lean_dec_ref_known(v___x_733_, 1);
v___x_734_ = l_List_forM___at___00Lean_Elab_Rewrites_evalExact_spec__3(v_a_704_, v_tk_654_, v_a_676_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_);
return v___x_734_;
}
else
{
lean_dec(v_a_704_);
lean_dec(v_a_676_);
lean_dec(v_tk_654_);
return v___x_733_;
}
}
else
{
lean_dec(v_a_704_);
lean_dec(v_a_676_);
lean_dec(v_tk_654_);
lean_dec_ref(v___x_653_);
lean_dec_ref(v___x_652_);
lean_dec_ref(v___x_651_);
return v___x_711_;
}
}
else
{
lean_object* v_a_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_742_; 
lean_dec(v_mvarIds_707_);
lean_dec(v_a_704_);
lean_dec(v_a_676_);
lean_dec(v_tk_654_);
lean_dec_ref(v___x_653_);
lean_dec_ref(v___x_652_);
lean_dec_ref(v___x_651_);
v_a_735_ = lean_ctor_get(v___x_708_, 0);
v_isSharedCheck_742_ = !lean_is_exclusive(v___x_708_);
if (v_isSharedCheck_742_ == 0)
{
v___x_737_ = v___x_708_;
v_isShared_738_ = v_isSharedCheck_742_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_a_735_);
lean_dec(v___x_708_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_742_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v___x_740_; 
if (v_isShared_738_ == 0)
{
v___x_740_ = v___x_737_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v_a_735_);
v___x_740_ = v_reuseFailAlloc_741_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
return v___x_740_;
}
}
}
}
else
{
lean_object* v_a_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_750_; 
lean_dec_ref(v_result_690_);
lean_dec(v_a_676_);
lean_dec(v_tk_654_);
lean_dec_ref(v___x_653_);
lean_dec_ref(v___x_652_);
lean_dec_ref(v___x_651_);
lean_dec(v_a_646_);
v_a_743_ = lean_ctor_get(v___x_703_, 0);
v_isSharedCheck_750_ = !lean_is_exclusive(v___x_703_);
if (v_isSharedCheck_750_ == 0)
{
v___x_745_ = v___x_703_;
v_isShared_746_ = v_isSharedCheck_750_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_a_743_);
lean_dec(v___x_703_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_750_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
lean_object* v___x_748_; 
if (v_isShared_746_ == 0)
{
v___x_748_ = v___x_745_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v_a_743_);
v___x_748_ = v_reuseFailAlloc_749_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
return v___x_748_;
}
}
}
}
}
}
else
{
lean_object* v___x_754_; 
lean_dec(v___x_688_);
lean_dec_ref(v___x_653_);
lean_dec_ref(v___x_652_);
lean_dec_ref(v___x_651_);
lean_dec(v_a_646_);
v___x_754_ = l_List_forM___at___00Lean_Elab_Rewrites_evalExact_spec__3(v_a_687_, v_tk_654_, v_a_676_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_);
return v___x_754_;
}
}
else
{
lean_object* v_a_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_762_; 
lean_dec(v_a_676_);
lean_dec(v_tk_654_);
lean_dec_ref(v___x_653_);
lean_dec_ref(v___x_652_);
lean_dec_ref(v___x_651_);
lean_dec(v___x_650_);
lean_dec(v_a_646_);
v_a_755_ = lean_ctor_get(v___x_686_, 0);
v_isSharedCheck_762_ = !lean_is_exclusive(v___x_686_);
if (v_isSharedCheck_762_ == 0)
{
v___x_757_ = v___x_686_;
v_isShared_758_ = v_isSharedCheck_762_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_a_755_);
lean_dec(v___x_686_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_762_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v___x_760_; 
if (v_isShared_758_ == 0)
{
v___x_760_ = v___x_757_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v_a_755_);
v___x_760_ = v_reuseFailAlloc_761_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
return v___x_760_;
}
}
}
}
}
else
{
lean_object* v_a_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_775_; 
lean_dec(v_tk_654_);
lean_dec_ref(v___x_653_);
lean_dec_ref(v___x_652_);
lean_dec_ref(v___x_651_);
lean_dec(v___x_650_);
lean_dec(v_a_646_);
v_a_768_ = lean_ctor_get(v___x_675_, 0);
v_isSharedCheck_775_ = !lean_is_exclusive(v___x_675_);
if (v_isSharedCheck_775_ == 0)
{
v___x_770_ = v___x_675_;
v_isShared_771_ = v_isSharedCheck_775_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_a_768_);
lean_dec(v___x_675_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_775_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v___x_773_; 
if (v_isShared_771_ == 0)
{
v___x_773_ = v___x_770_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v_a_768_);
v___x_773_ = v_reuseFailAlloc_774_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
return v___x_773_;
}
}
}
}
else
{
lean_object* v_a_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_783_; 
lean_dec(v_a_668_);
lean_dec(v_tk_654_);
lean_dec_ref(v___x_653_);
lean_dec_ref(v___x_652_);
lean_dec_ref(v___x_651_);
lean_dec(v___x_650_);
lean_dec(v_a_647_);
lean_dec(v_a_646_);
v_a_776_ = lean_ctor_get(v___x_670_, 0);
v_isSharedCheck_783_ = !lean_is_exclusive(v___x_670_);
if (v_isSharedCheck_783_ == 0)
{
v___x_778_ = v___x_670_;
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_a_776_);
lean_dec(v___x_670_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v___x_781_; 
if (v_isShared_779_ == 0)
{
v___x_781_ = v___x_778_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v_a_776_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
return v___x_781_;
}
}
}
}
else
{
lean_object* v_a_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_791_; 
lean_dec(v_tk_654_);
lean_dec_ref(v___x_653_);
lean_dec_ref(v___x_652_);
lean_dec_ref(v___x_651_);
lean_dec(v___x_650_);
lean_dec(v_a_647_);
lean_dec(v_a_646_);
v_a_784_ = lean_ctor_get(v___x_665_, 0);
v_isSharedCheck_791_ = !lean_is_exclusive(v___x_665_);
if (v_isSharedCheck_791_ == 0)
{
v___x_786_ = v___x_665_;
v_isShared_787_ = v_isSharedCheck_791_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_a_784_);
lean_dec(v___x_665_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_791_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v___x_789_; 
if (v_isShared_787_ == 0)
{
v___x_789_ = v___x_786_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v_a_784_);
v___x_789_ = v_reuseFailAlloc_790_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
return v___x_789_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Rewrites_evalExact___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_646_ = stack[0].m_obj;
lean_object* v_a_647_ = stack[1].m_obj;
lean_object* v___y_648_ = stack[2].m_obj;
uint8_t v___x_649_ = stack[3].m_num;
lean_object* v___x_650_ = stack[4].m_obj;
lean_object* v___x_651_ = stack[5].m_obj;
lean_object* v___x_652_ = stack[6].m_obj;
lean_object* v___x_653_ = stack[7].m_obj;
lean_object* v_tk_654_ = stack[8].m_obj;
lean_object* v___x_655_ = stack[9].m_obj;
lean_object* v___y_656_ = stack[10].m_obj;
lean_object* v___y_657_ = stack[11].m_obj;
lean_object* v___y_658_ = stack[12].m_obj;
lean_object* v___y_659_ = stack[13].m_obj;
lean_object* v___y_660_ = stack[14].m_obj;
lean_object* v___y_661_ = stack[15].m_obj;
lean_object* v___y_662_ = stack[16].m_obj;
lean_object* v___y_663_ = stack[17].m_obj;
lean_object* v_res_792_;
v_res_792_ = l_Lean_Elab_Rewrites_evalExact___lam__3(v_a_646_, v_a_647_, v___y_648_, v___x_649_, v___x_650_, v___x_651_, v___x_652_, v___x_653_, v_tk_654_, v___x_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_);
stack->m_obj
 = v_res_792_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact___lam__3___boxed(lean_object** _args){
lean_object* v_a_793_ = _args[0];
lean_object* v_a_794_ = _args[1];
lean_object* v___y_795_ = _args[2];
lean_object* v___x_796_ = _args[3];
lean_object* v___x_797_ = _args[4];
lean_object* v___x_798_ = _args[5];
lean_object* v___x_799_ = _args[6];
lean_object* v___x_800_ = _args[7];
lean_object* v_tk_801_ = _args[8];
lean_object* v___x_802_ = _args[9];
lean_object* v___y_803_ = _args[10];
lean_object* v___y_804_ = _args[11];
lean_object* v___y_805_ = _args[12];
lean_object* v___y_806_ = _args[13];
lean_object* v___y_807_ = _args[14];
lean_object* v___y_808_ = _args[15];
lean_object* v___y_809_ = _args[16];
lean_object* v___y_810_ = _args[17];
lean_object* v___y_811_ = _args[18];
_start:
{
uint8_t v___x_22636__boxed_812_; lean_object* v_res_813_; 
v___x_22636__boxed_812_ = lean_unbox(v___x_796_);
v_res_813_ = l_Lean_Elab_Rewrites_evalExact___lam__3(v_a_793_, v_a_794_, v___y_795_, v___x_22636__boxed_812_, v___x_797_, v___x_798_, v___x_799_, v___x_800_, v_tk_801_, v___x_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_);
lean_dec(v___y_810_);
lean_dec_ref(v___y_809_);
lean_dec(v___y_808_);
lean_dec_ref(v___y_807_);
lean_dec(v___y_806_);
lean_dec_ref(v___y_805_);
lean_dec(v___y_804_);
lean_dec_ref(v___y_803_);
lean_dec(v___x_802_);
lean_dec(v___y_795_);
return v_res_813_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__7(size_t v_sz_814_, size_t v_i_815_, lean_object* v_bs_816_){
_start:
{
uint8_t v___x_817_; 
v___x_817_ = lean_usize_dec_lt(v_i_815_, v_sz_814_);
if (v___x_817_ == 0)
{
return v_bs_816_;
}
else
{
lean_object* v_v_818_; lean_object* v___x_819_; lean_object* v_bs_x27_820_; lean_object* v___x_821_; size_t v___x_822_; size_t v___x_823_; lean_object* v___x_824_; 
v_v_818_ = lean_array_uget(v_bs_816_, v_i_815_);
v___x_819_ = lean_unsigned_to_nat(0u);
v_bs_x27_820_ = lean_array_uset(v_bs_816_, v_i_815_, v___x_819_);
v___x_821_ = l_Lean_Syntax_getId(v_v_818_);
lean_dec(v_v_818_);
v___x_822_ = ((size_t)1ULL);
v___x_823_ = lean_usize_add(v_i_815_, v___x_822_);
v___x_824_ = lean_array_uset(v_bs_x27_820_, v_i_815_, v___x_821_);
v_i_815_ = v___x_823_;
v_bs_816_ = v___x_824_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__7_0interp(lean_interpreter_value* stack)
{
size_t v_sz_814_ = stack[0].m_num;
size_t v_i_815_ = stack[1].m_num;
lean_object* v_bs_816_ = stack[2].m_obj;
lean_object* v_res_826_;
v_res_826_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__7(v_sz_814_, v_i_815_, v_bs_816_);
stack->m_obj
 = v_res_826_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__7___boxed(lean_object* v_sz_827_, lean_object* v_i_828_, lean_object* v_bs_829_){
_start:
{
size_t v_sz_boxed_830_; size_t v_i_boxed_831_; lean_object* v_res_832_; 
v_sz_boxed_830_ = lean_unbox_usize(v_sz_827_);
lean_dec(v_sz_827_);
v_i_boxed_831_ = lean_unbox_usize(v_i_828_);
lean_dec(v_i_828_);
v_res_832_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__7(v_sz_boxed_830_, v_i_boxed_831_, v_bs_829_);
return v_res_832_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Rewrites_evalExact_spec__10(uint8_t v___x_833_, uint8_t v___x_834_, lean_object* v_as_835_, size_t v_i_836_, size_t v_stop_837_, lean_object* v_b_838_){
_start:
{
lean_object* v___y_840_; uint8_t v___x_844_; 
v___x_844_ = lean_usize_dec_eq(v_i_836_, v_stop_837_);
if (v___x_844_ == 0)
{
lean_object* v_fst_845_; uint8_t v___x_846_; 
v_fst_845_ = lean_ctor_get(v_b_838_, 0);
v___x_846_ = lean_unbox(v_fst_845_);
if (v___x_846_ == 0)
{
lean_object* v_snd_847_; lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_855_; 
v_snd_847_ = lean_ctor_get(v_b_838_, 1);
v_isSharedCheck_855_ = !lean_is_exclusive(v_b_838_);
if (v_isSharedCheck_855_ == 0)
{
lean_object* v_unused_856_; 
v_unused_856_ = lean_ctor_get(v_b_838_, 0);
lean_dec(v_unused_856_);
v___x_849_ = v_b_838_;
v_isShared_850_ = v_isSharedCheck_855_;
goto v_resetjp_848_;
}
else
{
lean_inc(v_snd_847_);
lean_dec(v_b_838_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_855_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
lean_object* v___x_851_; lean_object* v___x_853_; 
v___x_851_ = lean_box(v___x_833_);
if (v_isShared_850_ == 0)
{
lean_ctor_set(v___x_849_, 0, v___x_851_);
v___x_853_ = v___x_849_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v___x_851_);
lean_ctor_set(v_reuseFailAlloc_854_, 1, v_snd_847_);
v___x_853_ = v_reuseFailAlloc_854_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
v___y_840_ = v___x_853_;
goto v___jp_839_;
}
}
}
else
{
lean_object* v_snd_857_; lean_object* v___x_859_; uint8_t v_isShared_860_; uint8_t v_isSharedCheck_867_; 
v_snd_857_ = lean_ctor_get(v_b_838_, 1);
v_isSharedCheck_867_ = !lean_is_exclusive(v_b_838_);
if (v_isSharedCheck_867_ == 0)
{
lean_object* v_unused_868_; 
v_unused_868_ = lean_ctor_get(v_b_838_, 0);
lean_dec(v_unused_868_);
v___x_859_ = v_b_838_;
v_isShared_860_ = v_isSharedCheck_867_;
goto v_resetjp_858_;
}
else
{
lean_inc(v_snd_857_);
lean_dec(v_b_838_);
v___x_859_ = lean_box(0);
v_isShared_860_ = v_isSharedCheck_867_;
goto v_resetjp_858_;
}
v_resetjp_858_:
{
lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_865_; 
v___x_861_ = lean_array_uget_borrowed(v_as_835_, v_i_836_);
lean_inc(v___x_861_);
v___x_862_ = lean_array_push(v_snd_857_, v___x_861_);
v___x_863_ = lean_box(v___x_834_);
if (v_isShared_860_ == 0)
{
lean_ctor_set(v___x_859_, 1, v___x_862_);
lean_ctor_set(v___x_859_, 0, v___x_863_);
v___x_865_ = v___x_859_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v___x_863_);
lean_ctor_set(v_reuseFailAlloc_866_, 1, v___x_862_);
v___x_865_ = v_reuseFailAlloc_866_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
v___y_840_ = v___x_865_;
goto v___jp_839_;
}
}
}
}
else
{
return v_b_838_;
}
v___jp_839_:
{
size_t v___x_841_; size_t v___x_842_; 
v___x_841_ = ((size_t)1ULL);
v___x_842_ = lean_usize_add(v_i_836_, v___x_841_);
v_i_836_ = v___x_842_;
v_b_838_ = v___y_840_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Rewrites_evalExact_spec__10_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_833_ = stack[0].m_num;
uint8_t v___x_834_ = stack[1].m_num;
lean_object* v_as_835_ = stack[2].m_obj;
size_t v_i_836_ = stack[3].m_num;
size_t v_stop_837_ = stack[4].m_num;
lean_object* v_b_838_ = stack[5].m_obj;
lean_object* v_res_869_;
v_res_869_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Rewrites_evalExact_spec__10(v___x_833_, v___x_834_, v_as_835_, v_i_836_, v_stop_837_, v_b_838_);
stack->m_obj
 = v_res_869_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Rewrites_evalExact_spec__10___boxed(lean_object* v___x_870_, lean_object* v___x_871_, lean_object* v_as_872_, lean_object* v_i_873_, lean_object* v_stop_874_, lean_object* v_b_875_){
_start:
{
uint8_t v___x_23127__boxed_876_; uint8_t v___x_23128__boxed_877_; size_t v_i_boxed_878_; size_t v_stop_boxed_879_; lean_object* v_res_880_; 
v___x_23127__boxed_876_ = lean_unbox(v___x_870_);
v___x_23128__boxed_877_ = lean_unbox(v___x_871_);
v_i_boxed_878_ = lean_unbox_usize(v_i_873_);
lean_dec(v_i_873_);
v_stop_boxed_879_ = lean_unbox_usize(v_stop_874_);
lean_dec(v_stop_874_);
v_res_880_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Rewrites_evalExact_spec__10(v___x_23127__boxed_876_, v___x_23128__boxed_877_, v_as_872_, v_i_boxed_878_, v_stop_boxed_879_, v_b_875_);
lean_dec_ref(v_as_872_);
return v_res_880_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Rewrites_evalExact_spec__8(lean_object* v_as_881_, size_t v_i_882_, size_t v_stop_883_, lean_object* v_b_884_){
_start:
{
uint8_t v___x_885_; 
v___x_885_ = lean_usize_dec_eq(v_i_882_, v_stop_883_);
if (v___x_885_ == 0)
{
lean_object* v___x_886_; lean_object* v___x_887_; size_t v___x_888_; size_t v___x_889_; 
v___x_886_ = lean_array_uget_borrowed(v_as_881_, v_i_882_);
lean_inc(v___x_886_);
v___x_887_ = l_Lean_NameSet_insert(v_b_884_, v___x_886_);
v___x_888_ = ((size_t)1ULL);
v___x_889_ = lean_usize_add(v_i_882_, v___x_888_);
v_i_882_ = v___x_889_;
v_b_884_ = v___x_887_;
goto _start;
}
else
{
return v_b_884_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Rewrites_evalExact_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_881_ = stack[0].m_obj;
size_t v_i_882_ = stack[1].m_num;
size_t v_stop_883_ = stack[2].m_num;
lean_object* v_b_884_ = stack[3].m_obj;
lean_object* v_res_891_;
v_res_891_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Rewrites_evalExact_spec__8(v_as_881_, v_i_882_, v_stop_883_, v_b_884_);
stack->m_obj
 = v_res_891_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Rewrites_evalExact_spec__8___boxed(lean_object* v_as_892_, lean_object* v_i_893_, lean_object* v_stop_894_, lean_object* v_b_895_){
_start:
{
size_t v_i_boxed_896_; size_t v_stop_boxed_897_; lean_object* v_res_898_; 
v_i_boxed_896_ = lean_unbox_usize(v_i_893_);
lean_dec(v_i_893_);
v_stop_boxed_897_ = lean_unbox_usize(v_stop_894_);
lean_dec(v_stop_894_);
v_res_898_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Rewrites_evalExact_spec__8(v_as_892_, v_i_boxed_896_, v_stop_boxed_897_, v_b_895_);
lean_dec_ref(v_as_892_);
return v_res_898_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__9(size_t v_sz_902_, size_t v_i_903_, lean_object* v_bs_904_){
_start:
{
uint8_t v___x_905_; 
v___x_905_ = lean_usize_dec_lt(v_i_903_, v_sz_902_);
if (v___x_905_ == 0)
{
lean_object* v___x_906_; 
v___x_906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_906_, 0, v_bs_904_);
return v___x_906_;
}
else
{
lean_object* v_v_907_; lean_object* v___x_908_; uint8_t v___x_909_; 
v_v_907_ = lean_array_uget(v_bs_904_, v_i_903_);
v___x_908_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__9___closed__1));
lean_inc(v_v_907_);
v___x_909_ = l_Lean_Syntax_isOfKind(v_v_907_, v___x_908_);
if (v___x_909_ == 0)
{
lean_object* v___x_910_; 
lean_dec(v_v_907_);
lean_dec_ref(v_bs_904_);
v___x_910_ = lean_box(0);
return v___x_910_;
}
else
{
lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v_bs_x27_913_; lean_object* v_forbidden_914_; size_t v___x_915_; size_t v___x_916_; lean_object* v___x_917_; 
v___x_911_ = lean_unsigned_to_nat(1u);
v___x_912_ = lean_unsigned_to_nat(0u);
v_bs_x27_913_ = lean_array_uset(v_bs_904_, v_i_903_, v___x_912_);
v_forbidden_914_ = l_Lean_Syntax_getArg(v_v_907_, v___x_911_);
lean_dec(v_v_907_);
v___x_915_ = ((size_t)1ULL);
v___x_916_ = lean_usize_add(v_i_903_, v___x_915_);
v___x_917_ = lean_array_uset(v_bs_x27_913_, v_i_903_, v_forbidden_914_);
v_i_903_ = v___x_916_;
v_bs_904_ = v___x_917_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__9_0interp(lean_interpreter_value* stack)
{
size_t v_sz_902_ = stack[0].m_num;
size_t v_i_903_ = stack[1].m_num;
lean_object* v_bs_904_ = stack[2].m_obj;
lean_object* v_res_919_;
v_res_919_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__9(v_sz_902_, v_i_903_, v_bs_904_);
stack->m_obj
 = v_res_919_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__9___boxed(lean_object* v_sz_920_, lean_object* v_i_921_, lean_object* v_bs_922_){
_start:
{
size_t v_sz_boxed_923_; size_t v_i_boxed_924_; lean_object* v_res_925_; 
v_sz_boxed_923_ = lean_unbox_usize(v_sz_920_);
lean_dec(v_sz_920_);
v_i_boxed_924_ = lean_unbox_usize(v_i_921_);
lean_dec(v_i_921_);
v_res_925_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__9(v_sz_boxed_923_, v_i_boxed_924_, v_bs_922_);
return v_res_925_;
}
}
lean_object* l_Lean_Elab_Rewrites_evalExact(lean_object* v_stx_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_){
_start:
{
lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; uint8_t v___x_963_; 
v___x_959_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___closed__0));
v___x_960_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___closed__1));
v___x_961_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___closed__2));
v___x_962_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___closed__4));
lean_inc(v_stx_949_);
v___x_963_ = l_Lean_Syntax_isOfKind(v_stx_949_, v___x_962_);
if (v___x_963_ == 0)
{
lean_object* v___x_964_; 
lean_dec(v_stx_949_);
v___x_964_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__1___redArg();
return v___x_964_;
}
else
{
lean_object* v___f_965_; lean_object* v___y_967_; lean_object* v___y_968_; lean_object* v___y_969_; lean_object* v___y_970_; lean_object* v___y_971_; lean_object* v___y_972_; lean_object* v___y_973_; lean_object* v___y_974_; lean_object* v___y_975_; lean_object* v___y_976_; lean_object* v___y_977_; lean_object* v___x_981_; lean_object* v_tk_982_; lean_object* v___y_984_; lean_object* v___y_985_; lean_object* v___y_986_; lean_object* v___y_987_; lean_object* v___y_988_; lean_object* v___y_989_; lean_object* v___y_990_; lean_object* v___y_991_; lean_object* v___y_992_; lean_object* v___y_993_; lean_object* v___y_994_; lean_object* v___y_1021_; lean_object* v___y_1022_; lean_object* v___y_1023_; lean_object* v___y_1024_; lean_object* v___y_1025_; lean_object* v___y_1026_; lean_object* v___y_1027_; lean_object* v___y_1028_; lean_object* v___y_1029_; lean_object* v___y_1030_; lean_object* v___y_1031_; lean_object* v___y_1032_; lean_object* v___y_1044_; lean_object* v_forbidden_1045_; lean_object* v___y_1046_; lean_object* v___y_1047_; lean_object* v___y_1048_; lean_object* v___y_1049_; lean_object* v___y_1050_; lean_object* v___y_1051_; lean_object* v___y_1052_; lean_object* v___y_1053_; lean_object* v___y_1068_; lean_object* v___y_1069_; lean_object* v___y_1070_; lean_object* v___y_1071_; lean_object* v___y_1072_; lean_object* v___y_1073_; lean_object* v___y_1074_; lean_object* v___y_1075_; lean_object* v___y_1076_; lean_object* v___y_1077_; lean_object* v___x_1082_; lean_object* v_loc_1084_; lean_object* v___y_1085_; lean_object* v___y_1086_; lean_object* v___y_1087_; lean_object* v___y_1088_; lean_object* v___y_1089_; lean_object* v___y_1090_; lean_object* v___y_1091_; lean_object* v___y_1092_; lean_object* v___x_1114_; uint8_t v___x_1115_; 
v___f_965_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___closed__5));
v___x_981_ = lean_unsigned_to_nat(0u);
v_tk_982_ = l_Lean_Syntax_getArg(v_stx_949_, v___x_981_);
v___x_1082_ = lean_unsigned_to_nat(1u);
v___x_1114_ = l_Lean_Syntax_getArg(v_stx_949_, v___x_1082_);
v___x_1115_ = l_Lean_Syntax_isNone(v___x_1114_);
if (v___x_1115_ == 0)
{
uint8_t v___x_1116_; 
lean_inc(v___x_1114_);
v___x_1116_ = l_Lean_Syntax_matchesNull(v___x_1114_, v___x_1082_);
if (v___x_1116_ == 0)
{
lean_object* v___x_1117_; 
lean_dec(v___x_1114_);
lean_dec(v_tk_982_);
lean_dec(v_stx_949_);
v___x_1117_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__1___redArg();
return v___x_1117_;
}
else
{
lean_object* v_loc_1118_; lean_object* v___x_1119_; 
v_loc_1118_ = l_Lean_Syntax_getArg(v___x_1114_, v___x_981_);
lean_dec(v___x_1114_);
v___x_1119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1119_, 0, v_loc_1118_);
v_loc_1084_ = v___x_1119_;
v___y_1085_ = v_a_950_;
v___y_1086_ = v_a_951_;
v___y_1087_ = v_a_952_;
v___y_1088_ = v_a_953_;
v___y_1089_ = v_a_954_;
v___y_1090_ = v_a_955_;
v___y_1091_ = v_a_956_;
v___y_1092_ = v_a_957_;
goto v___jp_1083_;
}
}
else
{
lean_object* v___x_1120_; 
lean_dec(v___x_1114_);
v___x_1120_ = lean_box(0);
v_loc_1084_ = v___x_1120_;
v___y_1085_ = v_a_950_;
v___y_1086_ = v_a_951_;
v___y_1087_ = v_a_952_;
v___y_1088_ = v_a_953_;
v___y_1089_ = v_a_954_;
v___y_1090_ = v_a_955_;
v___y_1091_ = v_a_956_;
v___y_1092_ = v_a_957_;
goto v___jp_1083_;
}
v___jp_966_:
{
lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; 
v___x_978_ = l_Lean_mkOptionalNode(v___y_977_);
v___x_979_ = l_Lean_Elab_Tactic_expandOptLocation(v___x_978_);
lean_dec(v___x_978_);
v___x_980_ = l_Lean_Elab_Tactic_withLocation(v___x_979_, v___y_976_, v___y_975_, v___f_965_, v___y_972_, v___y_973_, v___y_969_, v___y_970_, v___y_967_, v___y_971_, v___y_968_, v___y_974_);
lean_dec(v___x_979_);
return v___x_980_;
}
v___jp_983_:
{
lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; 
v___x_995_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___closed__7));
v___x_996_ = lean_unsigned_to_nat(90u);
v___x_997_ = l_Lean_reportOutOfHeartbeats(v___x_995_, v_tk_982_, v___x_996_, v___y_986_, v___y_993_);
if (lean_obj_tag(v___x_997_) == 0)
{
lean_object* v___x_998_; 
lean_dec_ref_known(v___x_997_, 1);
v___x_998_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_992_, v___y_985_, v___y_991_, v___y_986_, v___y_993_);
if (lean_obj_tag(v___x_998_) == 0)
{
lean_object* v_a_999_; lean_object* v___f_1000_; lean_object* v___x_1001_; lean_object* v___f_1002_; 
v_a_999_ = lean_ctor_get(v___x_998_, 0);
lean_inc_n(v_a_999_, 2);
lean_dec_ref_known(v___x_998_, 1);
lean_inc(v_tk_982_);
lean_inc(v___y_994_);
lean_inc(v___y_984_);
v___f_1000_ = lean_alloc_closure((void*)(l_Lean_Elab_Rewrites_evalExact___lam__2___boxed), 16, 6);
lean_closure_set(v___f_1000_, 0, v___y_984_);
lean_closure_set(v___f_1000_, 1, v_a_999_);
lean_closure_set(v___f_1000_, 2, v___y_994_);
lean_closure_set(v___f_1000_, 3, v_tk_982_);
lean_closure_set(v___f_1000_, 4, v___x_981_);
lean_closure_set(v___f_1000_, 5, v___x_996_);
v___x_1001_ = lean_box(v___x_963_);
v___f_1002_ = lean_alloc_closure((void*)(l_Lean_Elab_Rewrites_evalExact___lam__3___boxed), 19, 10);
lean_closure_set(v___f_1002_, 0, v_a_999_);
lean_closure_set(v___f_1002_, 1, v___y_984_);
lean_closure_set(v___f_1002_, 2, v___y_994_);
lean_closure_set(v___f_1002_, 3, v___x_1001_);
lean_closure_set(v___f_1002_, 4, v___x_981_);
lean_closure_set(v___f_1002_, 5, v___x_959_);
lean_closure_set(v___f_1002_, 6, v___x_960_);
lean_closure_set(v___f_1002_, 7, v___x_961_);
lean_closure_set(v___f_1002_, 8, v_tk_982_);
lean_closure_set(v___f_1002_, 9, v___x_996_);
if (lean_obj_tag(v___y_988_) == 0)
{
lean_object* v___x_1003_; 
v___x_1003_ = lean_box(0);
v___y_967_ = v___y_985_;
v___y_968_ = v___y_986_;
v___y_969_ = v___y_987_;
v___y_970_ = v___y_989_;
v___y_971_ = v___y_991_;
v___y_972_ = v___y_990_;
v___y_973_ = v___y_992_;
v___y_974_ = v___y_993_;
v___y_975_ = v___f_1002_;
v___y_976_ = v___f_1000_;
v___y_977_ = v___x_1003_;
goto v___jp_966_;
}
else
{
lean_object* v_val_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1011_; 
v_val_1004_ = lean_ctor_get(v___y_988_, 0);
v_isSharedCheck_1011_ = !lean_is_exclusive(v___y_988_);
if (v_isSharedCheck_1011_ == 0)
{
v___x_1006_ = v___y_988_;
v_isShared_1007_ = v_isSharedCheck_1011_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_val_1004_);
lean_dec(v___y_988_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1011_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
lean_object* v___x_1009_; 
if (v_isShared_1007_ == 0)
{
v___x_1009_ = v___x_1006_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v_val_1004_);
v___x_1009_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
v___y_967_ = v___y_985_;
v___y_968_ = v___y_986_;
v___y_969_ = v___y_987_;
v___y_970_ = v___y_989_;
v___y_971_ = v___y_991_;
v___y_972_ = v___y_990_;
v___y_973_ = v___y_992_;
v___y_974_ = v___y_993_;
v___y_975_ = v___f_1002_;
v___y_976_ = v___f_1000_;
v___y_977_ = v___x_1009_;
goto v___jp_966_;
}
}
}
}
else
{
lean_object* v_a_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1019_; 
lean_dec(v___y_994_);
lean_dec(v___y_988_);
lean_dec(v___y_984_);
lean_dec(v_tk_982_);
v_a_1012_ = lean_ctor_get(v___x_998_, 0);
v_isSharedCheck_1019_ = !lean_is_exclusive(v___x_998_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_1014_ = v___x_998_;
v_isShared_1015_ = v_isSharedCheck_1019_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_a_1012_);
lean_dec(v___x_998_);
v___x_1014_ = lean_box(0);
v_isShared_1015_ = v_isSharedCheck_1019_;
goto v_resetjp_1013_;
}
v_resetjp_1013_:
{
lean_object* v___x_1017_; 
if (v_isShared_1015_ == 0)
{
v___x_1017_ = v___x_1014_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v_a_1012_);
v___x_1017_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
return v___x_1017_;
}
}
}
}
else
{
lean_dec(v___y_994_);
lean_dec(v___y_988_);
lean_dec(v___y_984_);
lean_dec(v_tk_982_);
return v___x_997_;
}
}
v___jp_1020_:
{
size_t v_sz_1033_; size_t v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; uint8_t v___x_1037_; 
v_sz_1033_ = lean_array_size(v___y_1032_);
v___x_1034_ = ((size_t)0ULL);
v___x_1035_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__7(v_sz_1033_, v___x_1034_, v___y_1032_);
v___x_1036_ = lean_array_get_size(v___x_1035_);
v___x_1037_ = lean_nat_dec_lt(v___x_981_, v___x_1036_);
if (v___x_1037_ == 0)
{
lean_dec_ref(v___x_1035_);
lean_inc(v___y_1027_);
v___y_984_ = v___y_1021_;
v___y_985_ = v___y_1022_;
v___y_986_ = v___y_1023_;
v___y_987_ = v___y_1024_;
v___y_988_ = v___y_1026_;
v___y_989_ = v___y_1025_;
v___y_990_ = v___y_1029_;
v___y_991_ = v___y_1028_;
v___y_992_ = v___y_1030_;
v___y_993_ = v___y_1031_;
v___y_994_ = v___y_1027_;
goto v___jp_983_;
}
else
{
uint8_t v___x_1038_; 
v___x_1038_ = lean_nat_dec_le(v___x_1036_, v___x_1036_);
if (v___x_1038_ == 0)
{
if (v___x_1037_ == 0)
{
lean_dec_ref(v___x_1035_);
lean_inc(v___y_1027_);
v___y_984_ = v___y_1021_;
v___y_985_ = v___y_1022_;
v___y_986_ = v___y_1023_;
v___y_987_ = v___y_1024_;
v___y_988_ = v___y_1026_;
v___y_989_ = v___y_1025_;
v___y_990_ = v___y_1029_;
v___y_991_ = v___y_1028_;
v___y_992_ = v___y_1030_;
v___y_993_ = v___y_1031_;
v___y_994_ = v___y_1027_;
goto v___jp_983_;
}
else
{
size_t v___x_1039_; lean_object* v___x_1040_; 
v___x_1039_ = lean_usize_of_nat(v___x_1036_);
lean_inc(v___y_1027_);
v___x_1040_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Rewrites_evalExact_spec__8(v___x_1035_, v___x_1034_, v___x_1039_, v___y_1027_);
lean_dec_ref(v___x_1035_);
v___y_984_ = v___y_1021_;
v___y_985_ = v___y_1022_;
v___y_986_ = v___y_1023_;
v___y_987_ = v___y_1024_;
v___y_988_ = v___y_1026_;
v___y_989_ = v___y_1025_;
v___y_990_ = v___y_1029_;
v___y_991_ = v___y_1028_;
v___y_992_ = v___y_1030_;
v___y_993_ = v___y_1031_;
v___y_994_ = v___x_1040_;
goto v___jp_983_;
}
}
else
{
size_t v___x_1041_; lean_object* v___x_1042_; 
v___x_1041_ = lean_usize_of_nat(v___x_1036_);
lean_inc(v___y_1027_);
v___x_1042_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Rewrites_evalExact_spec__8(v___x_1035_, v___x_1034_, v___x_1041_, v___y_1027_);
lean_dec_ref(v___x_1035_);
v___y_984_ = v___y_1021_;
v___y_985_ = v___y_1022_;
v___y_986_ = v___y_1023_;
v___y_987_ = v___y_1024_;
v___y_988_ = v___y_1026_;
v___y_989_ = v___y_1025_;
v___y_990_ = v___y_1029_;
v___y_991_ = v___y_1028_;
v___y_992_ = v___y_1030_;
v___y_993_ = v___y_1031_;
v___y_994_ = v___x_1042_;
goto v___jp_983_;
}
}
}
v___jp_1043_:
{
lean_object* v___x_1054_; 
v___x_1054_ = l_Lean_Meta_Rewrites_createModuleTreeRef(v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_);
if (lean_obj_tag(v___x_1054_) == 0)
{
lean_object* v_a_1055_; lean_object* v___x_1056_; 
v_a_1055_ = lean_ctor_get(v___x_1054_, 0);
lean_inc(v_a_1055_);
lean_dec_ref_known(v___x_1054_, 1);
v___x_1056_ = l_Lean_NameSet_empty;
if (lean_obj_tag(v_forbidden_1045_) == 0)
{
lean_object* v___x_1057_; 
v___x_1057_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___closed__8));
v___y_1021_ = v_a_1055_;
v___y_1022_ = v___y_1050_;
v___y_1023_ = v___y_1052_;
v___y_1024_ = v___y_1048_;
v___y_1025_ = v___y_1049_;
v___y_1026_ = v___y_1044_;
v___y_1027_ = v___x_1056_;
v___y_1028_ = v___y_1051_;
v___y_1029_ = v___y_1046_;
v___y_1030_ = v___y_1047_;
v___y_1031_ = v___y_1053_;
v___y_1032_ = v___x_1057_;
goto v___jp_1020_;
}
else
{
lean_object* v_val_1058_; 
v_val_1058_ = lean_ctor_get(v_forbidden_1045_, 0);
lean_inc(v_val_1058_);
lean_dec_ref_known(v_forbidden_1045_, 1);
v___y_1021_ = v_a_1055_;
v___y_1022_ = v___y_1050_;
v___y_1023_ = v___y_1052_;
v___y_1024_ = v___y_1048_;
v___y_1025_ = v___y_1049_;
v___y_1026_ = v___y_1044_;
v___y_1027_ = v___x_1056_;
v___y_1028_ = v___y_1051_;
v___y_1029_ = v___y_1046_;
v___y_1030_ = v___y_1047_;
v___y_1031_ = v___y_1053_;
v___y_1032_ = v_val_1058_;
goto v___jp_1020_;
}
}
else
{
lean_object* v_a_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1066_; 
lean_dec(v_forbidden_1045_);
lean_dec(v___y_1044_);
lean_dec(v_tk_982_);
v_a_1059_ = lean_ctor_get(v___x_1054_, 0);
v_isSharedCheck_1066_ = !lean_is_exclusive(v___x_1054_);
if (v_isSharedCheck_1066_ == 0)
{
v___x_1061_ = v___x_1054_;
v_isShared_1062_ = v_isSharedCheck_1066_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_a_1059_);
lean_dec(v___x_1054_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1066_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
lean_object* v___x_1064_; 
if (v_isShared_1062_ == 0)
{
v___x_1064_ = v___x_1061_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v_a_1059_);
v___x_1064_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1063_;
}
v_reusejp_1063_:
{
return v___x_1064_;
}
}
}
}
v___jp_1067_:
{
size_t v_sz_1078_; size_t v___x_1079_; lean_object* v___x_1080_; 
v_sz_1078_ = lean_array_size(v___y_1077_);
v___x_1079_ = ((size_t)0ULL);
v___x_1080_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__9(v_sz_1078_, v___x_1079_, v___y_1077_);
if (lean_obj_tag(v___x_1080_) == 0)
{
lean_object* v___x_1081_; 
lean_dec(v___y_1075_);
lean_dec(v_tk_982_);
v___x_1081_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__1___redArg();
return v___x_1081_;
}
else
{
v___y_1044_ = v___y_1075_;
v_forbidden_1045_ = v___x_1080_;
v___y_1046_ = v___y_1071_;
v___y_1047_ = v___y_1074_;
v___y_1048_ = v___y_1076_;
v___y_1049_ = v___y_1069_;
v___y_1050_ = v___y_1073_;
v___y_1051_ = v___y_1070_;
v___y_1052_ = v___y_1068_;
v___y_1053_ = v___y_1072_;
goto v___jp_1043_;
}
}
v___jp_1083_:
{
lean_object* v___x_1093_; lean_object* v___x_1094_; uint8_t v___x_1095_; 
v___x_1093_ = lean_unsigned_to_nat(2u);
v___x_1094_ = l_Lean_Syntax_getArg(v_stx_949_, v___x_1093_);
lean_dec(v_stx_949_);
v___x_1095_ = l_Lean_Syntax_isNone(v___x_1094_);
if (v___x_1095_ == 0)
{
uint8_t v___x_1096_; 
lean_inc(v___x_1094_);
v___x_1096_ = l_Lean_Syntax_matchesNull(v___x_1094_, v___x_1082_);
if (v___x_1096_ == 0)
{
lean_object* v___x_1097_; 
lean_dec(v___x_1094_);
lean_dec(v_loc_1084_);
lean_dec(v_tk_982_);
v___x_1097_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__1___redArg();
return v___x_1097_;
}
else
{
lean_object* v___x_1098_; lean_object* v___x_1099_; uint8_t v___x_1100_; 
v___x_1098_ = l_Lean_Syntax_getArg(v___x_1094_, v___x_981_);
lean_dec(v___x_1094_);
v___x_1099_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___closed__10));
lean_inc(v___x_1098_);
v___x_1100_ = l_Lean_Syntax_isOfKind(v___x_1098_, v___x_1099_);
if (v___x_1100_ == 0)
{
lean_object* v___x_1101_; 
lean_dec(v___x_1098_);
lean_dec(v_loc_1084_);
lean_dec(v_tk_982_);
v___x_1101_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__1___redArg();
return v___x_1101_;
}
else
{
lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; uint8_t v___x_1106_; 
v___x_1102_ = l_Lean_Syntax_getArg(v___x_1098_, v___x_1082_);
lean_dec(v___x_1098_);
v___x_1103_ = l_Lean_Syntax_getArgs(v___x_1102_);
lean_dec(v___x_1102_);
v___x_1104_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___closed__11));
v___x_1105_ = lean_array_get_size(v___x_1103_);
v___x_1106_ = lean_nat_dec_lt(v___x_981_, v___x_1105_);
if (v___x_1106_ == 0)
{
lean_dec_ref(v___x_1103_);
v___y_1068_ = v___y_1091_;
v___y_1069_ = v___y_1088_;
v___y_1070_ = v___y_1090_;
v___y_1071_ = v___y_1085_;
v___y_1072_ = v___y_1092_;
v___y_1073_ = v___y_1089_;
v___y_1074_ = v___y_1086_;
v___y_1075_ = v_loc_1084_;
v___y_1076_ = v___y_1087_;
v___y_1077_ = v___x_1104_;
goto v___jp_1067_;
}
else
{
lean_object* v___x_1107_; lean_object* v___x_1108_; size_t v___x_1109_; size_t v___x_1110_; lean_object* v___x_1111_; lean_object* v_snd_1112_; 
v___x_1107_ = lean_box(v___x_1106_);
v___x_1108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1108_, 0, v___x_1107_);
lean_ctor_set(v___x_1108_, 1, v___x_1104_);
v___x_1109_ = ((size_t)0ULL);
v___x_1110_ = lean_usize_of_nat(v___x_1105_);
v___x_1111_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Rewrites_evalExact_spec__10(v___x_1100_, v___x_1095_, v___x_1103_, v___x_1109_, v___x_1110_, v___x_1108_);
lean_dec_ref(v___x_1103_);
v_snd_1112_ = lean_ctor_get(v___x_1111_, 1);
lean_inc(v_snd_1112_);
lean_dec_ref(v___x_1111_);
v___y_1068_ = v___y_1091_;
v___y_1069_ = v___y_1088_;
v___y_1070_ = v___y_1090_;
v___y_1071_ = v___y_1085_;
v___y_1072_ = v___y_1092_;
v___y_1073_ = v___y_1089_;
v___y_1074_ = v___y_1086_;
v___y_1075_ = v_loc_1084_;
v___y_1076_ = v___y_1087_;
v___y_1077_ = v_snd_1112_;
goto v___jp_1067_;
}
}
}
}
else
{
lean_object* v___x_1113_; 
lean_dec(v___x_1094_);
v___x_1113_ = lean_box(0);
v___y_1044_ = v_loc_1084_;
v_forbidden_1045_ = v___x_1113_;
v___y_1046_ = v___y_1085_;
v___y_1047_ = v___y_1086_;
v___y_1048_ = v___y_1087_;
v___y_1049_ = v___y_1088_;
v___y_1050_ = v___y_1089_;
v___y_1051_ = v___y_1090_;
v___y_1052_ = v___y_1091_;
v___y_1053_ = v___y_1092_;
goto v___jp_1043_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Rewrites_evalExact_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_949_ = stack[0].m_obj;
lean_object* v_a_950_ = stack[1].m_obj;
lean_object* v_a_951_ = stack[2].m_obj;
lean_object* v_a_952_ = stack[3].m_obj;
lean_object* v_a_953_ = stack[4].m_obj;
lean_object* v_a_954_ = stack[5].m_obj;
lean_object* v_a_955_ = stack[6].m_obj;
lean_object* v_a_956_ = stack[7].m_obj;
lean_object* v_a_957_ = stack[8].m_obj;
lean_object* v_res_1121_;
v_res_1121_ = l_Lean_Elab_Rewrites_evalExact(v_stx_949_, v_a_950_, v_a_951_, v_a_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_, v_a_957_);
stack->m_obj
 = v_res_1121_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact___boxed(lean_object* v_stx_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_){
_start:
{
lean_object* v_res_1132_; 
v_res_1132_ = l_Lean_Elab_Rewrites_evalExact(v_stx_1122_, v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_);
lean_dec(v_a_1130_);
lean_dec_ref(v_a_1129_);
lean_dec(v_a_1128_);
lean_dec_ref(v_a_1127_);
lean_dec(v_a_1126_);
lean_dec_ref(v_a_1125_);
lean_dec(v_a_1124_);
lean_dec_ref(v_a_1123_);
return v_res_1132_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__0(lean_object* v_00_u03b1_1133_, lean_object* v_msg_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_){
_start:
{
lean_object* v___x_1144_; 
v___x_1144_ = l_Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__0___redArg(v_msg_1134_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_);
return v___x_1144_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1134_ = stack[1].m_obj;
lean_object* v___y_1135_ = stack[2].m_obj;
lean_object* v___y_1136_ = stack[3].m_obj;
lean_object* v___y_1137_ = stack[4].m_obj;
lean_object* v___y_1138_ = stack[5].m_obj;
lean_object* v___y_1139_ = stack[6].m_obj;
lean_object* v___y_1140_ = stack[7].m_obj;
lean_object* v___y_1141_ = stack[8].m_obj;
lean_object* v___y_1142_ = stack[9].m_obj;
lean_object* v_res_1145_;
v_res_1145_ = l_Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__0(lean_box(0), v_msg_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_);
stack->m_obj
 = v_res_1145_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__0___boxed(lean_object* v_00_u03b1_1146_, lean_object* v_msg_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_){
_start:
{
lean_object* v_res_1157_; 
v_res_1157_ = l_Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__0(v_00_u03b1_1146_, v_msg_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_);
lean_dec(v___y_1155_);
lean_dec_ref(v___y_1154_);
lean_dec(v___y_1153_);
lean_dec_ref(v___y_1152_);
lean_dec(v___y_1151_);
lean_dec_ref(v___y_1150_);
lean_dec(v___y_1149_);
lean_dec_ref(v___y_1148_);
return v_res_1157_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__5(lean_object* v_f_1158_, lean_object* v_tk_1159_, lean_object* v_as_1160_, lean_object* v_as_x27_1161_, lean_object* v_b_1162_, lean_object* v_a_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_){
_start:
{
lean_object* v___x_1173_; 
v___x_1173_ = l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__5___redArg(v_f_1158_, v_tk_1159_, v_as_x27_1161_, v_b_1162_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_);
return v___x_1173_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1158_ = stack[0].m_obj;
lean_object* v_tk_1159_ = stack[1].m_obj;
lean_object* v_as_1160_ = stack[2].m_obj;
lean_object* v_as_x27_1161_ = stack[3].m_obj;
lean_object* v_b_1162_ = stack[4].m_obj;
lean_object* v___y_1164_ = stack[6].m_obj;
lean_object* v___y_1165_ = stack[7].m_obj;
lean_object* v___y_1166_ = stack[8].m_obj;
lean_object* v___y_1167_ = stack[9].m_obj;
lean_object* v___y_1168_ = stack[10].m_obj;
lean_object* v___y_1169_ = stack[11].m_obj;
lean_object* v___y_1170_ = stack[12].m_obj;
lean_object* v___y_1171_ = stack[13].m_obj;
lean_object* v_res_1174_;
v_res_1174_ = l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__5(v_f_1158_, v_tk_1159_, v_as_1160_, v_as_x27_1161_, v_b_1162_, lean_box(0), v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_);
stack->m_obj
 = v_res_1174_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__5___boxed(lean_object* v_f_1175_, lean_object* v_tk_1176_, lean_object* v_as_1177_, lean_object* v_as_x27_1178_, lean_object* v_b_1179_, lean_object* v_a_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_){
_start:
{
lean_object* v_res_1190_; 
v_res_1190_ = l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__5(v_f_1175_, v_tk_1176_, v_as_1177_, v_as_x27_1178_, v_b_1179_, v_a_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_);
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
lean_dec(v___y_1186_);
lean_dec_ref(v___y_1185_);
lean_dec(v___y_1184_);
lean_dec_ref(v___y_1183_);
lean_dec(v___y_1182_);
lean_dec_ref(v___y_1181_);
lean_dec(v_as_x27_1178_);
lean_dec(v_as_1177_);
return v_res_1190_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1(){
_start:
{
lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; 
v___x_1200_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1201_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___closed__4));
v___x_1202_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___closed__3));
v___x_1203_ = lean_alloc_closure((void*)(l_Lean_Elab_Rewrites_evalExact___boxed), 10, 0);
v___x_1204_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1200_, v___x_1201_, v___x_1202_, v___x_1203_);
return v___x_1204_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1205_;
v_res_1205_ = l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1();
stack->m_obj
 = v_res_1205_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___boxed(lean_object* v_a_1206_){
_start:
{
lean_object* v_res_1207_; 
v_res_1207_ = l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1();
return v_res_1207_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3(){
_start:
{
lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; 
v___x_1234_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___closed__3));
v___x_1235_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__6));
v___x_1236_ = l_Lean_addBuiltinDeclarationRanges(v___x_1234_, v___x_1235_);
return v___x_1236_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1237_;
v_res_1237_ = l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3();
stack->m_obj
 = v_res_1237_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___boxed(lean_object* v_a_1238_){
_start:
{
lean_object* v_res_1239_; 
v_res_1239_ = l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3();
return v_res_1239_;
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
