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
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Elab_Tactic_saveState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMCtxImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkOptionalNode(lean_object*);
lean_object* l_Lean_Elab_Tactic_expandOptLocation(lean_object*);
lean_object* l_Lean_Elab_Tactic_withLocation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__0___redArg___closed__0(void){
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
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__0___redArg(){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__0___redArg___closed__0);
v___x_6_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__0___redArg___boxed(lean_object* v___y_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__0___redArg();
return v_res_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__0(lean_object* v_00_u03b1_9_, lean_object* v___y_10_, lean_object* v___y_11_, lean_object* v___y_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__0___redArg();
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__0___boxed(lean_object* v_00_u03b1_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__0(v_00_u03b1_20_, v___y_21_, v___y_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_, v___y_27_, v___y_28_);
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
v___x_51_ = lean_st_ref_set(v___y_32_, v___x_50_);
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__1_spec__1(lean_object* v_msgData_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_){
_start:
{
lean_object* v___x_219_; lean_object* v_env_220_; lean_object* v___x_221_; lean_object* v_mctx_222_; lean_object* v_lctx_223_; lean_object* v_options_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_219_ = lean_st_ref_get(v___y_217_);
v_env_220_ = lean_ctor_get(v___x_219_, 0);
lean_inc_ref(v_env_220_);
lean_dec(v___x_219_);
v___x_221_ = lean_st_ref_get(v___y_215_);
v_mctx_222_ = lean_ctor_get(v___x_221_, 0);
lean_inc_ref(v_mctx_222_);
lean_dec(v___x_221_);
v_lctx_223_ = lean_ctor_get(v___y_214_, 2);
v_options_224_ = lean_ctor_get(v___y_216_, 2);
lean_inc_ref(v_options_224_);
lean_inc_ref(v_lctx_223_);
v___x_225_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_225_, 0, v_env_220_);
lean_ctor_set(v___x_225_, 1, v_mctx_222_);
lean_ctor_set(v___x_225_, 2, v_lctx_223_);
lean_ctor_set(v___x_225_, 3, v_options_224_);
v___x_226_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_226_, 0, v___x_225_);
lean_ctor_set(v___x_226_, 1, v_msgData_213_);
v___x_227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_227_, 0, v___x_226_);
return v___x_227_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__1_spec__1___boxed(lean_object* v_msgData_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_){
_start:
{
lean_object* v_res_234_; 
v_res_234_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__1_spec__1(v_msgData_228_, v___y_229_, v___y_230_, v___y_231_, v___y_232_);
lean_dec(v___y_232_);
lean_dec_ref(v___y_231_);
lean_dec(v___y_230_);
lean_dec_ref(v___y_229_);
return v_res_234_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__1___redArg(lean_object* v_msg_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_){
_start:
{
lean_object* v_ref_241_; lean_object* v___x_242_; lean_object* v_a_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_251_; 
v_ref_241_ = lean_ctor_get(v___y_238_, 5);
v___x_242_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__1_spec__1(v_msg_235_, v___y_236_, v___y_237_, v___y_238_, v___y_239_);
v_a_243_ = lean_ctor_get(v___x_242_, 0);
v_isSharedCheck_251_ = !lean_is_exclusive(v___x_242_);
if (v_isSharedCheck_251_ == 0)
{
v___x_245_ = v___x_242_;
v_isShared_246_ = v_isSharedCheck_251_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_a_243_);
lean_dec(v___x_242_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_251_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v___x_247_; lean_object* v___x_249_; 
lean_inc(v_ref_241_);
v___x_247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_247_, 0, v_ref_241_);
lean_ctor_set(v___x_247_, 1, v_a_243_);
if (v_isShared_246_ == 0)
{
lean_ctor_set_tag(v___x_245_, 1);
lean_ctor_set(v___x_245_, 0, v___x_247_);
v___x_249_ = v___x_245_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v___x_247_);
v___x_249_ = v_reuseFailAlloc_250_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
return v___x_249_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__1___redArg___boxed(lean_object* v_msg_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l_Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__1___redArg(v_msg_252_, v___y_253_, v___y_254_, v___y_255_, v___y_256_);
lean_dec(v___y_256_);
lean_dec_ref(v___y_255_);
lean_dec(v___y_254_);
lean_dec_ref(v___y_253_);
return v_res_258_;
}
}
static lean_object* _init_l_Lean_Elab_Rewrites_evalExact___lam__0___closed__1(void){
_start:
{
lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_260_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___lam__0___closed__0));
v___x_261_ = l_Lean_stringToMessageData(v___x_260_);
return v___x_261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact___lam__0(lean_object* v_x_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_){
_start:
{
lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_272_ = lean_obj_once(&l_Lean_Elab_Rewrites_evalExact___lam__0___closed__1, &l_Lean_Elab_Rewrites_evalExact___lam__0___closed__1_once, _init_l_Lean_Elab_Rewrites_evalExact___lam__0___closed__1);
v___x_273_ = l_Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__1___redArg(v___x_272_, v___y_267_, v___y_268_, v___y_269_, v___y_270_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact___lam__0___boxed(lean_object* v_x_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l_Lean_Elab_Rewrites_evalExact___lam__0(v_x_274_, v___y_275_, v___y_276_, v___y_277_, v___y_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_);
lean_dec(v___y_282_);
lean_dec_ref(v___y_281_);
lean_dec(v___y_280_);
lean_dec_ref(v___y_279_);
lean_dec(v___y_278_);
lean_dec_ref(v___y_277_);
lean_dec(v___y_276_);
lean_dec_ref(v___y_275_);
lean_dec(v_x_274_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact___lam__1(lean_object* v_eqProof_285_, lean_object* v___x_286_, lean_object* v_eNew_287_, lean_object* v_a_288_, lean_object* v_f_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_){
_start:
{
lean_object* v___x_295_; 
v___x_295_ = l_Lean_Meta_mkEqMP(v_eqProof_285_, v___x_286_, v___y_290_, v___y_291_, v___y_292_, v___y_293_);
if (lean_obj_tag(v___x_295_) == 0)
{
lean_object* v_a_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
v_a_296_ = lean_ctor_get(v___x_295_, 0);
lean_inc(v_a_296_);
lean_dec_ref(v___x_295_);
v___x_297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_297_, 0, v_eNew_287_);
v___x_298_ = lean_box(0);
v___x_299_ = l_Lean_MVarId_replace(v_a_288_, v_f_289_, v_a_296_, v___x_297_, v___x_298_, v___y_290_, v___y_291_, v___y_292_, v___y_293_);
return v___x_299_;
}
else
{
lean_object* v_a_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_307_; 
lean_dec(v_f_289_);
lean_dec(v_a_288_);
lean_dec_ref(v_eNew_287_);
v_a_300_ = lean_ctor_get(v___x_295_, 0);
v_isSharedCheck_307_ = !lean_is_exclusive(v___x_295_);
if (v_isSharedCheck_307_ == 0)
{
v___x_302_ = v___x_295_;
v_isShared_303_ = v_isSharedCheck_307_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_a_300_);
lean_dec(v___x_295_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_307_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v___x_305_; 
if (v_isShared_303_ == 0)
{
v___x_305_ = v___x_302_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v_a_300_);
v___x_305_ = v_reuseFailAlloc_306_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
return v___x_305_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact___lam__1___boxed(lean_object* v_eqProof_308_, lean_object* v___x_309_, lean_object* v_eNew_310_, lean_object* v_a_311_, lean_object* v_f_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_){
_start:
{
lean_object* v_res_318_; 
v_res_318_ = l_Lean_Elab_Rewrites_evalExact___lam__1(v_eqProof_308_, v___x_309_, v_eNew_310_, v_a_311_, v_f_312_, v___y_313_, v___y_314_, v___y_315_, v___y_316_);
lean_dec(v___y_316_);
lean_dec_ref(v___y_315_);
lean_dec(v___y_314_);
lean_dec_ref(v___y_313_);
return v_res_318_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__5___redArg___lam__0(lean_object* v_result_319_, lean_object* v_expr_320_, uint8_t v_symm_321_, lean_object* v_f_322_, lean_object* v_tk_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_){
_start:
{
lean_object* v___x_333_; 
v___x_333_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_325_, v___y_327_, v___y_329_, v___y_331_);
if (lean_obj_tag(v___x_333_) == 0)
{
lean_object* v_a_334_; lean_object* v_ref_335_; lean_object* v_eNew_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v_a_334_ = lean_ctor_get(v___x_333_, 0);
lean_inc(v_a_334_);
lean_dec_ref(v___x_333_);
v_ref_335_ = lean_ctor_get(v___y_330_, 5);
v_eNew_336_ = lean_ctor_get(v_result_319_, 0);
v___x_337_ = lean_box(v_symm_321_);
v___x_338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_338_, 0, v_expr_320_);
lean_ctor_set(v___x_338_, 1, v___x_337_);
v___x_339_ = lean_box(0);
v___x_340_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_340_, 0, v___x_338_);
lean_ctor_set(v___x_340_, 1, v___x_339_);
lean_inc_ref(v_eNew_336_);
v___x_341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_341_, 0, v_eNew_336_);
v___x_342_ = l_Lean_Expr_fvar___override(v_f_322_);
v___x_343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_343_, 0, v___x_342_);
lean_inc(v_ref_335_);
v___x_344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_344_, 0, v_ref_335_);
v___x_345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_345_, 0, v_a_334_);
v___x_346_ = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion(v_tk_323_, v___x_340_, v___x_341_, v___x_343_, v___x_344_, v___x_345_, v___y_324_, v___y_325_, v___y_326_, v___y_327_, v___y_328_, v___y_329_, v___y_330_, v___y_331_);
return v___x_346_;
}
else
{
lean_object* v_a_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_354_; 
lean_dec(v_tk_323_);
lean_dec(v_f_322_);
lean_dec_ref(v_expr_320_);
v_a_347_ = lean_ctor_get(v___x_333_, 0);
v_isSharedCheck_354_ = !lean_is_exclusive(v___x_333_);
if (v_isSharedCheck_354_ == 0)
{
v___x_349_ = v___x_333_;
v_isShared_350_ = v_isSharedCheck_354_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_a_347_);
lean_dec(v___x_333_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_354_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
lean_object* v___x_352_; 
if (v_isShared_350_ == 0)
{
v___x_352_ = v___x_349_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v_a_347_);
v___x_352_ = v_reuseFailAlloc_353_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
return v___x_352_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__5___redArg___lam__0___boxed(lean_object* v_result_355_, lean_object* v_expr_356_, lean_object* v_symm_357_, lean_object* v_f_358_, lean_object* v_tk_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_){
_start:
{
uint8_t v_symm_boxed_369_; lean_object* v_res_370_; 
v_symm_boxed_369_ = lean_unbox(v_symm_357_);
v_res_370_ = l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__5___redArg___lam__0(v_result_355_, v_expr_356_, v_symm_boxed_369_, v_f_358_, v_tk_359_, v___y_360_, v___y_361_, v___y_362_, v___y_363_, v___y_364_, v___y_365_, v___y_366_, v___y_367_);
lean_dec(v___y_367_);
lean_dec_ref(v___y_366_);
lean_dec(v___y_365_);
lean_dec_ref(v___y_364_);
lean_dec(v___y_363_);
lean_dec_ref(v___y_362_);
lean_dec(v___y_361_);
lean_dec_ref(v___y_360_);
lean_dec_ref(v_result_355_);
return v_res_370_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__5___redArg(lean_object* v_f_371_, lean_object* v_tk_372_, lean_object* v_as_x27_373_, lean_object* v_b_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_){
_start:
{
if (lean_obj_tag(v_as_x27_373_) == 0)
{
lean_object* v___x_384_; 
lean_dec(v_tk_372_);
lean_dec(v_f_371_);
v___x_384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_384_, 0, v_b_374_);
return v___x_384_;
}
else
{
lean_object* v_head_385_; lean_object* v_tail_386_; lean_object* v_expr_387_; uint8_t v_symm_388_; lean_object* v_result_389_; lean_object* v_mctx_390_; lean_object* v___x_391_; lean_object* v___f_392_; lean_object* v___x_393_; 
v_head_385_ = lean_ctor_get(v_as_x27_373_, 0);
v_tail_386_ = lean_ctor_get(v_as_x27_373_, 1);
v_expr_387_ = lean_ctor_get(v_head_385_, 0);
v_symm_388_ = lean_ctor_get_uint8(v_head_385_, sizeof(void*)*4);
v_result_389_ = lean_ctor_get(v_head_385_, 2);
v_mctx_390_ = lean_ctor_get(v_head_385_, 3);
v___x_391_ = lean_box(v_symm_388_);
lean_inc(v_tk_372_);
lean_inc(v_f_371_);
lean_inc_ref(v_expr_387_);
lean_inc_ref(v_result_389_);
v___f_392_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__5___redArg___lam__0___boxed), 14, 5);
lean_closure_set(v___f_392_, 0, v_result_389_);
lean_closure_set(v___f_392_, 1, v_expr_387_);
lean_closure_set(v___f_392_, 2, v___x_391_);
lean_closure_set(v___f_392_, 3, v_f_371_);
lean_closure_set(v___f_392_, 4, v_tk_372_);
lean_inc_ref(v_mctx_390_);
v___x_393_ = l_Lean_Meta_withMCtx___at___00Lean_Elab_Rewrites_evalExact_spec__4___redArg(v_mctx_390_, v___f_392_, v___y_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_);
if (lean_obj_tag(v___x_393_) == 0)
{
lean_object* v___x_394_; 
lean_dec_ref(v___x_393_);
v___x_394_ = lean_box(0);
v_as_x27_373_ = v_tail_386_;
v_b_374_ = v___x_394_;
goto _start;
}
else
{
lean_dec(v_tk_372_);
lean_dec(v_f_371_);
return v___x_393_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__5___redArg___boxed(lean_object* v_f_396_, lean_object* v_tk_397_, lean_object* v_as_x27_398_, lean_object* v_b_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__5___redArg(v_f_396_, v_tk_397_, v_as_x27_398_, v_b_399_, v___y_400_, v___y_401_, v___y_402_, v___y_403_, v___y_404_, v___y_405_, v___y_406_, v___y_407_);
lean_dec(v___y_407_);
lean_dec_ref(v___y_406_);
lean_dec(v___y_405_);
lean_dec_ref(v___y_404_);
lean_dec(v___y_403_);
lean_dec_ref(v___y_402_);
lean_dec(v___y_401_);
lean_dec_ref(v___y_400_);
lean_dec(v_as_x27_398_);
return v_res_409_;
}
}
static lean_object* _init_l_Lean_Elab_Rewrites_evalExact___lam__2___closed__3(void){
_start:
{
lean_object* v___x_414_; lean_object* v___x_415_; 
v___x_414_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___lam__2___closed__2));
v___x_415_ = l_Lean_stringToMessageData(v___x_414_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact___lam__2(lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v___y_418_, lean_object* v_tk_419_, lean_object* v___x_420_, lean_object* v___x_421_, lean_object* v_f_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_){
_start:
{
lean_object* v___x_432_; 
lean_inc(v_f_422_);
v___x_432_ = l_Lean_FVarId_findDecl_x3f___redArg(v_f_422_, v___y_427_);
if (lean_obj_tag(v___x_432_) == 0)
{
lean_object* v_a_433_; lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_556_; 
v_a_433_ = lean_ctor_get(v___x_432_, 0);
v_isSharedCheck_556_ = !lean_is_exclusive(v___x_432_);
if (v_isSharedCheck_556_ == 0)
{
v___x_435_ = v___x_432_;
v_isShared_436_ = v_isSharedCheck_556_;
goto v_resetjp_434_;
}
else
{
lean_inc(v_a_433_);
lean_dec(v___x_432_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_556_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
if (lean_obj_tag(v_a_433_) == 1)
{
lean_object* v_val_437_; uint8_t v___x_438_; 
v_val_437_ = lean_ctor_get(v_a_433_, 0);
lean_inc(v_val_437_);
lean_dec_ref(v_a_433_);
v___x_438_ = l_Lean_LocalDecl_isImplementationDetail(v_val_437_);
lean_dec(v_val_437_);
if (v___x_438_ == 0)
{
lean_object* v___x_439_; 
lean_del_object(v___x_435_);
lean_inc(v_f_422_);
v___x_439_ = l_Lean_FVarId_getType___redArg(v_f_422_, v___y_427_, v___y_429_, v___y_430_);
if (lean_obj_tag(v___x_439_) == 0)
{
lean_object* v_a_440_; lean_object* v___x_441_; lean_object* v_a_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; 
v_a_440_ = lean_ctor_get(v___x_439_, 0);
lean_inc(v_a_440_);
lean_dec_ref(v___x_439_);
v___x_441_ = l_Lean_instantiateMVars___at___00Lean_Elab_Rewrites_evalExact_spec__2___redArg(v_a_440_, v___y_428_);
v_a_442_ = lean_ctor_get(v___x_441_, 0);
lean_inc(v_a_442_);
lean_dec_ref(v___x_441_);
v___x_443_ = lean_box(0);
lean_inc(v_f_422_);
v___x_444_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_444_, 0, v_f_422_);
lean_ctor_set(v___x_444_, 1, v___x_443_);
v___x_445_ = l_Lean_Meta_Rewrites_localHypotheses(v___x_444_, v___y_427_, v___y_428_, v___y_429_, v___y_430_);
lean_dec_ref(v___x_444_);
if (lean_obj_tag(v___x_445_) == 0)
{
lean_object* v_a_446_; uint8_t v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; 
v_a_446_ = lean_ctor_get(v___x_445_, 0);
lean_inc(v_a_446_);
lean_dec_ref(v___x_445_);
v___x_447_ = 2;
v___x_448_ = lean_unsigned_to_nat(20u);
v___x_449_ = lean_unsigned_to_nat(10u);
lean_inc(v_a_417_);
v___x_450_ = l_Lean_Meta_Rewrites_findRewrites(v_a_446_, v_a_416_, v_a_417_, v_a_442_, v___y_418_, v___x_447_, v___x_438_, v___x_448_, v___x_449_, v___y_427_, v___y_428_, v___y_429_, v___y_430_);
if (lean_obj_tag(v___x_450_) == 0)
{
lean_object* v_a_451_; lean_object* v___y_453_; lean_object* v___y_454_; lean_object* v___y_455_; lean_object* v___y_456_; lean_object* v___y_457_; lean_object* v___y_458_; lean_object* v___y_459_; lean_object* v___y_460_; lean_object* v___x_507_; lean_object* v___x_508_; 
v_a_451_ = lean_ctor_get(v___x_450_, 0);
lean_inc(v_a_451_);
lean_dec_ref(v___x_450_);
v___x_507_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___lam__2___closed__1));
v___x_508_ = l_Lean_reportOutOfHeartbeats(v___x_507_, v_tk_419_, v___x_420_, v___y_429_, v___y_430_);
if (lean_obj_tag(v___x_508_) == 0)
{
uint8_t v___x_509_; 
lean_dec_ref(v___x_508_);
v___x_509_ = l_List_isEmpty___redArg(v_a_451_);
if (v___x_509_ == 0)
{
v___y_453_ = v___y_423_;
v___y_454_ = v___y_424_;
v___y_455_ = v___y_425_;
v___y_456_ = v___y_426_;
v___y_457_ = v___y_427_;
v___y_458_ = v___y_428_;
v___y_459_ = v___y_429_;
v___y_460_ = v___y_430_;
goto v___jp_452_;
}
else
{
lean_object* v___x_510_; 
lean_dec(v_a_451_);
lean_dec(v___x_421_);
lean_dec(v_tk_419_);
lean_dec(v_a_417_);
v___x_510_ = l_Lean_FVarId_getUserName___redArg(v_f_422_, v___y_427_, v___y_429_, v___y_430_);
if (lean_obj_tag(v___x_510_) == 0)
{
lean_object* v_a_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; 
v_a_511_ = lean_ctor_get(v___x_510_, 0);
lean_inc(v_a_511_);
lean_dec_ref(v___x_510_);
v___x_512_ = lean_obj_once(&l_Lean_Elab_Rewrites_evalExact___lam__2___closed__3, &l_Lean_Elab_Rewrites_evalExact___lam__2___closed__3_once, _init_l_Lean_Elab_Rewrites_evalExact___lam__2___closed__3);
v___x_513_ = l_Lean_MessageData_ofName(v_a_511_);
v___x_514_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_514_, 0, v___x_512_);
lean_ctor_set(v___x_514_, 1, v___x_513_);
v___x_515_ = l_Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__1___redArg(v___x_514_, v___y_427_, v___y_428_, v___y_429_, v___y_430_);
return v___x_515_;
}
else
{
lean_object* v_a_516_; lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_523_; 
v_a_516_ = lean_ctor_get(v___x_510_, 0);
v_isSharedCheck_523_ = !lean_is_exclusive(v___x_510_);
if (v_isSharedCheck_523_ == 0)
{
v___x_518_ = v___x_510_;
v_isShared_519_ = v_isSharedCheck_523_;
goto v_resetjp_517_;
}
else
{
lean_inc(v_a_516_);
lean_dec(v___x_510_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_523_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
lean_object* v___x_521_; 
if (v_isShared_519_ == 0)
{
v___x_521_ = v___x_518_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v_a_516_);
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
}
else
{
lean_dec(v_a_451_);
lean_dec(v_f_422_);
lean_dec(v___x_421_);
lean_dec(v_tk_419_);
lean_dec(v_a_417_);
return v___x_508_;
}
v___jp_452_:
{
lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_461_ = lean_box(0);
lean_inc(v_f_422_);
v___x_462_ = l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__5___redArg(v_f_422_, v_tk_419_, v_a_451_, v___x_461_, v___y_453_, v___y_454_, v___y_455_, v___y_456_, v___y_457_, v___y_458_, v___y_459_, v___y_460_);
if (lean_obj_tag(v___x_462_) == 0)
{
lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_505_; 
v_isSharedCheck_505_ = !lean_is_exclusive(v___x_462_);
if (v_isSharedCheck_505_ == 0)
{
lean_object* v_unused_506_; 
v_unused_506_ = lean_ctor_get(v___x_462_, 0);
lean_dec(v_unused_506_);
v___x_464_ = v___x_462_;
v_isShared_465_ = v_isSharedCheck_505_;
goto v_resetjp_463_;
}
else
{
lean_dec(v___x_462_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_505_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
lean_object* v___x_466_; 
v___x_466_ = l_List_get_x3fInternal___redArg(v_a_451_, v___x_421_);
lean_dec(v_a_451_);
if (lean_obj_tag(v___x_466_) == 1)
{
lean_object* v_val_467_; lean_object* v___x_468_; lean_object* v_result_469_; lean_object* v_mctx_470_; lean_object* v_cache_471_; lean_object* v_zetaDeltaFVarIds_472_; lean_object* v_postponed_473_; lean_object* v_diag_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_500_; 
lean_del_object(v___x_464_);
v_val_467_ = lean_ctor_get(v___x_466_, 0);
lean_inc(v_val_467_);
lean_dec_ref(v___x_466_);
v___x_468_ = lean_st_ref_take(v___y_458_);
v_result_469_ = lean_ctor_get(v_val_467_, 2);
lean_inc_ref(v_result_469_);
v_mctx_470_ = lean_ctor_get(v_val_467_, 3);
lean_inc_ref(v_mctx_470_);
lean_dec(v_val_467_);
v_cache_471_ = lean_ctor_get(v___x_468_, 1);
v_zetaDeltaFVarIds_472_ = lean_ctor_get(v___x_468_, 2);
v_postponed_473_ = lean_ctor_get(v___x_468_, 3);
v_diag_474_ = lean_ctor_get(v___x_468_, 4);
v_isSharedCheck_500_ = !lean_is_exclusive(v___x_468_);
if (v_isSharedCheck_500_ == 0)
{
lean_object* v_unused_501_; 
v_unused_501_ = lean_ctor_get(v___x_468_, 0);
lean_dec(v_unused_501_);
v___x_476_ = v___x_468_;
v_isShared_477_ = v_isSharedCheck_500_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_diag_474_);
lean_inc(v_postponed_473_);
lean_inc(v_zetaDeltaFVarIds_472_);
lean_inc(v_cache_471_);
lean_dec(v___x_468_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_500_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
lean_object* v___x_479_; 
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 0, v_mctx_470_);
v___x_479_ = v___x_476_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v_mctx_470_);
lean_ctor_set(v_reuseFailAlloc_499_, 1, v_cache_471_);
lean_ctor_set(v_reuseFailAlloc_499_, 2, v_zetaDeltaFVarIds_472_);
lean_ctor_set(v_reuseFailAlloc_499_, 3, v_postponed_473_);
lean_ctor_set(v_reuseFailAlloc_499_, 4, v_diag_474_);
v___x_479_ = v_reuseFailAlloc_499_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
lean_object* v___x_480_; lean_object* v_eNew_481_; lean_object* v_eqProof_482_; lean_object* v_mvarIds_483_; lean_object* v___x_484_; lean_object* v___f_485_; lean_object* v___x_486_; 
v___x_480_ = lean_st_ref_set(v___y_458_, v___x_479_);
v_eNew_481_ = lean_ctor_get(v_result_469_, 0);
lean_inc_ref(v_eNew_481_);
v_eqProof_482_ = lean_ctor_get(v_result_469_, 1);
lean_inc_ref(v_eqProof_482_);
v_mvarIds_483_ = lean_ctor_get(v_result_469_, 2);
lean_inc(v_mvarIds_483_);
lean_dec_ref(v_result_469_);
lean_inc(v_f_422_);
v___x_484_ = l_Lean_mkFVar(v_f_422_);
lean_inc(v_a_417_);
v___f_485_ = lean_alloc_closure((void*)(l_Lean_Elab_Rewrites_evalExact___lam__1___boxed), 10, 5);
lean_closure_set(v___f_485_, 0, v_eqProof_482_);
lean_closure_set(v___f_485_, 1, v___x_484_);
lean_closure_set(v___f_485_, 2, v_eNew_481_);
lean_closure_set(v___f_485_, 3, v_a_417_);
lean_closure_set(v___f_485_, 4, v_f_422_);
v___x_486_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Rewrites_evalExact_spec__6___redArg(v_a_417_, v___f_485_, v___y_457_, v___y_458_, v___y_459_, v___y_460_);
if (lean_obj_tag(v___x_486_) == 0)
{
lean_object* v_a_487_; lean_object* v_mvarId_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v_a_487_ = lean_ctor_get(v___x_486_, 0);
lean_inc(v_a_487_);
lean_dec_ref(v___x_486_);
v_mvarId_488_ = lean_ctor_get(v_a_487_, 1);
lean_inc(v_mvarId_488_);
lean_dec(v_a_487_);
v___x_489_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_489_, 0, v_mvarId_488_);
lean_ctor_set(v___x_489_, 1, v_mvarIds_483_);
v___x_490_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_489_, v___y_454_, v___y_457_, v___y_458_, v___y_459_, v___y_460_);
return v___x_490_;
}
else
{
lean_object* v_a_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_498_; 
lean_dec(v_mvarIds_483_);
v_a_491_ = lean_ctor_get(v___x_486_, 0);
v_isSharedCheck_498_ = !lean_is_exclusive(v___x_486_);
if (v_isSharedCheck_498_ == 0)
{
v___x_493_ = v___x_486_;
v_isShared_494_ = v_isSharedCheck_498_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_a_491_);
lean_dec(v___x_486_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_498_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v___x_496_; 
if (v_isShared_494_ == 0)
{
v___x_496_ = v___x_493_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v_a_491_);
v___x_496_ = v_reuseFailAlloc_497_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
return v___x_496_;
}
}
}
}
}
}
else
{
lean_object* v___x_503_; 
lean_dec(v___x_466_);
lean_dec(v_f_422_);
lean_dec(v_a_417_);
if (v_isShared_465_ == 0)
{
lean_ctor_set(v___x_464_, 0, v___x_461_);
v___x_503_ = v___x_464_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v___x_461_);
v___x_503_ = v_reuseFailAlloc_504_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
return v___x_503_;
}
}
}
}
else
{
lean_dec(v_a_451_);
lean_dec(v_f_422_);
lean_dec(v___x_421_);
lean_dec(v_a_417_);
return v___x_462_;
}
}
}
else
{
lean_object* v_a_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_531_; 
lean_dec(v_f_422_);
lean_dec(v___x_421_);
lean_dec(v_tk_419_);
lean_dec(v_a_417_);
v_a_524_ = lean_ctor_get(v___x_450_, 0);
v_isSharedCheck_531_ = !lean_is_exclusive(v___x_450_);
if (v_isSharedCheck_531_ == 0)
{
v___x_526_ = v___x_450_;
v_isShared_527_ = v_isSharedCheck_531_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_a_524_);
lean_dec(v___x_450_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_531_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v___x_529_; 
if (v_isShared_527_ == 0)
{
v___x_529_ = v___x_526_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v_a_524_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
return v___x_529_;
}
}
}
}
else
{
lean_object* v_a_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_539_; 
lean_dec(v_a_442_);
lean_dec(v_f_422_);
lean_dec(v___x_421_);
lean_dec(v_tk_419_);
lean_dec(v_a_417_);
lean_dec(v_a_416_);
v_a_532_ = lean_ctor_get(v___x_445_, 0);
v_isSharedCheck_539_ = !lean_is_exclusive(v___x_445_);
if (v_isSharedCheck_539_ == 0)
{
v___x_534_ = v___x_445_;
v_isShared_535_ = v_isSharedCheck_539_;
goto v_resetjp_533_;
}
else
{
lean_inc(v_a_532_);
lean_dec(v___x_445_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_539_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
lean_object* v___x_537_; 
if (v_isShared_535_ == 0)
{
v___x_537_ = v___x_534_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v_a_532_);
v___x_537_ = v_reuseFailAlloc_538_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
return v___x_537_;
}
}
}
}
else
{
lean_object* v_a_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_547_; 
lean_dec(v_f_422_);
lean_dec(v___x_421_);
lean_dec(v_tk_419_);
lean_dec(v_a_417_);
lean_dec(v_a_416_);
v_a_540_ = lean_ctor_get(v___x_439_, 0);
v_isSharedCheck_547_ = !lean_is_exclusive(v___x_439_);
if (v_isSharedCheck_547_ == 0)
{
v___x_542_ = v___x_439_;
v_isShared_543_ = v_isSharedCheck_547_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_a_540_);
lean_dec(v___x_439_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_547_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v___x_545_; 
if (v_isShared_543_ == 0)
{
v___x_545_ = v___x_542_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v_a_540_);
v___x_545_ = v_reuseFailAlloc_546_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
return v___x_545_;
}
}
}
}
else
{
lean_object* v___x_548_; lean_object* v___x_550_; 
lean_dec(v_f_422_);
lean_dec(v___x_421_);
lean_dec(v_tk_419_);
lean_dec(v_a_417_);
lean_dec(v_a_416_);
v___x_548_ = lean_box(0);
if (v_isShared_436_ == 0)
{
lean_ctor_set(v___x_435_, 0, v___x_548_);
v___x_550_ = v___x_435_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v___x_548_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
return v___x_550_;
}
}
}
else
{
lean_object* v___x_552_; lean_object* v___x_554_; 
lean_dec(v_a_433_);
lean_dec(v_f_422_);
lean_dec(v___x_421_);
lean_dec(v_tk_419_);
lean_dec(v_a_417_);
lean_dec(v_a_416_);
v___x_552_ = lean_box(0);
if (v_isShared_436_ == 0)
{
lean_ctor_set(v___x_435_, 0, v___x_552_);
v___x_554_ = v___x_435_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v___x_552_);
v___x_554_ = v_reuseFailAlloc_555_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
return v___x_554_;
}
}
}
}
else
{
lean_object* v_a_557_; lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_564_; 
lean_dec(v_f_422_);
lean_dec(v___x_421_);
lean_dec(v_tk_419_);
lean_dec(v_a_417_);
lean_dec(v_a_416_);
v_a_557_ = lean_ctor_get(v___x_432_, 0);
v_isSharedCheck_564_ = !lean_is_exclusive(v___x_432_);
if (v_isSharedCheck_564_ == 0)
{
v___x_559_ = v___x_432_;
v_isShared_560_ = v_isSharedCheck_564_;
goto v_resetjp_558_;
}
else
{
lean_inc(v_a_557_);
lean_dec(v___x_432_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_564_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
lean_object* v___x_562_; 
if (v_isShared_560_ == 0)
{
v___x_562_ = v___x_559_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v_a_557_);
v___x_562_ = v_reuseFailAlloc_563_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
return v___x_562_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact___lam__2___boxed(lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v___y_567_, lean_object* v_tk_568_, lean_object* v___x_569_, lean_object* v___x_570_, lean_object* v_f_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_){
_start:
{
lean_object* v_res_581_; 
v_res_581_ = l_Lean_Elab_Rewrites_evalExact___lam__2(v_a_565_, v_a_566_, v___y_567_, v_tk_568_, v___x_569_, v___x_570_, v_f_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_);
lean_dec(v___y_579_);
lean_dec_ref(v___y_578_);
lean_dec(v___y_577_);
lean_dec_ref(v___y_576_);
lean_dec(v___y_575_);
lean_dec_ref(v___y_574_);
lean_dec(v___y_573_);
lean_dec_ref(v___y_572_);
lean_dec(v___x_569_);
lean_dec(v___y_567_);
return v_res_581_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_Rewrites_evalExact_spec__3(lean_object* v_state_582_, lean_object* v_tk_583_, lean_object* v_as_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_){
_start:
{
if (lean_obj_tag(v_as_584_) == 0)
{
lean_object* v___x_594_; lean_object* v___x_595_; 
lean_dec(v_tk_583_);
lean_dec_ref(v_state_582_);
v___x_594_ = lean_box(0);
v___x_595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_595_, 0, v___x_594_);
return v___x_595_;
}
else
{
lean_object* v_head_596_; lean_object* v_tail_597_; lean_object* v___x_598_; lean_object* v___x_599_; 
v_head_596_ = lean_ctor_get(v_as_584_, 0);
lean_inc(v_head_596_);
v_tail_597_ = lean_ctor_get(v_as_584_, 1);
lean_inc(v_tail_597_);
lean_dec_ref(v_as_584_);
lean_inc_ref(v_state_582_);
v___x_598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_598_, 0, v_state_582_);
lean_inc(v_tk_583_);
v___x_599_ = l_Lean_Meta_Rewrites_RewriteResult_addSuggestion(v_tk_583_, v_head_596_, v___x_598_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_);
if (lean_obj_tag(v___x_599_) == 0)
{
lean_dec_ref(v___x_599_);
v_as_584_ = v_tail_597_;
goto _start;
}
else
{
lean_dec(v_tail_597_);
lean_dec(v_tk_583_);
lean_dec_ref(v_state_582_);
return v___x_599_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_Rewrites_evalExact_spec__3___boxed(lean_object* v_state_601_, lean_object* v_tk_602_, lean_object* v_as_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_){
_start:
{
lean_object* v_res_613_; 
v_res_613_ = l_List_forM___at___00Lean_Elab_Rewrites_evalExact_spec__3(v_state_601_, v_tk_602_, v_as_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_);
lean_dec(v___y_611_);
lean_dec_ref(v___y_610_);
lean_dec(v___y_609_);
lean_dec_ref(v___y_608_);
lean_dec(v___y_607_);
lean_dec_ref(v___y_606_);
lean_dec(v___y_605_);
lean_dec_ref(v___y_604_);
return v_res_613_;
}
}
static lean_object* _init_l_Lean_Elab_Rewrites_evalExact___lam__3___closed__9(void){
_start:
{
lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_624_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___lam__3___closed__8));
v___x_625_ = l_Lean_stringToMessageData(v___x_624_);
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact___lam__3(lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v___y_628_, uint8_t v___x_629_, lean_object* v_tk_630_, lean_object* v___x_631_, lean_object* v___x_632_, lean_object* v___x_633_, lean_object* v___x_634_, lean_object* v___x_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_){
_start:
{
lean_object* v___x_645_; 
lean_inc(v_a_626_);
v___x_645_ = l_Lean_MVarId_getType(v_a_626_, v___y_640_, v___y_641_, v___y_642_, v___y_643_);
if (lean_obj_tag(v___x_645_) == 0)
{
lean_object* v_a_646_; lean_object* v___x_647_; lean_object* v_a_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
v_a_646_ = lean_ctor_get(v___x_645_, 0);
lean_inc(v_a_646_);
lean_dec_ref(v___x_645_);
v___x_647_ = l_Lean_instantiateMVars___at___00Lean_Elab_Rewrites_evalExact_spec__2___redArg(v_a_646_, v___y_641_);
v_a_648_ = lean_ctor_get(v___x_647_, 0);
lean_inc(v_a_648_);
lean_dec_ref(v___x_647_);
v___x_649_ = lean_box(0);
v___x_650_ = l_Lean_Meta_Rewrites_localHypotheses(v___x_649_, v___y_640_, v___y_641_, v___y_642_, v___y_643_);
if (lean_obj_tag(v___x_650_) == 0)
{
lean_object* v_a_651_; uint8_t v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
v_a_651_ = lean_ctor_get(v___x_650_, 0);
lean_inc(v_a_651_);
lean_dec_ref(v___x_650_);
v___x_652_ = 2;
v___x_653_ = lean_unsigned_to_nat(20u);
v___x_654_ = lean_unsigned_to_nat(10u);
lean_inc(v_a_626_);
v___x_655_ = l_Lean_Meta_Rewrites_findRewrites(v_a_651_, v_a_627_, v_a_626_, v_a_648_, v___y_628_, v___x_652_, v___x_629_, v___x_653_, v___x_654_, v___y_640_, v___y_641_, v___y_642_, v___y_643_);
if (lean_obj_tag(v___x_655_) == 0)
{
lean_object* v_a_656_; lean_object* v___y_658_; lean_object* v___y_659_; lean_object* v___y_660_; lean_object* v___y_661_; lean_object* v___y_662_; lean_object* v___y_663_; lean_object* v___y_664_; lean_object* v___y_665_; lean_object* v___x_743_; lean_object* v___x_744_; 
v_a_656_ = lean_ctor_get(v___x_655_, 0);
lean_inc(v_a_656_);
lean_dec_ref(v___x_655_);
v___x_743_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___lam__2___closed__1));
v___x_744_ = l_Lean_reportOutOfHeartbeats(v___x_743_, v_tk_630_, v___x_631_, v___y_642_, v___y_643_);
if (lean_obj_tag(v___x_744_) == 0)
{
uint8_t v___x_745_; 
lean_dec_ref(v___x_744_);
v___x_745_ = l_List_isEmpty___redArg(v_a_656_);
if (v___x_745_ == 0)
{
v___y_658_ = v___y_636_;
v___y_659_ = v___y_637_;
v___y_660_ = v___y_638_;
v___y_661_ = v___y_639_;
v___y_662_ = v___y_640_;
v___y_663_ = v___y_641_;
v___y_664_ = v___y_642_;
v___y_665_ = v___y_643_;
goto v___jp_657_;
}
else
{
lean_object* v___x_746_; lean_object* v___x_747_; 
lean_dec(v_a_656_);
lean_dec_ref(v___x_635_);
lean_dec_ref(v___x_634_);
lean_dec_ref(v___x_633_);
lean_dec(v___x_632_);
lean_dec(v_tk_630_);
lean_dec(v_a_626_);
v___x_746_ = lean_obj_once(&l_Lean_Elab_Rewrites_evalExact___lam__3___closed__9, &l_Lean_Elab_Rewrites_evalExact___lam__3___closed__9_once, _init_l_Lean_Elab_Rewrites_evalExact___lam__3___closed__9);
v___x_747_ = l_Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__1___redArg(v___x_746_, v___y_640_, v___y_641_, v___y_642_, v___y_643_);
return v___x_747_;
}
}
else
{
lean_dec(v_a_656_);
lean_dec_ref(v___x_635_);
lean_dec_ref(v___x_634_);
lean_dec_ref(v___x_633_);
lean_dec(v___x_632_);
lean_dec(v_tk_630_);
lean_dec(v_a_626_);
return v___x_744_;
}
v___jp_657_:
{
lean_object* v___x_666_; 
v___x_666_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_659_, v___y_661_, v___y_663_, v___y_665_);
if (lean_obj_tag(v___x_666_) == 0)
{
lean_object* v_a_667_; lean_object* v___x_668_; 
v_a_667_ = lean_ctor_get(v___x_666_, 0);
lean_inc(v_a_667_);
lean_dec_ref(v___x_666_);
v___x_668_ = l_List_get_x3fInternal___redArg(v_a_656_, v___x_632_);
if (lean_obj_tag(v___x_668_) == 1)
{
lean_object* v_val_669_; lean_object* v___x_670_; lean_object* v_result_671_; lean_object* v_mctx_672_; lean_object* v_cache_673_; lean_object* v_zetaDeltaFVarIds_674_; lean_object* v_postponed_675_; lean_object* v_diag_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_732_; 
lean_dec(v_a_667_);
v_val_669_ = lean_ctor_get(v___x_668_, 0);
lean_inc(v_val_669_);
lean_dec_ref(v___x_668_);
v___x_670_ = lean_st_ref_take(v___y_663_);
v_result_671_ = lean_ctor_get(v_val_669_, 2);
lean_inc_ref(v_result_671_);
v_mctx_672_ = lean_ctor_get(v_val_669_, 3);
lean_inc_ref(v_mctx_672_);
lean_dec(v_val_669_);
v_cache_673_ = lean_ctor_get(v___x_670_, 1);
v_zetaDeltaFVarIds_674_ = lean_ctor_get(v___x_670_, 2);
v_postponed_675_ = lean_ctor_get(v___x_670_, 3);
v_diag_676_ = lean_ctor_get(v___x_670_, 4);
v_isSharedCheck_732_ = !lean_is_exclusive(v___x_670_);
if (v_isSharedCheck_732_ == 0)
{
lean_object* v_unused_733_; 
v_unused_733_ = lean_ctor_get(v___x_670_, 0);
lean_dec(v_unused_733_);
v___x_678_ = v___x_670_;
v_isShared_679_ = v_isSharedCheck_732_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_diag_676_);
lean_inc(v_postponed_675_);
lean_inc(v_zetaDeltaFVarIds_674_);
lean_inc(v_cache_673_);
lean_dec(v___x_670_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_732_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v___x_681_; 
if (v_isShared_679_ == 0)
{
lean_ctor_set(v___x_678_, 0, v_mctx_672_);
v___x_681_ = v___x_678_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v_mctx_672_);
lean_ctor_set(v_reuseFailAlloc_731_, 1, v_cache_673_);
lean_ctor_set(v_reuseFailAlloc_731_, 2, v_zetaDeltaFVarIds_674_);
lean_ctor_set(v_reuseFailAlloc_731_, 3, v_postponed_675_);
lean_ctor_set(v_reuseFailAlloc_731_, 4, v_diag_676_);
v___x_681_ = v_reuseFailAlloc_731_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_682_ = lean_st_ref_set(v___y_663_, v___x_681_);
v___x_683_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_659_, v___y_661_, v___y_663_, v___y_665_);
if (lean_obj_tag(v___x_683_) == 0)
{
lean_object* v_a_684_; lean_object* v_eNew_685_; lean_object* v_eqProof_686_; lean_object* v_mvarIds_687_; lean_object* v___x_688_; 
v_a_684_ = lean_ctor_get(v___x_683_, 0);
lean_inc(v_a_684_);
lean_dec_ref(v___x_683_);
v_eNew_685_ = lean_ctor_get(v_result_671_, 0);
lean_inc_ref(v_eNew_685_);
v_eqProof_686_ = lean_ctor_get(v_result_671_, 1);
lean_inc_ref(v_eqProof_686_);
v_mvarIds_687_ = lean_ctor_get(v_result_671_, 2);
lean_inc(v_mvarIds_687_);
lean_dec_ref(v_result_671_);
v___x_688_ = l_Lean_MVarId_replaceTargetEq(v_a_626_, v_eNew_685_, v_eqProof_686_, v___y_662_, v___y_663_, v___y_664_, v___y_665_);
if (lean_obj_tag(v___x_688_) == 0)
{
lean_object* v_a_689_; lean_object* v___x_690_; lean_object* v___x_691_; 
v_a_689_ = lean_ctor_get(v___x_688_, 0);
lean_inc(v_a_689_);
lean_dec_ref(v___x_688_);
v___x_690_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_690_, 0, v_a_689_);
lean_ctor_set(v___x_690_, 1, v_mvarIds_687_);
v___x_691_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_690_, v___y_659_, v___y_662_, v___y_663_, v___y_664_, v___y_665_);
if (lean_obj_tag(v___x_691_) == 0)
{
lean_object* v_ref_692_; uint8_t v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; 
lean_dec_ref(v___x_691_);
v_ref_692_ = lean_ctor_get(v___y_664_, 5);
v___x_693_ = 0;
v___x_694_ = l_Lean_SourceInfo_fromRef(v_ref_692_, v___x_693_);
v___x_695_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___lam__3___closed__0));
lean_inc_ref_n(v___x_635_, 3);
lean_inc_ref_n(v___x_634_, 3);
lean_inc_ref_n(v___x_633_, 3);
v___x_696_ = l_Lean_Name_mkStr4(v___x_633_, v___x_634_, v___x_635_, v___x_695_);
v___x_697_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___lam__3___closed__1));
lean_inc_n(v___x_694_, 6);
v___x_698_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_698_, 0, v___x_694_);
lean_ctor_set(v___x_698_, 1, v___x_697_);
v___x_699_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___lam__3___closed__2));
v___x_700_ = l_Lean_Name_mkStr4(v___x_633_, v___x_634_, v___x_635_, v___x_699_);
v___x_701_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___lam__3___closed__3));
v___x_702_ = l_Lean_Name_mkStr4(v___x_633_, v___x_634_, v___x_635_, v___x_701_);
v___x_703_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___lam__3___closed__5));
v___x_704_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___lam__3___closed__6));
v___x_705_ = l_Lean_Name_mkStr4(v___x_633_, v___x_634_, v___x_635_, v___x_704_);
v___x_706_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___lam__3___closed__7));
v___x_707_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_707_, 0, v___x_694_);
lean_ctor_set(v___x_707_, 1, v___x_706_);
v___x_708_ = l_Lean_Syntax_node1(v___x_694_, v___x_705_, v___x_707_);
v___x_709_ = l_Lean_Syntax_node1(v___x_694_, v___x_703_, v___x_708_);
v___x_710_ = l_Lean_Syntax_node1(v___x_694_, v___x_702_, v___x_709_);
v___x_711_ = l_Lean_Syntax_node1(v___x_694_, v___x_700_, v___x_710_);
v___x_712_ = l_Lean_Syntax_node2(v___x_694_, v___x_696_, v___x_698_, v___x_711_);
v___x_713_ = l_Lean_Elab_Tactic_evalTactic(v___x_712_, v___y_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_);
if (lean_obj_tag(v___x_713_) == 0)
{
lean_object* v___x_714_; 
lean_dec_ref(v___x_713_);
v___x_714_ = l_List_forM___at___00Lean_Elab_Rewrites_evalExact_spec__3(v_a_684_, v_tk_630_, v_a_656_, v___y_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_);
return v___x_714_;
}
else
{
lean_dec(v_a_684_);
lean_dec(v_a_656_);
lean_dec(v_tk_630_);
return v___x_713_;
}
}
else
{
lean_dec(v_a_684_);
lean_dec(v_a_656_);
lean_dec_ref(v___x_635_);
lean_dec_ref(v___x_634_);
lean_dec_ref(v___x_633_);
lean_dec(v_tk_630_);
return v___x_691_;
}
}
else
{
lean_object* v_a_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_722_; 
lean_dec(v_mvarIds_687_);
lean_dec(v_a_684_);
lean_dec(v_a_656_);
lean_dec_ref(v___x_635_);
lean_dec_ref(v___x_634_);
lean_dec_ref(v___x_633_);
lean_dec(v_tk_630_);
v_a_715_ = lean_ctor_get(v___x_688_, 0);
v_isSharedCheck_722_ = !lean_is_exclusive(v___x_688_);
if (v_isSharedCheck_722_ == 0)
{
v___x_717_ = v___x_688_;
v_isShared_718_ = v_isSharedCheck_722_;
goto v_resetjp_716_;
}
else
{
lean_inc(v_a_715_);
lean_dec(v___x_688_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_722_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
lean_object* v___x_720_; 
if (v_isShared_718_ == 0)
{
v___x_720_ = v___x_717_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v_a_715_);
v___x_720_ = v_reuseFailAlloc_721_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
return v___x_720_;
}
}
}
}
else
{
lean_object* v_a_723_; lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_730_; 
lean_dec_ref(v_result_671_);
lean_dec(v_a_656_);
lean_dec_ref(v___x_635_);
lean_dec_ref(v___x_634_);
lean_dec_ref(v___x_633_);
lean_dec(v_tk_630_);
lean_dec(v_a_626_);
v_a_723_ = lean_ctor_get(v___x_683_, 0);
v_isSharedCheck_730_ = !lean_is_exclusive(v___x_683_);
if (v_isSharedCheck_730_ == 0)
{
v___x_725_ = v___x_683_;
v_isShared_726_ = v_isSharedCheck_730_;
goto v_resetjp_724_;
}
else
{
lean_inc(v_a_723_);
lean_dec(v___x_683_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_730_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
lean_object* v___x_728_; 
if (v_isShared_726_ == 0)
{
v___x_728_ = v___x_725_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v_a_723_);
v___x_728_ = v_reuseFailAlloc_729_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
return v___x_728_;
}
}
}
}
}
}
else
{
lean_object* v___x_734_; 
lean_dec(v___x_668_);
lean_dec_ref(v___x_635_);
lean_dec_ref(v___x_634_);
lean_dec_ref(v___x_633_);
lean_dec(v_a_626_);
v___x_734_ = l_List_forM___at___00Lean_Elab_Rewrites_evalExact_spec__3(v_a_667_, v_tk_630_, v_a_656_, v___y_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_);
return v___x_734_;
}
}
else
{
lean_object* v_a_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_742_; 
lean_dec(v_a_656_);
lean_dec_ref(v___x_635_);
lean_dec_ref(v___x_634_);
lean_dec_ref(v___x_633_);
lean_dec(v___x_632_);
lean_dec(v_tk_630_);
lean_dec(v_a_626_);
v_a_735_ = lean_ctor_get(v___x_666_, 0);
v_isSharedCheck_742_ = !lean_is_exclusive(v___x_666_);
if (v_isSharedCheck_742_ == 0)
{
v___x_737_ = v___x_666_;
v_isShared_738_ = v_isSharedCheck_742_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_a_735_);
lean_dec(v___x_666_);
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
}
else
{
lean_object* v_a_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_755_; 
lean_dec_ref(v___x_635_);
lean_dec_ref(v___x_634_);
lean_dec_ref(v___x_633_);
lean_dec(v___x_632_);
lean_dec(v_tk_630_);
lean_dec(v_a_626_);
v_a_748_ = lean_ctor_get(v___x_655_, 0);
v_isSharedCheck_755_ = !lean_is_exclusive(v___x_655_);
if (v_isSharedCheck_755_ == 0)
{
v___x_750_ = v___x_655_;
v_isShared_751_ = v_isSharedCheck_755_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_a_748_);
lean_dec(v___x_655_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_755_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
lean_object* v___x_753_; 
if (v_isShared_751_ == 0)
{
v___x_753_ = v___x_750_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v_a_748_);
v___x_753_ = v_reuseFailAlloc_754_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
return v___x_753_;
}
}
}
}
else
{
lean_object* v_a_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_763_; 
lean_dec(v_a_648_);
lean_dec_ref(v___x_635_);
lean_dec_ref(v___x_634_);
lean_dec_ref(v___x_633_);
lean_dec(v___x_632_);
lean_dec(v_tk_630_);
lean_dec(v_a_627_);
lean_dec(v_a_626_);
v_a_756_ = lean_ctor_get(v___x_650_, 0);
v_isSharedCheck_763_ = !lean_is_exclusive(v___x_650_);
if (v_isSharedCheck_763_ == 0)
{
v___x_758_ = v___x_650_;
v_isShared_759_ = v_isSharedCheck_763_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_a_756_);
lean_dec(v___x_650_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_763_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
lean_object* v___x_761_; 
if (v_isShared_759_ == 0)
{
v___x_761_ = v___x_758_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v_a_756_);
v___x_761_ = v_reuseFailAlloc_762_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
return v___x_761_;
}
}
}
}
else
{
lean_object* v_a_764_; lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_771_; 
lean_dec_ref(v___x_635_);
lean_dec_ref(v___x_634_);
lean_dec_ref(v___x_633_);
lean_dec(v___x_632_);
lean_dec(v_tk_630_);
lean_dec(v_a_627_);
lean_dec(v_a_626_);
v_a_764_ = lean_ctor_get(v___x_645_, 0);
v_isSharedCheck_771_ = !lean_is_exclusive(v___x_645_);
if (v_isSharedCheck_771_ == 0)
{
v___x_766_ = v___x_645_;
v_isShared_767_ = v_isSharedCheck_771_;
goto v_resetjp_765_;
}
else
{
lean_inc(v_a_764_);
lean_dec(v___x_645_);
v___x_766_ = lean_box(0);
v_isShared_767_ = v_isSharedCheck_771_;
goto v_resetjp_765_;
}
v_resetjp_765_:
{
lean_object* v___x_769_; 
if (v_isShared_767_ == 0)
{
v___x_769_ = v___x_766_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v_a_764_);
v___x_769_ = v_reuseFailAlloc_770_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
return v___x_769_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact___lam__3___boxed(lean_object** _args){
lean_object* v_a_772_ = _args[0];
lean_object* v_a_773_ = _args[1];
lean_object* v___y_774_ = _args[2];
lean_object* v___x_775_ = _args[3];
lean_object* v_tk_776_ = _args[4];
lean_object* v___x_777_ = _args[5];
lean_object* v___x_778_ = _args[6];
lean_object* v___x_779_ = _args[7];
lean_object* v___x_780_ = _args[8];
lean_object* v___x_781_ = _args[9];
lean_object* v___y_782_ = _args[10];
lean_object* v___y_783_ = _args[11];
lean_object* v___y_784_ = _args[12];
lean_object* v___y_785_ = _args[13];
lean_object* v___y_786_ = _args[14];
lean_object* v___y_787_ = _args[15];
lean_object* v___y_788_ = _args[16];
lean_object* v___y_789_ = _args[17];
lean_object* v___y_790_ = _args[18];
_start:
{
uint8_t v___x_26742__boxed_791_; lean_object* v_res_792_; 
v___x_26742__boxed_791_ = lean_unbox(v___x_775_);
v_res_792_ = l_Lean_Elab_Rewrites_evalExact___lam__3(v_a_772_, v_a_773_, v___y_774_, v___x_26742__boxed_791_, v_tk_776_, v___x_777_, v___x_778_, v___x_779_, v___x_780_, v___x_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_, v___y_789_);
lean_dec(v___y_789_);
lean_dec_ref(v___y_788_);
lean_dec(v___y_787_);
lean_dec_ref(v___y_786_);
lean_dec(v___y_785_);
lean_dec_ref(v___y_784_);
lean_dec(v___y_783_);
lean_dec_ref(v___y_782_);
lean_dec(v___x_777_);
lean_dec(v___y_774_);
return v_res_792_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__7(size_t v_sz_793_, size_t v_i_794_, lean_object* v_bs_795_){
_start:
{
uint8_t v___x_796_; 
v___x_796_ = lean_usize_dec_lt(v_i_794_, v_sz_793_);
if (v___x_796_ == 0)
{
return v_bs_795_;
}
else
{
lean_object* v_v_797_; lean_object* v___x_798_; lean_object* v_bs_x27_799_; lean_object* v___x_800_; size_t v___x_801_; size_t v___x_802_; lean_object* v___x_803_; 
v_v_797_ = lean_array_uget(v_bs_795_, v_i_794_);
v___x_798_ = lean_unsigned_to_nat(0u);
v_bs_x27_799_ = lean_array_uset(v_bs_795_, v_i_794_, v___x_798_);
v___x_800_ = l_Lean_Syntax_getId(v_v_797_);
lean_dec(v_v_797_);
v___x_801_ = ((size_t)1ULL);
v___x_802_ = lean_usize_add(v_i_794_, v___x_801_);
v___x_803_ = lean_array_uset(v_bs_x27_799_, v_i_794_, v___x_800_);
v_i_794_ = v___x_802_;
v_bs_795_ = v___x_803_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__7___boxed(lean_object* v_sz_805_, lean_object* v_i_806_, lean_object* v_bs_807_){
_start:
{
size_t v_sz_boxed_808_; size_t v_i_boxed_809_; lean_object* v_res_810_; 
v_sz_boxed_808_ = lean_unbox_usize(v_sz_805_);
lean_dec(v_sz_805_);
v_i_boxed_809_ = lean_unbox_usize(v_i_806_);
lean_dec(v_i_806_);
v_res_810_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__7(v_sz_boxed_808_, v_i_boxed_809_, v_bs_807_);
return v_res_810_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Rewrites_evalExact_spec__10(uint8_t v___x_811_, uint8_t v___x_812_, lean_object* v_as_813_, size_t v_i_814_, size_t v_stop_815_, lean_object* v_b_816_){
_start:
{
lean_object* v___y_818_; uint8_t v___x_822_; 
v___x_822_ = lean_usize_dec_eq(v_i_814_, v_stop_815_);
if (v___x_822_ == 0)
{
lean_object* v_fst_823_; uint8_t v___x_824_; 
v_fst_823_ = lean_ctor_get(v_b_816_, 0);
v___x_824_ = lean_unbox(v_fst_823_);
if (v___x_824_ == 0)
{
lean_object* v_snd_825_; lean_object* v___x_827_; uint8_t v_isShared_828_; uint8_t v_isSharedCheck_833_; 
v_snd_825_ = lean_ctor_get(v_b_816_, 1);
v_isSharedCheck_833_ = !lean_is_exclusive(v_b_816_);
if (v_isSharedCheck_833_ == 0)
{
lean_object* v_unused_834_; 
v_unused_834_ = lean_ctor_get(v_b_816_, 0);
lean_dec(v_unused_834_);
v___x_827_ = v_b_816_;
v_isShared_828_ = v_isSharedCheck_833_;
goto v_resetjp_826_;
}
else
{
lean_inc(v_snd_825_);
lean_dec(v_b_816_);
v___x_827_ = lean_box(0);
v_isShared_828_ = v_isSharedCheck_833_;
goto v_resetjp_826_;
}
v_resetjp_826_:
{
lean_object* v___x_829_; lean_object* v___x_831_; 
v___x_829_ = lean_box(v___x_811_);
if (v_isShared_828_ == 0)
{
lean_ctor_set(v___x_827_, 0, v___x_829_);
v___x_831_ = v___x_827_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v___x_829_);
lean_ctor_set(v_reuseFailAlloc_832_, 1, v_snd_825_);
v___x_831_ = v_reuseFailAlloc_832_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
v___y_818_ = v___x_831_;
goto v___jp_817_;
}
}
}
else
{
lean_object* v_snd_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_845_; 
v_snd_835_ = lean_ctor_get(v_b_816_, 1);
v_isSharedCheck_845_ = !lean_is_exclusive(v_b_816_);
if (v_isSharedCheck_845_ == 0)
{
lean_object* v_unused_846_; 
v_unused_846_ = lean_ctor_get(v_b_816_, 0);
lean_dec(v_unused_846_);
v___x_837_ = v_b_816_;
v_isShared_838_ = v_isSharedCheck_845_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_snd_835_);
lean_dec(v_b_816_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_845_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_843_; 
v___x_839_ = lean_array_uget_borrowed(v_as_813_, v_i_814_);
lean_inc(v___x_839_);
v___x_840_ = lean_array_push(v_snd_835_, v___x_839_);
v___x_841_ = lean_box(v___x_812_);
if (v_isShared_838_ == 0)
{
lean_ctor_set(v___x_837_, 1, v___x_840_);
lean_ctor_set(v___x_837_, 0, v___x_841_);
v___x_843_ = v___x_837_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v___x_841_);
lean_ctor_set(v_reuseFailAlloc_844_, 1, v___x_840_);
v___x_843_ = v_reuseFailAlloc_844_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
v___y_818_ = v___x_843_;
goto v___jp_817_;
}
}
}
}
else
{
return v_b_816_;
}
v___jp_817_:
{
size_t v___x_819_; size_t v___x_820_; 
v___x_819_ = ((size_t)1ULL);
v___x_820_ = lean_usize_add(v_i_814_, v___x_819_);
v_i_814_ = v___x_820_;
v_b_816_ = v___y_818_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Rewrites_evalExact_spec__10___boxed(lean_object* v___x_847_, lean_object* v___x_848_, lean_object* v_as_849_, lean_object* v_i_850_, lean_object* v_stop_851_, lean_object* v_b_852_){
_start:
{
uint8_t v___x_27061__boxed_853_; uint8_t v___x_27062__boxed_854_; size_t v_i_boxed_855_; size_t v_stop_boxed_856_; lean_object* v_res_857_; 
v___x_27061__boxed_853_ = lean_unbox(v___x_847_);
v___x_27062__boxed_854_ = lean_unbox(v___x_848_);
v_i_boxed_855_ = lean_unbox_usize(v_i_850_);
lean_dec(v_i_850_);
v_stop_boxed_856_ = lean_unbox_usize(v_stop_851_);
lean_dec(v_stop_851_);
v_res_857_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Rewrites_evalExact_spec__10(v___x_27061__boxed_853_, v___x_27062__boxed_854_, v_as_849_, v_i_boxed_855_, v_stop_boxed_856_, v_b_852_);
lean_dec_ref(v_as_849_);
return v_res_857_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Rewrites_evalExact_spec__8(lean_object* v_as_858_, size_t v_i_859_, size_t v_stop_860_, lean_object* v_b_861_){
_start:
{
uint8_t v___x_862_; 
v___x_862_ = lean_usize_dec_eq(v_i_859_, v_stop_860_);
if (v___x_862_ == 0)
{
lean_object* v___x_863_; lean_object* v___x_864_; size_t v___x_865_; size_t v___x_866_; 
v___x_863_ = lean_array_uget_borrowed(v_as_858_, v_i_859_);
lean_inc(v___x_863_);
v___x_864_ = l_Lean_NameSet_insert(v_b_861_, v___x_863_);
v___x_865_ = ((size_t)1ULL);
v___x_866_ = lean_usize_add(v_i_859_, v___x_865_);
v_i_859_ = v___x_866_;
v_b_861_ = v___x_864_;
goto _start;
}
else
{
return v_b_861_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Rewrites_evalExact_spec__8___boxed(lean_object* v_as_868_, lean_object* v_i_869_, lean_object* v_stop_870_, lean_object* v_b_871_){
_start:
{
size_t v_i_boxed_872_; size_t v_stop_boxed_873_; lean_object* v_res_874_; 
v_i_boxed_872_ = lean_unbox_usize(v_i_869_);
lean_dec(v_i_869_);
v_stop_boxed_873_ = lean_unbox_usize(v_stop_870_);
lean_dec(v_stop_870_);
v_res_874_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Rewrites_evalExact_spec__8(v_as_868_, v_i_boxed_872_, v_stop_boxed_873_, v_b_871_);
lean_dec_ref(v_as_868_);
return v_res_874_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__9(size_t v_sz_878_, size_t v_i_879_, lean_object* v_bs_880_){
_start:
{
uint8_t v___x_881_; 
v___x_881_ = lean_usize_dec_lt(v_i_879_, v_sz_878_);
if (v___x_881_ == 0)
{
lean_object* v___x_882_; 
v___x_882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_882_, 0, v_bs_880_);
return v___x_882_;
}
else
{
lean_object* v_v_883_; lean_object* v___x_884_; uint8_t v___x_885_; 
v_v_883_ = lean_array_uget(v_bs_880_, v_i_879_);
v___x_884_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__9___closed__1));
lean_inc(v_v_883_);
v___x_885_ = l_Lean_Syntax_isOfKind(v_v_883_, v___x_884_);
if (v___x_885_ == 0)
{
lean_object* v___x_886_; 
lean_dec(v_v_883_);
lean_dec_ref(v_bs_880_);
v___x_886_ = lean_box(0);
return v___x_886_;
}
else
{
lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v_bs_x27_889_; lean_object* v_forbidden_890_; size_t v___x_891_; size_t v___x_892_; lean_object* v___x_893_; 
v___x_887_ = lean_unsigned_to_nat(1u);
v___x_888_ = lean_unsigned_to_nat(0u);
v_bs_x27_889_ = lean_array_uset(v_bs_880_, v_i_879_, v___x_888_);
v_forbidden_890_ = l_Lean_Syntax_getArg(v_v_883_, v___x_887_);
lean_dec(v_v_883_);
v___x_891_ = ((size_t)1ULL);
v___x_892_ = lean_usize_add(v_i_879_, v___x_891_);
v___x_893_ = lean_array_uset(v_bs_x27_889_, v_i_879_, v_forbidden_890_);
v_i_879_ = v___x_892_;
v_bs_880_ = v___x_893_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__9___boxed(lean_object* v_sz_895_, lean_object* v_i_896_, lean_object* v_bs_897_){
_start:
{
size_t v_sz_boxed_898_; size_t v_i_boxed_899_; lean_object* v_res_900_; 
v_sz_boxed_898_ = lean_unbox_usize(v_sz_895_);
lean_dec(v_sz_895_);
v_i_boxed_899_ = lean_unbox_usize(v_i_896_);
lean_dec(v_i_896_);
v_res_900_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__9(v_sz_boxed_898_, v_i_boxed_899_, v_bs_897_);
return v_res_900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact(lean_object* v_stx_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_){
_start:
{
lean_object* v___y_935_; lean_object* v___y_936_; lean_object* v___y_937_; lean_object* v___y_938_; lean_object* v___y_939_; lean_object* v___y_940_; lean_object* v___y_941_; lean_object* v___y_942_; lean_object* v___y_943_; lean_object* v___y_944_; lean_object* v___y_945_; lean_object* v___y_946_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; uint8_t v___x_954_; 
v___x_950_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___closed__0));
v___x_951_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___closed__1));
v___x_952_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___closed__2));
v___x_953_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___closed__4));
lean_inc(v_stx_924_);
v___x_954_ = l_Lean_Syntax_isOfKind(v_stx_924_, v___x_953_);
if (v___x_954_ == 0)
{
lean_object* v___x_955_; 
lean_dec(v_stx_924_);
v___x_955_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__0___redArg();
return v___x_955_;
}
else
{
lean_object* v___f_956_; lean_object* v___x_957_; lean_object* v_tk_958_; lean_object* v___y_960_; lean_object* v___y_961_; lean_object* v___y_962_; lean_object* v___y_963_; lean_object* v___y_964_; lean_object* v___y_965_; lean_object* v___y_966_; lean_object* v___y_967_; lean_object* v___y_968_; lean_object* v___y_969_; lean_object* v___y_970_; lean_object* v___y_971_; lean_object* v___y_998_; lean_object* v___y_999_; lean_object* v___y_1000_; lean_object* v___y_1001_; lean_object* v___y_1002_; lean_object* v___y_1003_; lean_object* v___y_1004_; lean_object* v___y_1005_; lean_object* v___y_1006_; lean_object* v___y_1007_; lean_object* v___y_1008_; lean_object* v___y_1009_; lean_object* v___y_1010_; lean_object* v___y_1022_; lean_object* v_forbidden_1023_; lean_object* v___y_1024_; lean_object* v___y_1025_; lean_object* v___y_1026_; lean_object* v___y_1027_; lean_object* v___y_1028_; lean_object* v___y_1029_; lean_object* v___y_1030_; lean_object* v___y_1031_; lean_object* v___y_1046_; lean_object* v___y_1047_; lean_object* v___y_1048_; lean_object* v___y_1049_; lean_object* v___y_1050_; lean_object* v___y_1051_; lean_object* v___y_1052_; lean_object* v___y_1053_; lean_object* v___y_1054_; lean_object* v___y_1055_; lean_object* v___x_1060_; lean_object* v_loc_1062_; lean_object* v___y_1063_; lean_object* v___y_1064_; lean_object* v___y_1065_; lean_object* v___y_1066_; lean_object* v___y_1067_; lean_object* v___y_1068_; lean_object* v___y_1069_; lean_object* v___y_1070_; lean_object* v___x_1097_; uint8_t v___x_1098_; 
v___f_956_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___closed__5));
v___x_957_ = lean_unsigned_to_nat(0u);
v_tk_958_ = l_Lean_Syntax_getArg(v_stx_924_, v___x_957_);
v___x_1060_ = lean_unsigned_to_nat(1u);
v___x_1097_ = l_Lean_Syntax_getArg(v_stx_924_, v___x_1060_);
v___x_1098_ = l_Lean_Syntax_isNone(v___x_1097_);
if (v___x_1098_ == 0)
{
uint8_t v___x_1099_; 
lean_inc(v___x_1097_);
v___x_1099_ = l_Lean_Syntax_matchesNull(v___x_1097_, v___x_1060_);
if (v___x_1099_ == 0)
{
lean_object* v___x_1100_; 
lean_dec(v___x_1097_);
lean_dec(v_tk_958_);
lean_dec(v_stx_924_);
v___x_1100_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__0___redArg();
return v___x_1100_;
}
else
{
lean_object* v_loc_1101_; lean_object* v___x_1102_; 
v_loc_1101_ = l_Lean_Syntax_getArg(v___x_1097_, v___x_957_);
lean_dec(v___x_1097_);
v___x_1102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1102_, 0, v_loc_1101_);
v_loc_1062_ = v___x_1102_;
v___y_1063_ = v_a_925_;
v___y_1064_ = v_a_926_;
v___y_1065_ = v_a_927_;
v___y_1066_ = v_a_928_;
v___y_1067_ = v_a_929_;
v___y_1068_ = v_a_930_;
v___y_1069_ = v_a_931_;
v___y_1070_ = v_a_932_;
goto v___jp_1061_;
}
}
else
{
lean_object* v___x_1103_; 
lean_dec(v___x_1097_);
v___x_1103_ = lean_box(0);
v_loc_1062_ = v___x_1103_;
v___y_1063_ = v_a_925_;
v___y_1064_ = v_a_926_;
v___y_1065_ = v_a_927_;
v___y_1066_ = v_a_928_;
v___y_1067_ = v_a_929_;
v___y_1068_ = v_a_930_;
v___y_1069_ = v_a_931_;
v___y_1070_ = v_a_932_;
goto v___jp_1061_;
}
v___jp_959_:
{
lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; 
v___x_972_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___closed__7));
v___x_973_ = lean_unsigned_to_nat(90u);
v___x_974_ = l_Lean_reportOutOfHeartbeats(v___x_972_, v_tk_958_, v___x_973_, v___y_963_, v___y_961_);
if (lean_obj_tag(v___x_974_) == 0)
{
lean_object* v___x_975_; 
lean_dec_ref(v___x_974_);
v___x_975_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_968_, v___y_967_, v___y_964_, v___y_963_, v___y_961_);
if (lean_obj_tag(v___x_975_) == 0)
{
lean_object* v_a_976_; lean_object* v___f_977_; lean_object* v___x_978_; lean_object* v___f_979_; 
v_a_976_ = lean_ctor_get(v___x_975_, 0);
lean_inc_n(v_a_976_, 2);
lean_dec_ref(v___x_975_);
lean_inc(v_tk_958_);
lean_inc(v___y_971_);
lean_inc(v___y_960_);
v___f_977_ = lean_alloc_closure((void*)(l_Lean_Elab_Rewrites_evalExact___lam__2___boxed), 16, 6);
lean_closure_set(v___f_977_, 0, v___y_960_);
lean_closure_set(v___f_977_, 1, v_a_976_);
lean_closure_set(v___f_977_, 2, v___y_971_);
lean_closure_set(v___f_977_, 3, v_tk_958_);
lean_closure_set(v___f_977_, 4, v___x_973_);
lean_closure_set(v___f_977_, 5, v___x_957_);
v___x_978_ = lean_box(v___x_954_);
v___f_979_ = lean_alloc_closure((void*)(l_Lean_Elab_Rewrites_evalExact___lam__3___boxed), 19, 10);
lean_closure_set(v___f_979_, 0, v_a_976_);
lean_closure_set(v___f_979_, 1, v___y_960_);
lean_closure_set(v___f_979_, 2, v___y_971_);
lean_closure_set(v___f_979_, 3, v___x_978_);
lean_closure_set(v___f_979_, 4, v_tk_958_);
lean_closure_set(v___f_979_, 5, v___x_973_);
lean_closure_set(v___f_979_, 6, v___x_957_);
lean_closure_set(v___f_979_, 7, v___x_950_);
lean_closure_set(v___f_979_, 8, v___x_951_);
lean_closure_set(v___f_979_, 9, v___x_952_);
if (lean_obj_tag(v___y_962_) == 0)
{
lean_object* v___x_980_; 
v___x_980_ = lean_box(0);
v___y_935_ = v___y_961_;
v___y_936_ = v___y_963_;
v___y_937_ = v___y_964_;
v___y_938_ = v___y_965_;
v___y_939_ = v___y_966_;
v___y_940_ = v___f_979_;
v___y_941_ = v___y_967_;
v___y_942_ = v___y_968_;
v___y_943_ = v___y_970_;
v___y_944_ = v___y_969_;
v___y_945_ = v___f_977_;
v___y_946_ = v___x_980_;
goto v___jp_934_;
}
else
{
lean_object* v_val_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_988_; 
v_val_981_ = lean_ctor_get(v___y_962_, 0);
v_isSharedCheck_988_ = !lean_is_exclusive(v___y_962_);
if (v_isSharedCheck_988_ == 0)
{
v___x_983_ = v___y_962_;
v_isShared_984_ = v_isSharedCheck_988_;
goto v_resetjp_982_;
}
else
{
lean_inc(v_val_981_);
lean_dec(v___y_962_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_988_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
lean_object* v___x_986_; 
if (v_isShared_984_ == 0)
{
v___x_986_ = v___x_983_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v_val_981_);
v___x_986_ = v_reuseFailAlloc_987_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
v___y_935_ = v___y_961_;
v___y_936_ = v___y_963_;
v___y_937_ = v___y_964_;
v___y_938_ = v___y_965_;
v___y_939_ = v___y_966_;
v___y_940_ = v___f_979_;
v___y_941_ = v___y_967_;
v___y_942_ = v___y_968_;
v___y_943_ = v___y_970_;
v___y_944_ = v___y_969_;
v___y_945_ = v___f_977_;
v___y_946_ = v___x_986_;
goto v___jp_934_;
}
}
}
}
else
{
lean_object* v_a_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_996_; 
lean_dec(v___y_971_);
lean_dec(v___y_962_);
lean_dec(v___y_960_);
lean_dec(v_tk_958_);
v_a_989_ = lean_ctor_get(v___x_975_, 0);
v_isSharedCheck_996_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_996_ == 0)
{
v___x_991_ = v___x_975_;
v_isShared_992_ = v_isSharedCheck_996_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_a_989_);
lean_dec(v___x_975_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_996_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
lean_object* v___x_994_; 
if (v_isShared_992_ == 0)
{
v___x_994_ = v___x_991_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v_a_989_);
v___x_994_ = v_reuseFailAlloc_995_;
goto v_reusejp_993_;
}
v_reusejp_993_:
{
return v___x_994_;
}
}
}
}
else
{
lean_dec(v___y_971_);
lean_dec(v___y_962_);
lean_dec(v___y_960_);
lean_dec(v_tk_958_);
return v___x_974_;
}
}
v___jp_997_:
{
size_t v_sz_1011_; size_t v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; uint8_t v___x_1015_; 
v_sz_1011_ = lean_array_size(v___y_1010_);
v___x_1012_ = ((size_t)0ULL);
v___x_1013_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__7(v_sz_1011_, v___x_1012_, v___y_1010_);
v___x_1014_ = lean_array_get_size(v___x_1013_);
v___x_1015_ = lean_nat_dec_lt(v___x_957_, v___x_1014_);
if (v___x_1015_ == 0)
{
lean_dec_ref(v___x_1013_);
lean_inc(v___y_1004_);
v___y_960_ = v___y_998_;
v___y_961_ = v___y_999_;
v___y_962_ = v___y_1000_;
v___y_963_ = v___y_1001_;
v___y_964_ = v___y_1002_;
v___y_965_ = v___y_1003_;
v___y_966_ = v___y_1005_;
v___y_967_ = v___y_1006_;
v___y_968_ = v___y_1007_;
v___y_969_ = v___y_1009_;
v___y_970_ = v___y_1008_;
v___y_971_ = v___y_1004_;
goto v___jp_959_;
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
lean_inc(v___y_1004_);
v___y_960_ = v___y_998_;
v___y_961_ = v___y_999_;
v___y_962_ = v___y_1000_;
v___y_963_ = v___y_1001_;
v___y_964_ = v___y_1002_;
v___y_965_ = v___y_1003_;
v___y_966_ = v___y_1005_;
v___y_967_ = v___y_1006_;
v___y_968_ = v___y_1007_;
v___y_969_ = v___y_1009_;
v___y_970_ = v___y_1008_;
v___y_971_ = v___y_1004_;
goto v___jp_959_;
}
else
{
size_t v___x_1017_; lean_object* v___x_1018_; 
v___x_1017_ = lean_usize_of_nat(v___x_1014_);
lean_inc(v___y_1004_);
v___x_1018_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Rewrites_evalExact_spec__8(v___x_1013_, v___x_1012_, v___x_1017_, v___y_1004_);
lean_dec_ref(v___x_1013_);
v___y_960_ = v___y_998_;
v___y_961_ = v___y_999_;
v___y_962_ = v___y_1000_;
v___y_963_ = v___y_1001_;
v___y_964_ = v___y_1002_;
v___y_965_ = v___y_1003_;
v___y_966_ = v___y_1005_;
v___y_967_ = v___y_1006_;
v___y_968_ = v___y_1007_;
v___y_969_ = v___y_1009_;
v___y_970_ = v___y_1008_;
v___y_971_ = v___x_1018_;
goto v___jp_959_;
}
}
else
{
size_t v___x_1019_; lean_object* v___x_1020_; 
v___x_1019_ = lean_usize_of_nat(v___x_1014_);
lean_inc(v___y_1004_);
v___x_1020_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Rewrites_evalExact_spec__8(v___x_1013_, v___x_1012_, v___x_1019_, v___y_1004_);
lean_dec_ref(v___x_1013_);
v___y_960_ = v___y_998_;
v___y_961_ = v___y_999_;
v___y_962_ = v___y_1000_;
v___y_963_ = v___y_1001_;
v___y_964_ = v___y_1002_;
v___y_965_ = v___y_1003_;
v___y_966_ = v___y_1005_;
v___y_967_ = v___y_1006_;
v___y_968_ = v___y_1007_;
v___y_969_ = v___y_1009_;
v___y_970_ = v___y_1008_;
v___y_971_ = v___x_1020_;
goto v___jp_959_;
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
lean_dec_ref(v___x_1032_);
v___x_1034_ = l_Lean_NameSet_empty;
if (lean_obj_tag(v_forbidden_1023_) == 0)
{
lean_object* v___x_1035_; 
v___x_1035_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___closed__8));
v___y_998_ = v_a_1033_;
v___y_999_ = v___y_1031_;
v___y_1000_ = v___y_1022_;
v___y_1001_ = v___y_1030_;
v___y_1002_ = v___y_1029_;
v___y_1003_ = v___y_1024_;
v___y_1004_ = v___x_1034_;
v___y_1005_ = v___y_1026_;
v___y_1006_ = v___y_1028_;
v___y_1007_ = v___y_1025_;
v___y_1008_ = v___y_1027_;
v___y_1009_ = v___f_956_;
v___y_1010_ = v___x_1035_;
goto v___jp_997_;
}
else
{
lean_object* v_val_1036_; 
v_val_1036_ = lean_ctor_get(v_forbidden_1023_, 0);
lean_inc(v_val_1036_);
lean_dec_ref(v_forbidden_1023_);
v___y_998_ = v_a_1033_;
v___y_999_ = v___y_1031_;
v___y_1000_ = v___y_1022_;
v___y_1001_ = v___y_1030_;
v___y_1002_ = v___y_1029_;
v___y_1003_ = v___y_1024_;
v___y_1004_ = v___x_1034_;
v___y_1005_ = v___y_1026_;
v___y_1006_ = v___y_1028_;
v___y_1007_ = v___y_1025_;
v___y_1008_ = v___y_1027_;
v___y_1009_ = v___f_956_;
v___y_1010_ = v_val_1036_;
goto v___jp_997_;
}
}
else
{
lean_object* v_a_1037_; lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1044_; 
lean_dec(v_forbidden_1023_);
lean_dec(v___y_1022_);
lean_dec(v_tk_958_);
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
lean_dec(v___y_1046_);
lean_dec(v_tk_958_);
v___x_1059_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__0___redArg();
return v___x_1059_;
}
else
{
v___y_1022_ = v___y_1046_;
v_forbidden_1023_ = v___x_1058_;
v___y_1024_ = v___y_1049_;
v___y_1025_ = v___y_1054_;
v___y_1026_ = v___y_1048_;
v___y_1027_ = v___y_1052_;
v___y_1028_ = v___y_1053_;
v___y_1029_ = v___y_1051_;
v___y_1030_ = v___y_1047_;
v___y_1031_ = v___y_1050_;
goto v___jp_1021_;
}
}
v___jp_1061_:
{
lean_object* v___x_1071_; lean_object* v___x_1072_; uint8_t v___x_1073_; 
v___x_1071_ = lean_unsigned_to_nat(2u);
v___x_1072_ = l_Lean_Syntax_getArg(v_stx_924_, v___x_1071_);
lean_dec(v_stx_924_);
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
lean_dec(v_tk_958_);
v___x_1075_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__0___redArg();
return v___x_1075_;
}
else
{
lean_object* v___x_1076_; lean_object* v___x_1077_; uint8_t v___x_1078_; 
v___x_1076_ = l_Lean_Syntax_getArg(v___x_1072_, v___x_957_);
lean_dec(v___x_1072_);
v___x_1077_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___closed__10));
lean_inc(v___x_1076_);
v___x_1078_ = l_Lean_Syntax_isOfKind(v___x_1076_, v___x_1077_);
if (v___x_1078_ == 0)
{
lean_object* v___x_1079_; 
lean_dec(v___x_1076_);
lean_dec(v_loc_1062_);
lean_dec(v_tk_958_);
v___x_1079_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__0___redArg();
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
v___x_1084_ = lean_nat_dec_lt(v___x_957_, v___x_1083_);
if (v___x_1084_ == 0)
{
lean_dec_ref(v___x_1081_);
v___y_1046_ = v_loc_1062_;
v___y_1047_ = v___y_1069_;
v___y_1048_ = v___y_1065_;
v___y_1049_ = v___y_1063_;
v___y_1050_ = v___y_1070_;
v___y_1051_ = v___y_1068_;
v___y_1052_ = v___y_1066_;
v___y_1053_ = v___y_1067_;
v___y_1054_ = v___y_1064_;
v___y_1055_ = v___x_1082_;
goto v___jp_1045_;
}
else
{
lean_object* v___x_1085_; lean_object* v___x_1086_; uint8_t v___x_1087_; 
v___x_1085_ = lean_box(v___x_1078_);
v___x_1086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1086_, 0, v___x_1085_);
lean_ctor_set(v___x_1086_, 1, v___x_1082_);
v___x_1087_ = lean_nat_dec_le(v___x_1083_, v___x_1083_);
if (v___x_1087_ == 0)
{
if (v___x_1084_ == 0)
{
lean_dec_ref(v___x_1086_);
lean_dec_ref(v___x_1081_);
v___y_1046_ = v_loc_1062_;
v___y_1047_ = v___y_1069_;
v___y_1048_ = v___y_1065_;
v___y_1049_ = v___y_1063_;
v___y_1050_ = v___y_1070_;
v___y_1051_ = v___y_1068_;
v___y_1052_ = v___y_1066_;
v___y_1053_ = v___y_1067_;
v___y_1054_ = v___y_1064_;
v___y_1055_ = v___x_1082_;
goto v___jp_1045_;
}
else
{
size_t v___x_1088_; size_t v___x_1089_; lean_object* v___x_1090_; lean_object* v_snd_1091_; 
v___x_1088_ = ((size_t)0ULL);
v___x_1089_ = lean_usize_of_nat(v___x_1083_);
v___x_1090_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Rewrites_evalExact_spec__10(v___x_1078_, v___x_1073_, v___x_1081_, v___x_1088_, v___x_1089_, v___x_1086_);
lean_dec_ref(v___x_1081_);
v_snd_1091_ = lean_ctor_get(v___x_1090_, 1);
lean_inc(v_snd_1091_);
lean_dec_ref(v___x_1090_);
v___y_1046_ = v_loc_1062_;
v___y_1047_ = v___y_1069_;
v___y_1048_ = v___y_1065_;
v___y_1049_ = v___y_1063_;
v___y_1050_ = v___y_1070_;
v___y_1051_ = v___y_1068_;
v___y_1052_ = v___y_1066_;
v___y_1053_ = v___y_1067_;
v___y_1054_ = v___y_1064_;
v___y_1055_ = v_snd_1091_;
goto v___jp_1045_;
}
}
else
{
size_t v___x_1092_; size_t v___x_1093_; lean_object* v___x_1094_; lean_object* v_snd_1095_; 
v___x_1092_ = ((size_t)0ULL);
v___x_1093_ = lean_usize_of_nat(v___x_1083_);
v___x_1094_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Rewrites_evalExact_spec__10(v___x_1078_, v___x_1073_, v___x_1081_, v___x_1092_, v___x_1093_, v___x_1086_);
lean_dec_ref(v___x_1081_);
v_snd_1095_ = lean_ctor_get(v___x_1094_, 1);
lean_inc(v_snd_1095_);
lean_dec_ref(v___x_1094_);
v___y_1046_ = v_loc_1062_;
v___y_1047_ = v___y_1069_;
v___y_1048_ = v___y_1065_;
v___y_1049_ = v___y_1063_;
v___y_1050_ = v___y_1070_;
v___y_1051_ = v___y_1068_;
v___y_1052_ = v___y_1066_;
v___y_1053_ = v___y_1067_;
v___y_1054_ = v___y_1064_;
v___y_1055_ = v_snd_1095_;
goto v___jp_1045_;
}
}
}
}
}
else
{
lean_object* v___x_1096_; 
lean_dec(v___x_1072_);
v___x_1096_ = lean_box(0);
v___y_1022_ = v_loc_1062_;
v_forbidden_1023_ = v___x_1096_;
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
v___jp_934_:
{
lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; 
v___x_947_ = l_Lean_mkOptionalNode(v___y_946_);
v___x_948_ = l_Lean_Elab_Tactic_expandOptLocation(v___x_947_);
lean_dec(v___x_947_);
lean_inc_ref(v___y_944_);
v___x_949_ = l_Lean_Elab_Tactic_withLocation(v___x_948_, v___y_945_, v___y_940_, v___y_944_, v___y_938_, v___y_942_, v___y_939_, v___y_943_, v___y_941_, v___y_937_, v___y_936_, v___y_935_);
lean_dec(v___x_948_);
return v___x_949_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact___boxed(lean_object* v_stx_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_){
_start:
{
lean_object* v_res_1114_; 
v_res_1114_ = l_Lean_Elab_Rewrites_evalExact(v_stx_1104_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_);
lean_dec(v_a_1112_);
lean_dec_ref(v_a_1111_);
lean_dec(v_a_1110_);
lean_dec_ref(v_a_1109_);
lean_dec(v_a_1108_);
lean_dec_ref(v_a_1107_);
lean_dec(v_a_1106_);
lean_dec_ref(v_a_1105_);
return v_res_1114_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__1(lean_object* v_00_u03b1_1115_, lean_object* v_msg_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_){
_start:
{
lean_object* v___x_1126_; 
v___x_1126_ = l_Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__1___redArg(v_msg_1116_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_);
return v___x_1126_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__1___boxed(lean_object* v_00_u03b1_1127_, lean_object* v_msg_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_){
_start:
{
lean_object* v_res_1138_; 
v_res_1138_ = l_Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__1(v_00_u03b1_1127_, v_msg_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_);
lean_dec(v___y_1136_);
lean_dec_ref(v___y_1135_);
lean_dec(v___y_1134_);
lean_dec_ref(v___y_1133_);
lean_dec(v___y_1132_);
lean_dec_ref(v___y_1131_);
lean_dec(v___y_1130_);
lean_dec_ref(v___y_1129_);
return v_res_1138_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__5(lean_object* v_f_1139_, lean_object* v_tk_1140_, lean_object* v_as_1141_, lean_object* v_as_x27_1142_, lean_object* v_b_1143_, lean_object* v_a_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_){
_start:
{
lean_object* v___x_1154_; 
v___x_1154_ = l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__5___redArg(v_f_1139_, v_tk_1140_, v_as_x27_1142_, v_b_1143_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_);
return v___x_1154_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__5___boxed(lean_object* v_f_1155_, lean_object* v_tk_1156_, lean_object* v_as_1157_, lean_object* v_as_x27_1158_, lean_object* v_b_1159_, lean_object* v_a_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_){
_start:
{
lean_object* v_res_1170_; 
v_res_1170_ = l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__5(v_f_1155_, v_tk_1156_, v_as_1157_, v_as_x27_1158_, v_b_1159_, v_a_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_);
lean_dec(v___y_1168_);
lean_dec_ref(v___y_1167_);
lean_dec(v___y_1166_);
lean_dec_ref(v___y_1165_);
lean_dec(v___y_1164_);
lean_dec_ref(v___y_1163_);
lean_dec(v___y_1162_);
lean_dec_ref(v___y_1161_);
lean_dec(v_as_x27_1158_);
lean_dec(v_as_1157_);
return v_res_1170_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1(){
_start:
{
lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; 
v___x_1180_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1181_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___closed__4));
v___x_1182_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___closed__3));
v___x_1183_ = lean_alloc_closure((void*)(l_Lean_Elab_Rewrites_evalExact___boxed), 10, 0);
v___x_1184_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1180_, v___x_1181_, v___x_1182_, v___x_1183_);
return v___x_1184_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___boxed(lean_object* v_a_1185_){
_start:
{
lean_object* v_res_1186_; 
v_res_1186_ = l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1();
return v_res_1186_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3(){
_start:
{
lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; 
v___x_1213_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___closed__3));
v___x_1214_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__6));
v___x_1215_ = l_Lean_addBuiltinDeclarationRanges(v___x_1213_, v___x_1214_);
return v___x_1215_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___boxed(lean_object* v_a_1216_){
_start:
{
lean_object* v_res_1217_; 
v_res_1217_ = l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3();
return v_res_1217_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Location(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Replace(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Rewrites(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Rewrites(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
