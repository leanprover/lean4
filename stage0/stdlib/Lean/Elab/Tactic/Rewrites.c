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
uint8_t lean_bool_not(uint8_t);
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
uint8_t v___x_34_; uint8_t v___x_35_; 
v___x_34_ = l_Lean_Expr_hasMVar(v_e_31_);
v___x_35_ = lean_bool_not(v___x_34_);
if (v___x_35_ == 0)
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
else
{
lean_object* v___x_56_; 
v___x_56_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_56_, 0, v_e_31_);
return v___x_56_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Rewrites_evalExact_spec__2___redArg___boxed(lean_object* v_e_57_, lean_object* v___y_58_, lean_object* v___y_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l_Lean_instantiateMVars___at___00Lean_Elab_Rewrites_evalExact_spec__2___redArg(v_e_57_, v___y_58_);
lean_dec(v___y_58_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Rewrites_evalExact_spec__2(lean_object* v_e_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = l_Lean_instantiateMVars___at___00Lean_Elab_Rewrites_evalExact_spec__2___redArg(v_e_61_, v___y_67_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Rewrites_evalExact_spec__2___boxed(lean_object* v_e_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = l_Lean_instantiateMVars___at___00Lean_Elab_Rewrites_evalExact_spec__2(v_e_72_, v___y_73_, v___y_74_, v___y_75_, v___y_76_, v___y_77_, v___y_78_, v___y_79_, v___y_80_);
lean_dec(v___y_80_);
lean_dec_ref(v___y_79_);
lean_dec(v___y_78_);
lean_dec_ref(v___y_77_);
lean_dec(v___y_76_);
lean_dec_ref(v___y_75_);
lean_dec(v___y_74_);
lean_dec_ref(v___y_73_);
return v_res_82_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Elab_Rewrites_evalExact_spec__4___redArg___lam__0(lean_object* v_x_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_){
_start:
{
lean_object* v___x_93_; 
lean_inc(v___y_87_);
lean_inc_ref(v___y_86_);
lean_inc(v___y_85_);
lean_inc_ref(v___y_84_);
v___x_93_ = lean_apply_9(v_x_83_, v___y_84_, v___y_85_, v___y_86_, v___y_87_, v___y_88_, v___y_89_, v___y_90_, v___y_91_, lean_box(0));
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Elab_Rewrites_evalExact_spec__4___redArg___lam__0___boxed(lean_object* v_x_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_){
_start:
{
lean_object* v_res_104_; 
v_res_104_ = l_Lean_Meta_withMCtx___at___00Lean_Elab_Rewrites_evalExact_spec__4___redArg___lam__0(v_x_94_, v___y_95_, v___y_96_, v___y_97_, v___y_98_, v___y_99_, v___y_100_, v___y_101_, v___y_102_);
lean_dec(v___y_98_);
lean_dec_ref(v___y_97_);
lean_dec(v___y_96_);
lean_dec_ref(v___y_95_);
return v_res_104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Elab_Rewrites_evalExact_spec__4___redArg(lean_object* v_mctx_105_, lean_object* v_x_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_){
_start:
{
lean_object* v___f_116_; lean_object* v___x_117_; 
lean_inc(v___y_110_);
lean_inc_ref(v___y_109_);
lean_inc(v___y_108_);
lean_inc_ref(v___y_107_);
v___f_116_ = lean_alloc_closure((void*)(l_Lean_Meta_withMCtx___at___00Lean_Elab_Rewrites_evalExact_spec__4___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_116_, 0, v_x_106_);
lean_closure_set(v___f_116_, 1, v___y_107_);
lean_closure_set(v___f_116_, 2, v___y_108_);
lean_closure_set(v___f_116_, 3, v___y_109_);
lean_closure_set(v___f_116_, 4, v___y_110_);
v___x_117_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMCtxImp(lean_box(0), v_mctx_105_, v___f_116_, v___y_111_, v___y_112_, v___y_113_, v___y_114_);
if (lean_obj_tag(v___x_117_) == 0)
{
return v___x_117_;
}
else
{
lean_object* v_a_118_; lean_object* v___x_120_; uint8_t v_isShared_121_; uint8_t v_isSharedCheck_125_; 
v_a_118_ = lean_ctor_get(v___x_117_, 0);
v_isSharedCheck_125_ = !lean_is_exclusive(v___x_117_);
if (v_isSharedCheck_125_ == 0)
{
v___x_120_ = v___x_117_;
v_isShared_121_ = v_isSharedCheck_125_;
goto v_resetjp_119_;
}
else
{
lean_inc(v_a_118_);
lean_dec(v___x_117_);
v___x_120_ = lean_box(0);
v_isShared_121_ = v_isSharedCheck_125_;
goto v_resetjp_119_;
}
v_resetjp_119_:
{
lean_object* v___x_123_; 
if (v_isShared_121_ == 0)
{
v___x_123_ = v___x_120_;
goto v_reusejp_122_;
}
else
{
lean_object* v_reuseFailAlloc_124_; 
v_reuseFailAlloc_124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_124_, 0, v_a_118_);
v___x_123_ = v_reuseFailAlloc_124_;
goto v_reusejp_122_;
}
v_reusejp_122_:
{
return v___x_123_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Elab_Rewrites_evalExact_spec__4___redArg___boxed(lean_object* v_mctx_126_, lean_object* v_x_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_){
_start:
{
lean_object* v_res_137_; 
v_res_137_ = l_Lean_Meta_withMCtx___at___00Lean_Elab_Rewrites_evalExact_spec__4___redArg(v_mctx_126_, v_x_127_, v___y_128_, v___y_129_, v___y_130_, v___y_131_, v___y_132_, v___y_133_, v___y_134_, v___y_135_);
lean_dec(v___y_135_);
lean_dec_ref(v___y_134_);
lean_dec(v___y_133_);
lean_dec_ref(v___y_132_);
lean_dec(v___y_131_);
lean_dec_ref(v___y_130_);
lean_dec(v___y_129_);
lean_dec_ref(v___y_128_);
return v_res_137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Elab_Rewrites_evalExact_spec__4(lean_object* v_00_u03b1_138_, lean_object* v_mctx_139_, lean_object* v_x_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_){
_start:
{
lean_object* v___x_150_; 
v___x_150_ = l_Lean_Meta_withMCtx___at___00Lean_Elab_Rewrites_evalExact_spec__4___redArg(v_mctx_139_, v_x_140_, v___y_141_, v___y_142_, v___y_143_, v___y_144_, v___y_145_, v___y_146_, v___y_147_, v___y_148_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withMCtx___at___00Lean_Elab_Rewrites_evalExact_spec__4___boxed(lean_object* v_00_u03b1_151_, lean_object* v_mctx_152_, lean_object* v_x_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_){
_start:
{
lean_object* v_res_163_; 
v_res_163_ = l_Lean_Meta_withMCtx___at___00Lean_Elab_Rewrites_evalExact_spec__4(v_00_u03b1_151_, v_mctx_152_, v_x_153_, v___y_154_, v___y_155_, v___y_156_, v___y_157_, v___y_158_, v___y_159_, v___y_160_, v___y_161_);
lean_dec(v___y_161_);
lean_dec_ref(v___y_160_);
lean_dec(v___y_159_);
lean_dec_ref(v___y_158_);
lean_dec(v___y_157_);
lean_dec_ref(v___y_156_);
lean_dec(v___y_155_);
lean_dec_ref(v___y_154_);
return v_res_163_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Rewrites_evalExact_spec__6___redArg(lean_object* v_mvarId_164_, lean_object* v_x_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_){
_start:
{
lean_object* v___x_171_; 
v___x_171_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_164_, v_x_165_, v___y_166_, v___y_167_, v___y_168_, v___y_169_);
if (lean_obj_tag(v___x_171_) == 0)
{
lean_object* v_a_172_; lean_object* v___x_174_; uint8_t v_isShared_175_; uint8_t v_isSharedCheck_179_; 
v_a_172_ = lean_ctor_get(v___x_171_, 0);
v_isSharedCheck_179_ = !lean_is_exclusive(v___x_171_);
if (v_isSharedCheck_179_ == 0)
{
v___x_174_ = v___x_171_;
v_isShared_175_ = v_isSharedCheck_179_;
goto v_resetjp_173_;
}
else
{
lean_inc(v_a_172_);
lean_dec(v___x_171_);
v___x_174_ = lean_box(0);
v_isShared_175_ = v_isSharedCheck_179_;
goto v_resetjp_173_;
}
v_resetjp_173_:
{
lean_object* v___x_177_; 
if (v_isShared_175_ == 0)
{
v___x_177_ = v___x_174_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v_a_172_);
v___x_177_ = v_reuseFailAlloc_178_;
goto v_reusejp_176_;
}
v_reusejp_176_:
{
return v___x_177_;
}
}
}
else
{
lean_object* v_a_180_; lean_object* v___x_182_; uint8_t v_isShared_183_; uint8_t v_isSharedCheck_187_; 
v_a_180_ = lean_ctor_get(v___x_171_, 0);
v_isSharedCheck_187_ = !lean_is_exclusive(v___x_171_);
if (v_isSharedCheck_187_ == 0)
{
v___x_182_ = v___x_171_;
v_isShared_183_ = v_isSharedCheck_187_;
goto v_resetjp_181_;
}
else
{
lean_inc(v_a_180_);
lean_dec(v___x_171_);
v___x_182_ = lean_box(0);
v_isShared_183_ = v_isSharedCheck_187_;
goto v_resetjp_181_;
}
v_resetjp_181_:
{
lean_object* v___x_185_; 
if (v_isShared_183_ == 0)
{
v___x_185_ = v___x_182_;
goto v_reusejp_184_;
}
else
{
lean_object* v_reuseFailAlloc_186_; 
v_reuseFailAlloc_186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_186_, 0, v_a_180_);
v___x_185_ = v_reuseFailAlloc_186_;
goto v_reusejp_184_;
}
v_reusejp_184_:
{
return v___x_185_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Rewrites_evalExact_spec__6___redArg___boxed(lean_object* v_mvarId_188_, lean_object* v_x_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_){
_start:
{
lean_object* v_res_195_; 
v_res_195_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Rewrites_evalExact_spec__6___redArg(v_mvarId_188_, v_x_189_, v___y_190_, v___y_191_, v___y_192_, v___y_193_);
lean_dec(v___y_193_);
lean_dec_ref(v___y_192_);
lean_dec(v___y_191_);
lean_dec_ref(v___y_190_);
return v_res_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Rewrites_evalExact_spec__6(lean_object* v_00_u03b1_196_, lean_object* v_mvarId_197_, lean_object* v_x_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_){
_start:
{
lean_object* v___x_204_; 
v___x_204_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Rewrites_evalExact_spec__6___redArg(v_mvarId_197_, v_x_198_, v___y_199_, v___y_200_, v___y_201_, v___y_202_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Rewrites_evalExact_spec__6___boxed(lean_object* v_00_u03b1_205_, lean_object* v_mvarId_206_, lean_object* v_x_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Rewrites_evalExact_spec__6(v_00_u03b1_205_, v_mvarId_206_, v_x_207_, v___y_208_, v___y_209_, v___y_210_, v___y_211_);
lean_dec(v___y_211_);
lean_dec_ref(v___y_210_);
lean_dec(v___y_209_);
lean_dec_ref(v___y_208_);
return v_res_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__1_spec__1(lean_object* v_msgData_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_){
_start:
{
lean_object* v___x_220_; lean_object* v_env_221_; lean_object* v___x_222_; lean_object* v_mctx_223_; lean_object* v_lctx_224_; lean_object* v_options_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_220_ = lean_st_ref_get(v___y_218_);
v_env_221_ = lean_ctor_get(v___x_220_, 0);
lean_inc_ref(v_env_221_);
lean_dec(v___x_220_);
v___x_222_ = lean_st_ref_get(v___y_216_);
v_mctx_223_ = lean_ctor_get(v___x_222_, 0);
lean_inc_ref(v_mctx_223_);
lean_dec(v___x_222_);
v_lctx_224_ = lean_ctor_get(v___y_215_, 2);
v_options_225_ = lean_ctor_get(v___y_217_, 2);
lean_inc_ref(v_options_225_);
lean_inc_ref(v_lctx_224_);
v___x_226_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_226_, 0, v_env_221_);
lean_ctor_set(v___x_226_, 1, v_mctx_223_);
lean_ctor_set(v___x_226_, 2, v_lctx_224_);
lean_ctor_set(v___x_226_, 3, v_options_225_);
v___x_227_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_227_, 0, v___x_226_);
lean_ctor_set(v___x_227_, 1, v_msgData_214_);
v___x_228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_228_, 0, v___x_227_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__1_spec__1___boxed(lean_object* v_msgData_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_){
_start:
{
lean_object* v_res_235_; 
v_res_235_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__1_spec__1(v_msgData_229_, v___y_230_, v___y_231_, v___y_232_, v___y_233_);
lean_dec(v___y_233_);
lean_dec_ref(v___y_232_);
lean_dec(v___y_231_);
lean_dec_ref(v___y_230_);
return v_res_235_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__1___redArg(lean_object* v_msg_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_){
_start:
{
lean_object* v_ref_242_; lean_object* v___x_243_; lean_object* v_a_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_252_; 
v_ref_242_ = lean_ctor_get(v___y_239_, 5);
v___x_243_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__1_spec__1(v_msg_236_, v___y_237_, v___y_238_, v___y_239_, v___y_240_);
v_a_244_ = lean_ctor_get(v___x_243_, 0);
v_isSharedCheck_252_ = !lean_is_exclusive(v___x_243_);
if (v_isSharedCheck_252_ == 0)
{
v___x_246_ = v___x_243_;
v_isShared_247_ = v_isSharedCheck_252_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_a_244_);
lean_dec(v___x_243_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_252_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
lean_object* v___x_248_; lean_object* v___x_250_; 
lean_inc(v_ref_242_);
v___x_248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_248_, 0, v_ref_242_);
lean_ctor_set(v___x_248_, 1, v_a_244_);
if (v_isShared_247_ == 0)
{
lean_ctor_set_tag(v___x_246_, 1);
lean_ctor_set(v___x_246_, 0, v___x_248_);
v___x_250_ = v___x_246_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v___x_248_);
v___x_250_ = v_reuseFailAlloc_251_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
return v___x_250_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__1___redArg___boxed(lean_object* v_msg_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l_Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__1___redArg(v_msg_253_, v___y_254_, v___y_255_, v___y_256_, v___y_257_);
lean_dec(v___y_257_);
lean_dec_ref(v___y_256_);
lean_dec(v___y_255_);
lean_dec_ref(v___y_254_);
return v_res_259_;
}
}
static lean_object* _init_l_Lean_Elab_Rewrites_evalExact___lam__0___closed__1(void){
_start:
{
lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_261_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___lam__0___closed__0));
v___x_262_ = l_Lean_stringToMessageData(v___x_261_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact___lam__0(lean_object* v_x_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_){
_start:
{
lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_273_ = lean_obj_once(&l_Lean_Elab_Rewrites_evalExact___lam__0___closed__1, &l_Lean_Elab_Rewrites_evalExact___lam__0___closed__1_once, _init_l_Lean_Elab_Rewrites_evalExact___lam__0___closed__1);
v___x_274_ = l_Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__1___redArg(v___x_273_, v___y_268_, v___y_269_, v___y_270_, v___y_271_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact___lam__0___boxed(lean_object* v_x_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = l_Lean_Elab_Rewrites_evalExact___lam__0(v_x_275_, v___y_276_, v___y_277_, v___y_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_);
lean_dec(v___y_283_);
lean_dec_ref(v___y_282_);
lean_dec(v___y_281_);
lean_dec_ref(v___y_280_);
lean_dec(v___y_279_);
lean_dec_ref(v___y_278_);
lean_dec(v___y_277_);
lean_dec_ref(v___y_276_);
lean_dec(v_x_275_);
return v_res_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact___lam__1(lean_object* v_eqProof_286_, lean_object* v___x_287_, lean_object* v_eNew_288_, lean_object* v_a_289_, lean_object* v_f_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_){
_start:
{
lean_object* v___x_296_; 
v___x_296_ = l_Lean_Meta_mkEqMP(v_eqProof_286_, v___x_287_, v___y_291_, v___y_292_, v___y_293_, v___y_294_);
if (lean_obj_tag(v___x_296_) == 0)
{
lean_object* v_a_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
v_a_297_ = lean_ctor_get(v___x_296_, 0);
lean_inc(v_a_297_);
lean_dec_ref_known(v___x_296_, 1);
v___x_298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_298_, 0, v_eNew_288_);
v___x_299_ = lean_box(0);
v___x_300_ = l_Lean_MVarId_replace(v_a_289_, v_f_290_, v_a_297_, v___x_298_, v___x_299_, v___y_291_, v___y_292_, v___y_293_, v___y_294_);
return v___x_300_;
}
else
{
lean_object* v_a_301_; lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_308_; 
lean_dec(v_f_290_);
lean_dec(v_a_289_);
lean_dec_ref(v_eNew_288_);
v_a_301_ = lean_ctor_get(v___x_296_, 0);
v_isSharedCheck_308_ = !lean_is_exclusive(v___x_296_);
if (v_isSharedCheck_308_ == 0)
{
v___x_303_ = v___x_296_;
v_isShared_304_ = v_isSharedCheck_308_;
goto v_resetjp_302_;
}
else
{
lean_inc(v_a_301_);
lean_dec(v___x_296_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_308_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
lean_object* v___x_306_; 
if (v_isShared_304_ == 0)
{
v___x_306_ = v___x_303_;
goto v_reusejp_305_;
}
else
{
lean_object* v_reuseFailAlloc_307_; 
v_reuseFailAlloc_307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_307_, 0, v_a_301_);
v___x_306_ = v_reuseFailAlloc_307_;
goto v_reusejp_305_;
}
v_reusejp_305_:
{
return v___x_306_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact___lam__1___boxed(lean_object* v_eqProof_309_, lean_object* v___x_310_, lean_object* v_eNew_311_, lean_object* v_a_312_, lean_object* v_f_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l_Lean_Elab_Rewrites_evalExact___lam__1(v_eqProof_309_, v___x_310_, v_eNew_311_, v_a_312_, v_f_313_, v___y_314_, v___y_315_, v___y_316_, v___y_317_);
lean_dec(v___y_317_);
lean_dec_ref(v___y_316_);
lean_dec(v___y_315_);
lean_dec_ref(v___y_314_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__5___redArg___lam__0(lean_object* v_result_320_, lean_object* v_expr_321_, uint8_t v_symm_322_, lean_object* v_f_323_, lean_object* v_tk_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_){
_start:
{
lean_object* v___x_334_; 
v___x_334_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_326_, v___y_328_, v___y_330_, v___y_332_);
if (lean_obj_tag(v___x_334_) == 0)
{
lean_object* v_a_335_; lean_object* v_ref_336_; lean_object* v_eNew_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
v_a_335_ = lean_ctor_get(v___x_334_, 0);
lean_inc(v_a_335_);
lean_dec_ref_known(v___x_334_, 1);
v_ref_336_ = lean_ctor_get(v___y_331_, 5);
v_eNew_337_ = lean_ctor_get(v_result_320_, 0);
v___x_338_ = lean_box(v_symm_322_);
v___x_339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_339_, 0, v_expr_321_);
lean_ctor_set(v___x_339_, 1, v___x_338_);
v___x_340_ = lean_box(0);
v___x_341_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_341_, 0, v___x_339_);
lean_ctor_set(v___x_341_, 1, v___x_340_);
lean_inc_ref(v_eNew_337_);
v___x_342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_342_, 0, v_eNew_337_);
v___x_343_ = l_Lean_Expr_fvar___override(v_f_323_);
v___x_344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_344_, 0, v___x_343_);
lean_inc(v_ref_336_);
v___x_345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_345_, 0, v_ref_336_);
v___x_346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_346_, 0, v_a_335_);
v___x_347_ = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion(v_tk_324_, v___x_341_, v___x_342_, v___x_344_, v___x_345_, v___x_346_, v___y_325_, v___y_326_, v___y_327_, v___y_328_, v___y_329_, v___y_330_, v___y_331_, v___y_332_);
return v___x_347_;
}
else
{
lean_object* v_a_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_355_; 
lean_dec(v_tk_324_);
lean_dec(v_f_323_);
lean_dec_ref(v_expr_321_);
v_a_348_ = lean_ctor_get(v___x_334_, 0);
v_isSharedCheck_355_ = !lean_is_exclusive(v___x_334_);
if (v_isSharedCheck_355_ == 0)
{
v___x_350_ = v___x_334_;
v_isShared_351_ = v_isSharedCheck_355_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_a_348_);
lean_dec(v___x_334_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_355_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
lean_object* v___x_353_; 
if (v_isShared_351_ == 0)
{
v___x_353_ = v___x_350_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v_a_348_);
v___x_353_ = v_reuseFailAlloc_354_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
return v___x_353_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__5___redArg___lam__0___boxed(lean_object* v_result_356_, lean_object* v_expr_357_, lean_object* v_symm_358_, lean_object* v_f_359_, lean_object* v_tk_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_){
_start:
{
uint8_t v_symm_boxed_370_; lean_object* v_res_371_; 
v_symm_boxed_370_ = lean_unbox(v_symm_358_);
v_res_371_ = l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__5___redArg___lam__0(v_result_356_, v_expr_357_, v_symm_boxed_370_, v_f_359_, v_tk_360_, v___y_361_, v___y_362_, v___y_363_, v___y_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_);
lean_dec(v___y_368_);
lean_dec_ref(v___y_367_);
lean_dec(v___y_366_);
lean_dec_ref(v___y_365_);
lean_dec(v___y_364_);
lean_dec_ref(v___y_363_);
lean_dec(v___y_362_);
lean_dec_ref(v___y_361_);
lean_dec_ref(v_result_356_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__5___redArg(lean_object* v_f_372_, lean_object* v_tk_373_, lean_object* v_as_x27_374_, lean_object* v_b_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_){
_start:
{
if (lean_obj_tag(v_as_x27_374_) == 0)
{
lean_object* v___x_385_; 
lean_dec(v_tk_373_);
lean_dec(v_f_372_);
v___x_385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_385_, 0, v_b_375_);
return v___x_385_;
}
else
{
lean_object* v_head_386_; lean_object* v_tail_387_; lean_object* v_expr_388_; uint8_t v_symm_389_; lean_object* v_result_390_; lean_object* v_mctx_391_; lean_object* v___x_392_; lean_object* v___f_393_; lean_object* v___x_394_; 
v_head_386_ = lean_ctor_get(v_as_x27_374_, 0);
v_tail_387_ = lean_ctor_get(v_as_x27_374_, 1);
v_expr_388_ = lean_ctor_get(v_head_386_, 0);
v_symm_389_ = lean_ctor_get_uint8(v_head_386_, sizeof(void*)*4);
v_result_390_ = lean_ctor_get(v_head_386_, 2);
v_mctx_391_ = lean_ctor_get(v_head_386_, 3);
v___x_392_ = lean_box(v_symm_389_);
lean_inc(v_tk_373_);
lean_inc(v_f_372_);
lean_inc_ref(v_expr_388_);
lean_inc_ref(v_result_390_);
v___f_393_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__5___redArg___lam__0___boxed), 14, 5);
lean_closure_set(v___f_393_, 0, v_result_390_);
lean_closure_set(v___f_393_, 1, v_expr_388_);
lean_closure_set(v___f_393_, 2, v___x_392_);
lean_closure_set(v___f_393_, 3, v_f_372_);
lean_closure_set(v___f_393_, 4, v_tk_373_);
lean_inc_ref(v_mctx_391_);
v___x_394_ = l_Lean_Meta_withMCtx___at___00Lean_Elab_Rewrites_evalExact_spec__4___redArg(v_mctx_391_, v___f_393_, v___y_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_);
if (lean_obj_tag(v___x_394_) == 0)
{
lean_object* v___x_395_; 
lean_dec_ref_known(v___x_394_, 1);
v___x_395_ = lean_box(0);
v_as_x27_374_ = v_tail_387_;
v_b_375_ = v___x_395_;
goto _start;
}
else
{
lean_dec(v_tk_373_);
lean_dec(v_f_372_);
return v___x_394_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__5___redArg___boxed(lean_object* v_f_397_, lean_object* v_tk_398_, lean_object* v_as_x27_399_, lean_object* v_b_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__5___redArg(v_f_397_, v_tk_398_, v_as_x27_399_, v_b_400_, v___y_401_, v___y_402_, v___y_403_, v___y_404_, v___y_405_, v___y_406_, v___y_407_, v___y_408_);
lean_dec(v___y_408_);
lean_dec_ref(v___y_407_);
lean_dec(v___y_406_);
lean_dec_ref(v___y_405_);
lean_dec(v___y_404_);
lean_dec_ref(v___y_403_);
lean_dec(v___y_402_);
lean_dec_ref(v___y_401_);
lean_dec(v_as_x27_399_);
return v_res_410_;
}
}
static lean_object* _init_l_Lean_Elab_Rewrites_evalExact___lam__2___closed__3(void){
_start:
{
lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_415_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___lam__2___closed__2));
v___x_416_ = l_Lean_stringToMessageData(v___x_415_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact___lam__2(lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v___y_419_, lean_object* v_tk_420_, lean_object* v___x_421_, lean_object* v___x_422_, lean_object* v_f_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_){
_start:
{
lean_object* v___x_433_; 
lean_inc(v_f_423_);
v___x_433_ = l_Lean_FVarId_findDecl_x3f___redArg(v_f_423_, v___y_428_);
if (lean_obj_tag(v___x_433_) == 0)
{
lean_object* v_a_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_557_; 
v_a_434_ = lean_ctor_get(v___x_433_, 0);
v_isSharedCheck_557_ = !lean_is_exclusive(v___x_433_);
if (v_isSharedCheck_557_ == 0)
{
v___x_436_ = v___x_433_;
v_isShared_437_ = v_isSharedCheck_557_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_a_434_);
lean_dec(v___x_433_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_557_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
if (lean_obj_tag(v_a_434_) == 1)
{
lean_object* v_val_438_; uint8_t v___x_439_; 
v_val_438_ = lean_ctor_get(v_a_434_, 0);
lean_inc(v_val_438_);
lean_dec_ref_known(v_a_434_, 1);
v___x_439_ = l_Lean_LocalDecl_isImplementationDetail(v_val_438_);
lean_dec(v_val_438_);
if (v___x_439_ == 0)
{
lean_object* v___x_440_; 
lean_del_object(v___x_436_);
lean_inc(v_f_423_);
v___x_440_ = l_Lean_FVarId_getType___redArg(v_f_423_, v___y_428_, v___y_430_, v___y_431_);
if (lean_obj_tag(v___x_440_) == 0)
{
lean_object* v_a_441_; lean_object* v___x_442_; lean_object* v_a_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; 
v_a_441_ = lean_ctor_get(v___x_440_, 0);
lean_inc(v_a_441_);
lean_dec_ref_known(v___x_440_, 1);
v___x_442_ = l_Lean_instantiateMVars___at___00Lean_Elab_Rewrites_evalExact_spec__2___redArg(v_a_441_, v___y_429_);
v_a_443_ = lean_ctor_get(v___x_442_, 0);
lean_inc(v_a_443_);
lean_dec_ref(v___x_442_);
v___x_444_ = lean_box(0);
lean_inc(v_f_423_);
v___x_445_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_445_, 0, v_f_423_);
lean_ctor_set(v___x_445_, 1, v___x_444_);
v___x_446_ = l_Lean_Meta_Rewrites_localHypotheses(v___x_445_, v___y_428_, v___y_429_, v___y_430_, v___y_431_);
lean_dec_ref_known(v___x_445_, 2);
if (lean_obj_tag(v___x_446_) == 0)
{
lean_object* v_a_447_; uint8_t v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; 
v_a_447_ = lean_ctor_get(v___x_446_, 0);
lean_inc(v_a_447_);
lean_dec_ref_known(v___x_446_, 1);
v___x_448_ = 2;
v___x_449_ = lean_unsigned_to_nat(20u);
v___x_450_ = lean_unsigned_to_nat(10u);
lean_inc(v_a_418_);
v___x_451_ = l_Lean_Meta_Rewrites_findRewrites(v_a_447_, v_a_417_, v_a_418_, v_a_443_, v___y_419_, v___x_448_, v___x_439_, v___x_449_, v___x_450_, v___y_428_, v___y_429_, v___y_430_, v___y_431_);
if (lean_obj_tag(v___x_451_) == 0)
{
lean_object* v_a_452_; lean_object* v___y_454_; lean_object* v___y_455_; lean_object* v___y_456_; lean_object* v___y_457_; lean_object* v___y_458_; lean_object* v___y_459_; lean_object* v___y_460_; lean_object* v___y_461_; lean_object* v___x_508_; lean_object* v___x_509_; 
v_a_452_ = lean_ctor_get(v___x_451_, 0);
lean_inc(v_a_452_);
lean_dec_ref_known(v___x_451_, 1);
v___x_508_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___lam__2___closed__1));
v___x_509_ = l_Lean_reportOutOfHeartbeats(v___x_508_, v_tk_420_, v___x_421_, v___y_430_, v___y_431_);
if (lean_obj_tag(v___x_509_) == 0)
{
uint8_t v___x_510_; 
lean_dec_ref_known(v___x_509_, 1);
v___x_510_ = l_List_isEmpty___redArg(v_a_452_);
if (v___x_510_ == 0)
{
v___y_454_ = v___y_424_;
v___y_455_ = v___y_425_;
v___y_456_ = v___y_426_;
v___y_457_ = v___y_427_;
v___y_458_ = v___y_428_;
v___y_459_ = v___y_429_;
v___y_460_ = v___y_430_;
v___y_461_ = v___y_431_;
goto v___jp_453_;
}
else
{
lean_object* v___x_511_; 
lean_dec(v_a_452_);
lean_dec(v___x_422_);
lean_dec(v_tk_420_);
lean_dec(v_a_418_);
v___x_511_ = l_Lean_FVarId_getUserName___redArg(v_f_423_, v___y_428_, v___y_430_, v___y_431_);
if (lean_obj_tag(v___x_511_) == 0)
{
lean_object* v_a_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; 
v_a_512_ = lean_ctor_get(v___x_511_, 0);
lean_inc(v_a_512_);
lean_dec_ref_known(v___x_511_, 1);
v___x_513_ = lean_obj_once(&l_Lean_Elab_Rewrites_evalExact___lam__2___closed__3, &l_Lean_Elab_Rewrites_evalExact___lam__2___closed__3_once, _init_l_Lean_Elab_Rewrites_evalExact___lam__2___closed__3);
v___x_514_ = l_Lean_MessageData_ofName(v_a_512_);
v___x_515_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_515_, 0, v___x_513_);
lean_ctor_set(v___x_515_, 1, v___x_514_);
v___x_516_ = l_Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__1___redArg(v___x_515_, v___y_428_, v___y_429_, v___y_430_, v___y_431_);
return v___x_516_;
}
else
{
lean_object* v_a_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_524_; 
v_a_517_ = lean_ctor_get(v___x_511_, 0);
v_isSharedCheck_524_ = !lean_is_exclusive(v___x_511_);
if (v_isSharedCheck_524_ == 0)
{
v___x_519_ = v___x_511_;
v_isShared_520_ = v_isSharedCheck_524_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_a_517_);
lean_dec(v___x_511_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_524_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
lean_object* v___x_522_; 
if (v_isShared_520_ == 0)
{
v___x_522_ = v___x_519_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v_a_517_);
v___x_522_ = v_reuseFailAlloc_523_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
return v___x_522_;
}
}
}
}
}
else
{
lean_dec(v_a_452_);
lean_dec(v_f_423_);
lean_dec(v___x_422_);
lean_dec(v_tk_420_);
lean_dec(v_a_418_);
return v___x_509_;
}
v___jp_453_:
{
lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_462_ = lean_box(0);
lean_inc(v_f_423_);
v___x_463_ = l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__5___redArg(v_f_423_, v_tk_420_, v_a_452_, v___x_462_, v___y_454_, v___y_455_, v___y_456_, v___y_457_, v___y_458_, v___y_459_, v___y_460_, v___y_461_);
if (lean_obj_tag(v___x_463_) == 0)
{
lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_506_; 
v_isSharedCheck_506_ = !lean_is_exclusive(v___x_463_);
if (v_isSharedCheck_506_ == 0)
{
lean_object* v_unused_507_; 
v_unused_507_ = lean_ctor_get(v___x_463_, 0);
lean_dec(v_unused_507_);
v___x_465_ = v___x_463_;
v_isShared_466_ = v_isSharedCheck_506_;
goto v_resetjp_464_;
}
else
{
lean_dec(v___x_463_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_506_;
goto v_resetjp_464_;
}
v_resetjp_464_:
{
lean_object* v___x_467_; 
v___x_467_ = l_List_get_x3fInternal___redArg(v_a_452_, v___x_422_);
lean_dec(v_a_452_);
if (lean_obj_tag(v___x_467_) == 1)
{
lean_object* v_val_468_; lean_object* v___x_469_; lean_object* v_result_470_; lean_object* v_mctx_471_; lean_object* v_cache_472_; lean_object* v_zetaDeltaFVarIds_473_; lean_object* v_postponed_474_; lean_object* v_diag_475_; lean_object* v___x_477_; uint8_t v_isShared_478_; uint8_t v_isSharedCheck_501_; 
lean_del_object(v___x_465_);
v_val_468_ = lean_ctor_get(v___x_467_, 0);
lean_inc(v_val_468_);
lean_dec_ref_known(v___x_467_, 1);
v___x_469_ = lean_st_ref_take(v___y_459_);
v_result_470_ = lean_ctor_get(v_val_468_, 2);
lean_inc_ref(v_result_470_);
v_mctx_471_ = lean_ctor_get(v_val_468_, 3);
lean_inc_ref(v_mctx_471_);
lean_dec(v_val_468_);
v_cache_472_ = lean_ctor_get(v___x_469_, 1);
v_zetaDeltaFVarIds_473_ = lean_ctor_get(v___x_469_, 2);
v_postponed_474_ = lean_ctor_get(v___x_469_, 3);
v_diag_475_ = lean_ctor_get(v___x_469_, 4);
v_isSharedCheck_501_ = !lean_is_exclusive(v___x_469_);
if (v_isSharedCheck_501_ == 0)
{
lean_object* v_unused_502_; 
v_unused_502_ = lean_ctor_get(v___x_469_, 0);
lean_dec(v_unused_502_);
v___x_477_ = v___x_469_;
v_isShared_478_ = v_isSharedCheck_501_;
goto v_resetjp_476_;
}
else
{
lean_inc(v_diag_475_);
lean_inc(v_postponed_474_);
lean_inc(v_zetaDeltaFVarIds_473_);
lean_inc(v_cache_472_);
lean_dec(v___x_469_);
v___x_477_ = lean_box(0);
v_isShared_478_ = v_isSharedCheck_501_;
goto v_resetjp_476_;
}
v_resetjp_476_:
{
lean_object* v___x_480_; 
if (v_isShared_478_ == 0)
{
lean_ctor_set(v___x_477_, 0, v_mctx_471_);
v___x_480_ = v___x_477_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v_mctx_471_);
lean_ctor_set(v_reuseFailAlloc_500_, 1, v_cache_472_);
lean_ctor_set(v_reuseFailAlloc_500_, 2, v_zetaDeltaFVarIds_473_);
lean_ctor_set(v_reuseFailAlloc_500_, 3, v_postponed_474_);
lean_ctor_set(v_reuseFailAlloc_500_, 4, v_diag_475_);
v___x_480_ = v_reuseFailAlloc_500_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
lean_object* v___x_481_; lean_object* v_eNew_482_; lean_object* v_eqProof_483_; lean_object* v_mvarIds_484_; lean_object* v___x_485_; lean_object* v___f_486_; lean_object* v___x_487_; 
v___x_481_ = lean_st_ref_set(v___y_459_, v___x_480_);
v_eNew_482_ = lean_ctor_get(v_result_470_, 0);
lean_inc_ref(v_eNew_482_);
v_eqProof_483_ = lean_ctor_get(v_result_470_, 1);
lean_inc_ref(v_eqProof_483_);
v_mvarIds_484_ = lean_ctor_get(v_result_470_, 2);
lean_inc(v_mvarIds_484_);
lean_dec_ref(v_result_470_);
lean_inc(v_f_423_);
v___x_485_ = l_Lean_mkFVar(v_f_423_);
lean_inc(v_a_418_);
v___f_486_ = lean_alloc_closure((void*)(l_Lean_Elab_Rewrites_evalExact___lam__1___boxed), 10, 5);
lean_closure_set(v___f_486_, 0, v_eqProof_483_);
lean_closure_set(v___f_486_, 1, v___x_485_);
lean_closure_set(v___f_486_, 2, v_eNew_482_);
lean_closure_set(v___f_486_, 3, v_a_418_);
lean_closure_set(v___f_486_, 4, v_f_423_);
v___x_487_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Rewrites_evalExact_spec__6___redArg(v_a_418_, v___f_486_, v___y_458_, v___y_459_, v___y_460_, v___y_461_);
if (lean_obj_tag(v___x_487_) == 0)
{
lean_object* v_a_488_; lean_object* v_mvarId_489_; lean_object* v___x_490_; lean_object* v___x_491_; 
v_a_488_ = lean_ctor_get(v___x_487_, 0);
lean_inc(v_a_488_);
lean_dec_ref_known(v___x_487_, 1);
v_mvarId_489_ = lean_ctor_get(v_a_488_, 1);
lean_inc(v_mvarId_489_);
lean_dec(v_a_488_);
v___x_490_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_490_, 0, v_mvarId_489_);
lean_ctor_set(v___x_490_, 1, v_mvarIds_484_);
v___x_491_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_490_, v___y_455_, v___y_458_, v___y_459_, v___y_460_, v___y_461_);
return v___x_491_;
}
else
{
lean_object* v_a_492_; lean_object* v___x_494_; uint8_t v_isShared_495_; uint8_t v_isSharedCheck_499_; 
lean_dec(v_mvarIds_484_);
v_a_492_ = lean_ctor_get(v___x_487_, 0);
v_isSharedCheck_499_ = !lean_is_exclusive(v___x_487_);
if (v_isSharedCheck_499_ == 0)
{
v___x_494_ = v___x_487_;
v_isShared_495_ = v_isSharedCheck_499_;
goto v_resetjp_493_;
}
else
{
lean_inc(v_a_492_);
lean_dec(v___x_487_);
v___x_494_ = lean_box(0);
v_isShared_495_ = v_isSharedCheck_499_;
goto v_resetjp_493_;
}
v_resetjp_493_:
{
lean_object* v___x_497_; 
if (v_isShared_495_ == 0)
{
v___x_497_ = v___x_494_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v_a_492_);
v___x_497_ = v_reuseFailAlloc_498_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
return v___x_497_;
}
}
}
}
}
}
else
{
lean_object* v___x_504_; 
lean_dec(v___x_467_);
lean_dec(v_f_423_);
lean_dec(v_a_418_);
if (v_isShared_466_ == 0)
{
lean_ctor_set(v___x_465_, 0, v___x_462_);
v___x_504_ = v___x_465_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v___x_462_);
v___x_504_ = v_reuseFailAlloc_505_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
return v___x_504_;
}
}
}
}
else
{
lean_dec(v_a_452_);
lean_dec(v_f_423_);
lean_dec(v___x_422_);
lean_dec(v_a_418_);
return v___x_463_;
}
}
}
else
{
lean_object* v_a_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_532_; 
lean_dec(v_f_423_);
lean_dec(v___x_422_);
lean_dec(v_tk_420_);
lean_dec(v_a_418_);
v_a_525_ = lean_ctor_get(v___x_451_, 0);
v_isSharedCheck_532_ = !lean_is_exclusive(v___x_451_);
if (v_isSharedCheck_532_ == 0)
{
v___x_527_ = v___x_451_;
v_isShared_528_ = v_isSharedCheck_532_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_a_525_);
lean_dec(v___x_451_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_532_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
lean_object* v___x_530_; 
if (v_isShared_528_ == 0)
{
v___x_530_ = v___x_527_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v_a_525_);
v___x_530_ = v_reuseFailAlloc_531_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
return v___x_530_;
}
}
}
}
else
{
lean_object* v_a_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_540_; 
lean_dec(v_a_443_);
lean_dec(v_f_423_);
lean_dec(v___x_422_);
lean_dec(v_tk_420_);
lean_dec(v_a_418_);
lean_dec(v_a_417_);
v_a_533_ = lean_ctor_get(v___x_446_, 0);
v_isSharedCheck_540_ = !lean_is_exclusive(v___x_446_);
if (v_isSharedCheck_540_ == 0)
{
v___x_535_ = v___x_446_;
v_isShared_536_ = v_isSharedCheck_540_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_a_533_);
lean_dec(v___x_446_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_540_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
lean_object* v___x_538_; 
if (v_isShared_536_ == 0)
{
v___x_538_ = v___x_535_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v_a_533_);
v___x_538_ = v_reuseFailAlloc_539_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
return v___x_538_;
}
}
}
}
else
{
lean_object* v_a_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_548_; 
lean_dec(v_f_423_);
lean_dec(v___x_422_);
lean_dec(v_tk_420_);
lean_dec(v_a_418_);
lean_dec(v_a_417_);
v_a_541_ = lean_ctor_get(v___x_440_, 0);
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_440_);
if (v_isSharedCheck_548_ == 0)
{
v___x_543_ = v___x_440_;
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_a_541_);
lean_dec(v___x_440_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v___x_546_; 
if (v_isShared_544_ == 0)
{
v___x_546_ = v___x_543_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v_a_541_);
v___x_546_ = v_reuseFailAlloc_547_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
return v___x_546_;
}
}
}
}
else
{
lean_object* v___x_549_; lean_object* v___x_551_; 
lean_dec(v_f_423_);
lean_dec(v___x_422_);
lean_dec(v_tk_420_);
lean_dec(v_a_418_);
lean_dec(v_a_417_);
v___x_549_ = lean_box(0);
if (v_isShared_437_ == 0)
{
lean_ctor_set(v___x_436_, 0, v___x_549_);
v___x_551_ = v___x_436_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v___x_549_);
v___x_551_ = v_reuseFailAlloc_552_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
return v___x_551_;
}
}
}
else
{
lean_object* v___x_553_; lean_object* v___x_555_; 
lean_dec(v_a_434_);
lean_dec(v_f_423_);
lean_dec(v___x_422_);
lean_dec(v_tk_420_);
lean_dec(v_a_418_);
lean_dec(v_a_417_);
v___x_553_ = lean_box(0);
if (v_isShared_437_ == 0)
{
lean_ctor_set(v___x_436_, 0, v___x_553_);
v___x_555_ = v___x_436_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v___x_553_);
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
lean_dec(v_f_423_);
lean_dec(v___x_422_);
lean_dec(v_tk_420_);
lean_dec(v_a_418_);
lean_dec(v_a_417_);
v_a_558_ = lean_ctor_get(v___x_433_, 0);
v_isSharedCheck_565_ = !lean_is_exclusive(v___x_433_);
if (v_isSharedCheck_565_ == 0)
{
v___x_560_ = v___x_433_;
v_isShared_561_ = v_isSharedCheck_565_;
goto v_resetjp_559_;
}
else
{
lean_inc(v_a_558_);
lean_dec(v___x_433_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact___lam__2___boxed(lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v___y_568_, lean_object* v_tk_569_, lean_object* v___x_570_, lean_object* v___x_571_, lean_object* v_f_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_){
_start:
{
lean_object* v_res_582_; 
v_res_582_ = l_Lean_Elab_Rewrites_evalExact___lam__2(v_a_566_, v_a_567_, v___y_568_, v_tk_569_, v___x_570_, v___x_571_, v_f_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_);
lean_dec(v___y_580_);
lean_dec_ref(v___y_579_);
lean_dec(v___y_578_);
lean_dec_ref(v___y_577_);
lean_dec(v___y_576_);
lean_dec_ref(v___y_575_);
lean_dec(v___y_574_);
lean_dec_ref(v___y_573_);
lean_dec(v___x_570_);
lean_dec(v___y_568_);
return v_res_582_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_Rewrites_evalExact_spec__3(lean_object* v_state_583_, lean_object* v_tk_584_, lean_object* v_as_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_){
_start:
{
if (lean_obj_tag(v_as_585_) == 0)
{
lean_object* v___x_595_; lean_object* v___x_596_; 
lean_dec(v_tk_584_);
lean_dec_ref(v_state_583_);
v___x_595_ = lean_box(0);
v___x_596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_596_, 0, v___x_595_);
return v___x_596_;
}
else
{
lean_object* v_head_597_; lean_object* v_tail_598_; lean_object* v___x_599_; lean_object* v___x_600_; 
v_head_597_ = lean_ctor_get(v_as_585_, 0);
lean_inc(v_head_597_);
v_tail_598_ = lean_ctor_get(v_as_585_, 1);
lean_inc(v_tail_598_);
lean_dec_ref_known(v_as_585_, 2);
lean_inc_ref(v_state_583_);
v___x_599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_599_, 0, v_state_583_);
lean_inc(v_tk_584_);
v___x_600_ = l_Lean_Meta_Rewrites_RewriteResult_addSuggestion(v_tk_584_, v_head_597_, v___x_599_, v___y_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_);
if (lean_obj_tag(v___x_600_) == 0)
{
lean_dec_ref_known(v___x_600_, 1);
v_as_585_ = v_tail_598_;
goto _start;
}
else
{
lean_dec(v_tail_598_);
lean_dec(v_tk_584_);
lean_dec_ref(v_state_583_);
return v___x_600_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_Rewrites_evalExact_spec__3___boxed(lean_object* v_state_602_, lean_object* v_tk_603_, lean_object* v_as_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_){
_start:
{
lean_object* v_res_614_; 
v_res_614_ = l_List_forM___at___00Lean_Elab_Rewrites_evalExact_spec__3(v_state_602_, v_tk_603_, v_as_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_);
lean_dec(v___y_612_);
lean_dec_ref(v___y_611_);
lean_dec(v___y_610_);
lean_dec_ref(v___y_609_);
lean_dec(v___y_608_);
lean_dec_ref(v___y_607_);
lean_dec(v___y_606_);
lean_dec_ref(v___y_605_);
return v_res_614_;
}
}
static lean_object* _init_l_Lean_Elab_Rewrites_evalExact___lam__3___closed__9(void){
_start:
{
lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_625_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___lam__3___closed__8));
v___x_626_ = l_Lean_stringToMessageData(v___x_625_);
return v___x_626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact___lam__3(lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v___y_629_, uint8_t v___x_630_, lean_object* v_tk_631_, lean_object* v___x_632_, lean_object* v___x_633_, lean_object* v___x_634_, lean_object* v___x_635_, lean_object* v___x_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_){
_start:
{
lean_object* v___x_646_; 
lean_inc(v_a_627_);
v___x_646_ = l_Lean_MVarId_getType(v_a_627_, v___y_641_, v___y_642_, v___y_643_, v___y_644_);
if (lean_obj_tag(v___x_646_) == 0)
{
lean_object* v_a_647_; lean_object* v___x_648_; lean_object* v_a_649_; lean_object* v___x_650_; lean_object* v___x_651_; 
v_a_647_ = lean_ctor_get(v___x_646_, 0);
lean_inc(v_a_647_);
lean_dec_ref_known(v___x_646_, 1);
v___x_648_ = l_Lean_instantiateMVars___at___00Lean_Elab_Rewrites_evalExact_spec__2___redArg(v_a_647_, v___y_642_);
v_a_649_ = lean_ctor_get(v___x_648_, 0);
lean_inc(v_a_649_);
lean_dec_ref(v___x_648_);
v___x_650_ = lean_box(0);
v___x_651_ = l_Lean_Meta_Rewrites_localHypotheses(v___x_650_, v___y_641_, v___y_642_, v___y_643_, v___y_644_);
if (lean_obj_tag(v___x_651_) == 0)
{
lean_object* v_a_652_; uint8_t v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; 
v_a_652_ = lean_ctor_get(v___x_651_, 0);
lean_inc(v_a_652_);
lean_dec_ref_known(v___x_651_, 1);
v___x_653_ = 2;
v___x_654_ = lean_unsigned_to_nat(20u);
v___x_655_ = lean_unsigned_to_nat(10u);
lean_inc(v_a_627_);
v___x_656_ = l_Lean_Meta_Rewrites_findRewrites(v_a_652_, v_a_628_, v_a_627_, v_a_649_, v___y_629_, v___x_653_, v___x_630_, v___x_654_, v___x_655_, v___y_641_, v___y_642_, v___y_643_, v___y_644_);
if (lean_obj_tag(v___x_656_) == 0)
{
lean_object* v_a_657_; lean_object* v___y_659_; lean_object* v___y_660_; lean_object* v___y_661_; lean_object* v___y_662_; lean_object* v___y_663_; lean_object* v___y_664_; lean_object* v___y_665_; lean_object* v___y_666_; lean_object* v___x_744_; lean_object* v___x_745_; 
v_a_657_ = lean_ctor_get(v___x_656_, 0);
lean_inc(v_a_657_);
lean_dec_ref_known(v___x_656_, 1);
v___x_744_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___lam__2___closed__1));
v___x_745_ = l_Lean_reportOutOfHeartbeats(v___x_744_, v_tk_631_, v___x_632_, v___y_643_, v___y_644_);
if (lean_obj_tag(v___x_745_) == 0)
{
uint8_t v___x_746_; 
lean_dec_ref_known(v___x_745_, 1);
v___x_746_ = l_List_isEmpty___redArg(v_a_657_);
if (v___x_746_ == 0)
{
v___y_659_ = v___y_637_;
v___y_660_ = v___y_638_;
v___y_661_ = v___y_639_;
v___y_662_ = v___y_640_;
v___y_663_ = v___y_641_;
v___y_664_ = v___y_642_;
v___y_665_ = v___y_643_;
v___y_666_ = v___y_644_;
goto v___jp_658_;
}
else
{
lean_object* v___x_747_; lean_object* v___x_748_; 
lean_dec(v_a_657_);
lean_dec_ref(v___x_636_);
lean_dec_ref(v___x_635_);
lean_dec_ref(v___x_634_);
lean_dec(v___x_633_);
lean_dec(v_tk_631_);
lean_dec(v_a_627_);
v___x_747_ = lean_obj_once(&l_Lean_Elab_Rewrites_evalExact___lam__3___closed__9, &l_Lean_Elab_Rewrites_evalExact___lam__3___closed__9_once, _init_l_Lean_Elab_Rewrites_evalExact___lam__3___closed__9);
v___x_748_ = l_Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__1___redArg(v___x_747_, v___y_641_, v___y_642_, v___y_643_, v___y_644_);
return v___x_748_;
}
}
else
{
lean_dec(v_a_657_);
lean_dec_ref(v___x_636_);
lean_dec_ref(v___x_635_);
lean_dec_ref(v___x_634_);
lean_dec(v___x_633_);
lean_dec(v_tk_631_);
lean_dec(v_a_627_);
return v___x_745_;
}
v___jp_658_:
{
lean_object* v___x_667_; 
v___x_667_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_660_, v___y_662_, v___y_664_, v___y_666_);
if (lean_obj_tag(v___x_667_) == 0)
{
lean_object* v_a_668_; lean_object* v___x_669_; 
v_a_668_ = lean_ctor_get(v___x_667_, 0);
lean_inc(v_a_668_);
lean_dec_ref_known(v___x_667_, 1);
v___x_669_ = l_List_get_x3fInternal___redArg(v_a_657_, v___x_633_);
if (lean_obj_tag(v___x_669_) == 1)
{
lean_object* v_val_670_; lean_object* v___x_671_; lean_object* v_result_672_; lean_object* v_mctx_673_; lean_object* v_cache_674_; lean_object* v_zetaDeltaFVarIds_675_; lean_object* v_postponed_676_; lean_object* v_diag_677_; lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_733_; 
lean_dec(v_a_668_);
v_val_670_ = lean_ctor_get(v___x_669_, 0);
lean_inc(v_val_670_);
lean_dec_ref_known(v___x_669_, 1);
v___x_671_ = lean_st_ref_take(v___y_664_);
v_result_672_ = lean_ctor_get(v_val_670_, 2);
lean_inc_ref(v_result_672_);
v_mctx_673_ = lean_ctor_get(v_val_670_, 3);
lean_inc_ref(v_mctx_673_);
lean_dec(v_val_670_);
v_cache_674_ = lean_ctor_get(v___x_671_, 1);
v_zetaDeltaFVarIds_675_ = lean_ctor_get(v___x_671_, 2);
v_postponed_676_ = lean_ctor_get(v___x_671_, 3);
v_diag_677_ = lean_ctor_get(v___x_671_, 4);
v_isSharedCheck_733_ = !lean_is_exclusive(v___x_671_);
if (v_isSharedCheck_733_ == 0)
{
lean_object* v_unused_734_; 
v_unused_734_ = lean_ctor_get(v___x_671_, 0);
lean_dec(v_unused_734_);
v___x_679_ = v___x_671_;
v_isShared_680_ = v_isSharedCheck_733_;
goto v_resetjp_678_;
}
else
{
lean_inc(v_diag_677_);
lean_inc(v_postponed_676_);
lean_inc(v_zetaDeltaFVarIds_675_);
lean_inc(v_cache_674_);
lean_dec(v___x_671_);
v___x_679_ = lean_box(0);
v_isShared_680_ = v_isSharedCheck_733_;
goto v_resetjp_678_;
}
v_resetjp_678_:
{
lean_object* v___x_682_; 
if (v_isShared_680_ == 0)
{
lean_ctor_set(v___x_679_, 0, v_mctx_673_);
v___x_682_ = v___x_679_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v_mctx_673_);
lean_ctor_set(v_reuseFailAlloc_732_, 1, v_cache_674_);
lean_ctor_set(v_reuseFailAlloc_732_, 2, v_zetaDeltaFVarIds_675_);
lean_ctor_set(v_reuseFailAlloc_732_, 3, v_postponed_676_);
lean_ctor_set(v_reuseFailAlloc_732_, 4, v_diag_677_);
v___x_682_ = v_reuseFailAlloc_732_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_683_ = lean_st_ref_set(v___y_664_, v___x_682_);
v___x_684_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_660_, v___y_662_, v___y_664_, v___y_666_);
if (lean_obj_tag(v___x_684_) == 0)
{
lean_object* v_a_685_; lean_object* v_eNew_686_; lean_object* v_eqProof_687_; lean_object* v_mvarIds_688_; lean_object* v___x_689_; 
v_a_685_ = lean_ctor_get(v___x_684_, 0);
lean_inc(v_a_685_);
lean_dec_ref_known(v___x_684_, 1);
v_eNew_686_ = lean_ctor_get(v_result_672_, 0);
lean_inc_ref(v_eNew_686_);
v_eqProof_687_ = lean_ctor_get(v_result_672_, 1);
lean_inc_ref(v_eqProof_687_);
v_mvarIds_688_ = lean_ctor_get(v_result_672_, 2);
lean_inc(v_mvarIds_688_);
lean_dec_ref(v_result_672_);
v___x_689_ = l_Lean_MVarId_replaceTargetEq(v_a_627_, v_eNew_686_, v_eqProof_687_, v___y_663_, v___y_664_, v___y_665_, v___y_666_);
if (lean_obj_tag(v___x_689_) == 0)
{
lean_object* v_a_690_; lean_object* v___x_691_; lean_object* v___x_692_; 
v_a_690_ = lean_ctor_get(v___x_689_, 0);
lean_inc(v_a_690_);
lean_dec_ref_known(v___x_689_, 1);
v___x_691_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_691_, 0, v_a_690_);
lean_ctor_set(v___x_691_, 1, v_mvarIds_688_);
v___x_692_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_691_, v___y_660_, v___y_663_, v___y_664_, v___y_665_, v___y_666_);
if (lean_obj_tag(v___x_692_) == 0)
{
lean_object* v_ref_693_; uint8_t v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; 
lean_dec_ref_known(v___x_692_, 1);
v_ref_693_ = lean_ctor_get(v___y_665_, 5);
v___x_694_ = 0;
v___x_695_ = l_Lean_SourceInfo_fromRef(v_ref_693_, v___x_694_);
v___x_696_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___lam__3___closed__0));
lean_inc_ref_n(v___x_636_, 3);
lean_inc_ref_n(v___x_635_, 3);
lean_inc_ref_n(v___x_634_, 3);
v___x_697_ = l_Lean_Name_mkStr4(v___x_634_, v___x_635_, v___x_636_, v___x_696_);
v___x_698_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___lam__3___closed__1));
lean_inc_n(v___x_695_, 6);
v___x_699_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_699_, 0, v___x_695_);
lean_ctor_set(v___x_699_, 1, v___x_698_);
v___x_700_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___lam__3___closed__2));
v___x_701_ = l_Lean_Name_mkStr4(v___x_634_, v___x_635_, v___x_636_, v___x_700_);
v___x_702_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___lam__3___closed__3));
v___x_703_ = l_Lean_Name_mkStr4(v___x_634_, v___x_635_, v___x_636_, v___x_702_);
v___x_704_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___lam__3___closed__5));
v___x_705_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___lam__3___closed__6));
v___x_706_ = l_Lean_Name_mkStr4(v___x_634_, v___x_635_, v___x_636_, v___x_705_);
v___x_707_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___lam__3___closed__7));
v___x_708_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_708_, 0, v___x_695_);
lean_ctor_set(v___x_708_, 1, v___x_707_);
v___x_709_ = l_Lean_Syntax_node1(v___x_695_, v___x_706_, v___x_708_);
v___x_710_ = l_Lean_Syntax_node1(v___x_695_, v___x_704_, v___x_709_);
v___x_711_ = l_Lean_Syntax_node1(v___x_695_, v___x_703_, v___x_710_);
v___x_712_ = l_Lean_Syntax_node1(v___x_695_, v___x_701_, v___x_711_);
v___x_713_ = l_Lean_Syntax_node2(v___x_695_, v___x_697_, v___x_699_, v___x_712_);
v___x_714_ = l_Lean_Elab_Tactic_evalTactic(v___x_713_, v___y_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_);
if (lean_obj_tag(v___x_714_) == 0)
{
lean_object* v___x_715_; 
lean_dec_ref_known(v___x_714_, 1);
v___x_715_ = l_List_forM___at___00Lean_Elab_Rewrites_evalExact_spec__3(v_a_685_, v_tk_631_, v_a_657_, v___y_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_);
return v___x_715_;
}
else
{
lean_dec(v_a_685_);
lean_dec(v_a_657_);
lean_dec(v_tk_631_);
return v___x_714_;
}
}
else
{
lean_dec(v_a_685_);
lean_dec(v_a_657_);
lean_dec_ref(v___x_636_);
lean_dec_ref(v___x_635_);
lean_dec_ref(v___x_634_);
lean_dec(v_tk_631_);
return v___x_692_;
}
}
else
{
lean_object* v_a_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_723_; 
lean_dec(v_mvarIds_688_);
lean_dec(v_a_685_);
lean_dec(v_a_657_);
lean_dec_ref(v___x_636_);
lean_dec_ref(v___x_635_);
lean_dec_ref(v___x_634_);
lean_dec(v_tk_631_);
v_a_716_ = lean_ctor_get(v___x_689_, 0);
v_isSharedCheck_723_ = !lean_is_exclusive(v___x_689_);
if (v_isSharedCheck_723_ == 0)
{
v___x_718_ = v___x_689_;
v_isShared_719_ = v_isSharedCheck_723_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_a_716_);
lean_dec(v___x_689_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_723_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
lean_object* v___x_721_; 
if (v_isShared_719_ == 0)
{
v___x_721_ = v___x_718_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v_a_716_);
v___x_721_ = v_reuseFailAlloc_722_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
return v___x_721_;
}
}
}
}
else
{
lean_object* v_a_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_731_; 
lean_dec_ref(v_result_672_);
lean_dec(v_a_657_);
lean_dec_ref(v___x_636_);
lean_dec_ref(v___x_635_);
lean_dec_ref(v___x_634_);
lean_dec(v_tk_631_);
lean_dec(v_a_627_);
v_a_724_ = lean_ctor_get(v___x_684_, 0);
v_isSharedCheck_731_ = !lean_is_exclusive(v___x_684_);
if (v_isSharedCheck_731_ == 0)
{
v___x_726_ = v___x_684_;
v_isShared_727_ = v_isSharedCheck_731_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_a_724_);
lean_dec(v___x_684_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_731_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
lean_object* v___x_729_; 
if (v_isShared_727_ == 0)
{
v___x_729_ = v___x_726_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v_a_724_);
v___x_729_ = v_reuseFailAlloc_730_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
return v___x_729_;
}
}
}
}
}
}
else
{
lean_object* v___x_735_; 
lean_dec(v___x_669_);
lean_dec_ref(v___x_636_);
lean_dec_ref(v___x_635_);
lean_dec_ref(v___x_634_);
lean_dec(v_a_627_);
v___x_735_ = l_List_forM___at___00Lean_Elab_Rewrites_evalExact_spec__3(v_a_668_, v_tk_631_, v_a_657_, v___y_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_);
return v___x_735_;
}
}
else
{
lean_object* v_a_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_743_; 
lean_dec(v_a_657_);
lean_dec_ref(v___x_636_);
lean_dec_ref(v___x_635_);
lean_dec_ref(v___x_634_);
lean_dec(v___x_633_);
lean_dec(v_tk_631_);
lean_dec(v_a_627_);
v_a_736_ = lean_ctor_get(v___x_667_, 0);
v_isSharedCheck_743_ = !lean_is_exclusive(v___x_667_);
if (v_isSharedCheck_743_ == 0)
{
v___x_738_ = v___x_667_;
v_isShared_739_ = v_isSharedCheck_743_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_a_736_);
lean_dec(v___x_667_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_743_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v___x_741_; 
if (v_isShared_739_ == 0)
{
v___x_741_ = v___x_738_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v_a_736_);
v___x_741_ = v_reuseFailAlloc_742_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
return v___x_741_;
}
}
}
}
}
else
{
lean_object* v_a_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_756_; 
lean_dec_ref(v___x_636_);
lean_dec_ref(v___x_635_);
lean_dec_ref(v___x_634_);
lean_dec(v___x_633_);
lean_dec(v_tk_631_);
lean_dec(v_a_627_);
v_a_749_ = lean_ctor_get(v___x_656_, 0);
v_isSharedCheck_756_ = !lean_is_exclusive(v___x_656_);
if (v_isSharedCheck_756_ == 0)
{
v___x_751_ = v___x_656_;
v_isShared_752_ = v_isSharedCheck_756_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_a_749_);
lean_dec(v___x_656_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_756_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
lean_object* v___x_754_; 
if (v_isShared_752_ == 0)
{
v___x_754_ = v___x_751_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v_a_749_);
v___x_754_ = v_reuseFailAlloc_755_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
return v___x_754_;
}
}
}
}
else
{
lean_object* v_a_757_; lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_764_; 
lean_dec(v_a_649_);
lean_dec_ref(v___x_636_);
lean_dec_ref(v___x_635_);
lean_dec_ref(v___x_634_);
lean_dec(v___x_633_);
lean_dec(v_tk_631_);
lean_dec(v_a_628_);
lean_dec(v_a_627_);
v_a_757_ = lean_ctor_get(v___x_651_, 0);
v_isSharedCheck_764_ = !lean_is_exclusive(v___x_651_);
if (v_isSharedCheck_764_ == 0)
{
v___x_759_ = v___x_651_;
v_isShared_760_ = v_isSharedCheck_764_;
goto v_resetjp_758_;
}
else
{
lean_inc(v_a_757_);
lean_dec(v___x_651_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_764_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
lean_object* v___x_762_; 
if (v_isShared_760_ == 0)
{
v___x_762_ = v___x_759_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v_a_757_);
v___x_762_ = v_reuseFailAlloc_763_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
return v___x_762_;
}
}
}
}
else
{
lean_object* v_a_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_772_; 
lean_dec_ref(v___x_636_);
lean_dec_ref(v___x_635_);
lean_dec_ref(v___x_634_);
lean_dec(v___x_633_);
lean_dec(v_tk_631_);
lean_dec(v_a_628_);
lean_dec(v_a_627_);
v_a_765_ = lean_ctor_get(v___x_646_, 0);
v_isSharedCheck_772_ = !lean_is_exclusive(v___x_646_);
if (v_isSharedCheck_772_ == 0)
{
v___x_767_ = v___x_646_;
v_isShared_768_ = v_isSharedCheck_772_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_a_765_);
lean_dec(v___x_646_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_772_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v___x_770_; 
if (v_isShared_768_ == 0)
{
v___x_770_ = v___x_767_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v_a_765_);
v___x_770_ = v_reuseFailAlloc_771_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
return v___x_770_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact___lam__3___boxed(lean_object** _args){
lean_object* v_a_773_ = _args[0];
lean_object* v_a_774_ = _args[1];
lean_object* v___y_775_ = _args[2];
lean_object* v___x_776_ = _args[3];
lean_object* v_tk_777_ = _args[4];
lean_object* v___x_778_ = _args[5];
lean_object* v___x_779_ = _args[6];
lean_object* v___x_780_ = _args[7];
lean_object* v___x_781_ = _args[8];
lean_object* v___x_782_ = _args[9];
lean_object* v___y_783_ = _args[10];
lean_object* v___y_784_ = _args[11];
lean_object* v___y_785_ = _args[12];
lean_object* v___y_786_ = _args[13];
lean_object* v___y_787_ = _args[14];
lean_object* v___y_788_ = _args[15];
lean_object* v___y_789_ = _args[16];
lean_object* v___y_790_ = _args[17];
lean_object* v___y_791_ = _args[18];
_start:
{
uint8_t v___x_26746__boxed_792_; lean_object* v_res_793_; 
v___x_26746__boxed_792_ = lean_unbox(v___x_776_);
v_res_793_ = l_Lean_Elab_Rewrites_evalExact___lam__3(v_a_773_, v_a_774_, v___y_775_, v___x_26746__boxed_792_, v_tk_777_, v___x_778_, v___x_779_, v___x_780_, v___x_781_, v___x_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_, v___y_789_, v___y_790_);
lean_dec(v___y_790_);
lean_dec_ref(v___y_789_);
lean_dec(v___y_788_);
lean_dec_ref(v___y_787_);
lean_dec(v___y_786_);
lean_dec_ref(v___y_785_);
lean_dec(v___y_784_);
lean_dec_ref(v___y_783_);
lean_dec(v___x_778_);
lean_dec(v___y_775_);
return v_res_793_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__7(size_t v_sz_794_, size_t v_i_795_, lean_object* v_bs_796_){
_start:
{
uint8_t v___x_797_; 
v___x_797_ = lean_usize_dec_lt(v_i_795_, v_sz_794_);
if (v___x_797_ == 0)
{
return v_bs_796_;
}
else
{
lean_object* v_v_798_; lean_object* v___x_799_; lean_object* v_bs_x27_800_; lean_object* v___x_801_; size_t v___x_802_; size_t v___x_803_; lean_object* v___x_804_; 
v_v_798_ = lean_array_uget(v_bs_796_, v_i_795_);
v___x_799_ = lean_unsigned_to_nat(0u);
v_bs_x27_800_ = lean_array_uset(v_bs_796_, v_i_795_, v___x_799_);
v___x_801_ = l_Lean_Syntax_getId(v_v_798_);
lean_dec(v_v_798_);
v___x_802_ = ((size_t)1ULL);
v___x_803_ = lean_usize_add(v_i_795_, v___x_802_);
v___x_804_ = lean_array_uset(v_bs_x27_800_, v_i_795_, v___x_801_);
v_i_795_ = v___x_803_;
v_bs_796_ = v___x_804_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__7___boxed(lean_object* v_sz_806_, lean_object* v_i_807_, lean_object* v_bs_808_){
_start:
{
size_t v_sz_boxed_809_; size_t v_i_boxed_810_; lean_object* v_res_811_; 
v_sz_boxed_809_ = lean_unbox_usize(v_sz_806_);
lean_dec(v_sz_806_);
v_i_boxed_810_ = lean_unbox_usize(v_i_807_);
lean_dec(v_i_807_);
v_res_811_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__7(v_sz_boxed_809_, v_i_boxed_810_, v_bs_808_);
return v_res_811_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Rewrites_evalExact_spec__10(uint8_t v___x_812_, uint8_t v___x_813_, lean_object* v_as_814_, size_t v_i_815_, size_t v_stop_816_, lean_object* v_b_817_){
_start:
{
lean_object* v___y_819_; uint8_t v___x_823_; 
v___x_823_ = lean_usize_dec_eq(v_i_815_, v_stop_816_);
if (v___x_823_ == 0)
{
lean_object* v_fst_824_; uint8_t v___x_825_; 
v_fst_824_ = lean_ctor_get(v_b_817_, 0);
v___x_825_ = lean_unbox(v_fst_824_);
if (v___x_825_ == 0)
{
lean_object* v_snd_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_834_; 
v_snd_826_ = lean_ctor_get(v_b_817_, 1);
v_isSharedCheck_834_ = !lean_is_exclusive(v_b_817_);
if (v_isSharedCheck_834_ == 0)
{
lean_object* v_unused_835_; 
v_unused_835_ = lean_ctor_get(v_b_817_, 0);
lean_dec(v_unused_835_);
v___x_828_ = v_b_817_;
v_isShared_829_ = v_isSharedCheck_834_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_snd_826_);
lean_dec(v_b_817_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_834_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
lean_object* v___x_830_; lean_object* v___x_832_; 
v___x_830_ = lean_box(v___x_812_);
if (v_isShared_829_ == 0)
{
lean_ctor_set(v___x_828_, 0, v___x_830_);
v___x_832_ = v___x_828_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v___x_830_);
lean_ctor_set(v_reuseFailAlloc_833_, 1, v_snd_826_);
v___x_832_ = v_reuseFailAlloc_833_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
v___y_819_ = v___x_832_;
goto v___jp_818_;
}
}
}
else
{
lean_object* v_snd_836_; lean_object* v___x_838_; uint8_t v_isShared_839_; uint8_t v_isSharedCheck_846_; 
v_snd_836_ = lean_ctor_get(v_b_817_, 1);
v_isSharedCheck_846_ = !lean_is_exclusive(v_b_817_);
if (v_isSharedCheck_846_ == 0)
{
lean_object* v_unused_847_; 
v_unused_847_ = lean_ctor_get(v_b_817_, 0);
lean_dec(v_unused_847_);
v___x_838_ = v_b_817_;
v_isShared_839_ = v_isSharedCheck_846_;
goto v_resetjp_837_;
}
else
{
lean_inc(v_snd_836_);
lean_dec(v_b_817_);
v___x_838_ = lean_box(0);
v_isShared_839_ = v_isSharedCheck_846_;
goto v_resetjp_837_;
}
v_resetjp_837_:
{
lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_844_; 
v___x_840_ = lean_array_uget_borrowed(v_as_814_, v_i_815_);
lean_inc(v___x_840_);
v___x_841_ = lean_array_push(v_snd_836_, v___x_840_);
v___x_842_ = lean_box(v___x_813_);
if (v_isShared_839_ == 0)
{
lean_ctor_set(v___x_838_, 1, v___x_841_);
lean_ctor_set(v___x_838_, 0, v___x_842_);
v___x_844_ = v___x_838_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v___x_842_);
lean_ctor_set(v_reuseFailAlloc_845_, 1, v___x_841_);
v___x_844_ = v_reuseFailAlloc_845_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
v___y_819_ = v___x_844_;
goto v___jp_818_;
}
}
}
}
else
{
return v_b_817_;
}
v___jp_818_:
{
size_t v___x_820_; size_t v___x_821_; 
v___x_820_ = ((size_t)1ULL);
v___x_821_ = lean_usize_add(v_i_815_, v___x_820_);
v_i_815_ = v___x_821_;
v_b_817_ = v___y_819_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Rewrites_evalExact_spec__10___boxed(lean_object* v___x_848_, lean_object* v___x_849_, lean_object* v_as_850_, lean_object* v_i_851_, lean_object* v_stop_852_, lean_object* v_b_853_){
_start:
{
uint8_t v___x_27065__boxed_854_; uint8_t v___x_27066__boxed_855_; size_t v_i_boxed_856_; size_t v_stop_boxed_857_; lean_object* v_res_858_; 
v___x_27065__boxed_854_ = lean_unbox(v___x_848_);
v___x_27066__boxed_855_ = lean_unbox(v___x_849_);
v_i_boxed_856_ = lean_unbox_usize(v_i_851_);
lean_dec(v_i_851_);
v_stop_boxed_857_ = lean_unbox_usize(v_stop_852_);
lean_dec(v_stop_852_);
v_res_858_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Rewrites_evalExact_spec__10(v___x_27065__boxed_854_, v___x_27066__boxed_855_, v_as_850_, v_i_boxed_856_, v_stop_boxed_857_, v_b_853_);
lean_dec_ref(v_as_850_);
return v_res_858_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Rewrites_evalExact_spec__8(lean_object* v_as_859_, size_t v_i_860_, size_t v_stop_861_, lean_object* v_b_862_){
_start:
{
uint8_t v___x_863_; 
v___x_863_ = lean_usize_dec_eq(v_i_860_, v_stop_861_);
if (v___x_863_ == 0)
{
lean_object* v___x_864_; lean_object* v___x_865_; size_t v___x_866_; size_t v___x_867_; 
v___x_864_ = lean_array_uget_borrowed(v_as_859_, v_i_860_);
lean_inc(v___x_864_);
v___x_865_ = l_Lean_NameSet_insert(v_b_862_, v___x_864_);
v___x_866_ = ((size_t)1ULL);
v___x_867_ = lean_usize_add(v_i_860_, v___x_866_);
v_i_860_ = v___x_867_;
v_b_862_ = v___x_865_;
goto _start;
}
else
{
return v_b_862_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Rewrites_evalExact_spec__8___boxed(lean_object* v_as_869_, lean_object* v_i_870_, lean_object* v_stop_871_, lean_object* v_b_872_){
_start:
{
size_t v_i_boxed_873_; size_t v_stop_boxed_874_; lean_object* v_res_875_; 
v_i_boxed_873_ = lean_unbox_usize(v_i_870_);
lean_dec(v_i_870_);
v_stop_boxed_874_ = lean_unbox_usize(v_stop_871_);
lean_dec(v_stop_871_);
v_res_875_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Rewrites_evalExact_spec__8(v_as_869_, v_i_boxed_873_, v_stop_boxed_874_, v_b_872_);
lean_dec_ref(v_as_869_);
return v_res_875_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__9(size_t v_sz_879_, size_t v_i_880_, lean_object* v_bs_881_){
_start:
{
uint8_t v___x_882_; 
v___x_882_ = lean_usize_dec_lt(v_i_880_, v_sz_879_);
if (v___x_882_ == 0)
{
lean_object* v___x_883_; 
v___x_883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_883_, 0, v_bs_881_);
return v___x_883_;
}
else
{
lean_object* v_v_884_; lean_object* v___x_885_; uint8_t v___x_886_; 
v_v_884_ = lean_array_uget(v_bs_881_, v_i_880_);
v___x_885_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__9___closed__1));
lean_inc(v_v_884_);
v___x_886_ = l_Lean_Syntax_isOfKind(v_v_884_, v___x_885_);
if (v___x_886_ == 0)
{
lean_object* v___x_887_; 
lean_dec(v_v_884_);
lean_dec_ref(v_bs_881_);
v___x_887_ = lean_box(0);
return v___x_887_;
}
else
{
lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v_bs_x27_890_; lean_object* v_forbidden_891_; size_t v___x_892_; size_t v___x_893_; lean_object* v___x_894_; 
v___x_888_ = lean_unsigned_to_nat(1u);
v___x_889_ = lean_unsigned_to_nat(0u);
v_bs_x27_890_ = lean_array_uset(v_bs_881_, v_i_880_, v___x_889_);
v_forbidden_891_ = l_Lean_Syntax_getArg(v_v_884_, v___x_888_);
lean_dec(v_v_884_);
v___x_892_ = ((size_t)1ULL);
v___x_893_ = lean_usize_add(v_i_880_, v___x_892_);
v___x_894_ = lean_array_uset(v_bs_x27_890_, v_i_880_, v_forbidden_891_);
v_i_880_ = v___x_893_;
v_bs_881_ = v___x_894_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__9___boxed(lean_object* v_sz_896_, lean_object* v_i_897_, lean_object* v_bs_898_){
_start:
{
size_t v_sz_boxed_899_; size_t v_i_boxed_900_; lean_object* v_res_901_; 
v_sz_boxed_899_ = lean_unbox_usize(v_sz_896_);
lean_dec(v_sz_896_);
v_i_boxed_900_ = lean_unbox_usize(v_i_897_);
lean_dec(v_i_897_);
v_res_901_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__9(v_sz_boxed_899_, v_i_boxed_900_, v_bs_898_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact(lean_object* v_stx_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_){
_start:
{
lean_object* v___y_936_; lean_object* v___y_937_; lean_object* v___y_938_; lean_object* v___y_939_; lean_object* v___y_940_; lean_object* v___y_941_; lean_object* v___y_942_; lean_object* v___y_943_; lean_object* v___y_944_; lean_object* v___y_945_; lean_object* v___y_946_; lean_object* v___y_947_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; uint8_t v___x_955_; 
v___x_951_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___closed__0));
v___x_952_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___closed__1));
v___x_953_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___closed__2));
v___x_954_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___closed__4));
lean_inc(v_stx_925_);
v___x_955_ = l_Lean_Syntax_isOfKind(v_stx_925_, v___x_954_);
if (v___x_955_ == 0)
{
lean_object* v___x_956_; 
lean_dec(v_stx_925_);
v___x_956_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__0___redArg();
return v___x_956_;
}
else
{
lean_object* v___f_957_; lean_object* v___x_958_; lean_object* v_tk_959_; lean_object* v___y_961_; lean_object* v___y_962_; lean_object* v___y_963_; lean_object* v___y_964_; lean_object* v___y_965_; lean_object* v___y_966_; lean_object* v___y_967_; lean_object* v___y_968_; lean_object* v___y_969_; lean_object* v___y_970_; lean_object* v___y_971_; lean_object* v___y_972_; lean_object* v___y_999_; lean_object* v___y_1000_; lean_object* v___y_1001_; lean_object* v___y_1002_; lean_object* v___y_1003_; lean_object* v___y_1004_; lean_object* v___y_1005_; lean_object* v___y_1006_; lean_object* v___y_1007_; lean_object* v___y_1008_; lean_object* v___y_1009_; lean_object* v___y_1010_; lean_object* v___y_1011_; lean_object* v___y_1023_; lean_object* v_forbidden_1024_; lean_object* v___y_1025_; lean_object* v___y_1026_; lean_object* v___y_1027_; lean_object* v___y_1028_; lean_object* v___y_1029_; lean_object* v___y_1030_; lean_object* v___y_1031_; lean_object* v___y_1032_; lean_object* v___y_1047_; lean_object* v___y_1048_; lean_object* v___y_1049_; lean_object* v___y_1050_; lean_object* v___y_1051_; lean_object* v___y_1052_; lean_object* v___y_1053_; lean_object* v___y_1054_; lean_object* v___y_1055_; lean_object* v___y_1056_; lean_object* v___x_1061_; lean_object* v_loc_1063_; lean_object* v___y_1064_; lean_object* v___y_1065_; lean_object* v___y_1066_; lean_object* v___y_1067_; lean_object* v___y_1068_; lean_object* v___y_1069_; lean_object* v___y_1070_; lean_object* v___y_1071_; lean_object* v___x_1098_; uint8_t v___x_1099_; 
v___f_957_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___closed__5));
v___x_958_ = lean_unsigned_to_nat(0u);
v_tk_959_ = l_Lean_Syntax_getArg(v_stx_925_, v___x_958_);
v___x_1061_ = lean_unsigned_to_nat(1u);
v___x_1098_ = l_Lean_Syntax_getArg(v_stx_925_, v___x_1061_);
v___x_1099_ = l_Lean_Syntax_isNone(v___x_1098_);
if (v___x_1099_ == 0)
{
uint8_t v___x_1100_; 
lean_inc(v___x_1098_);
v___x_1100_ = l_Lean_Syntax_matchesNull(v___x_1098_, v___x_1061_);
if (v___x_1100_ == 0)
{
lean_object* v___x_1101_; 
lean_dec(v___x_1098_);
lean_dec(v_tk_959_);
lean_dec(v_stx_925_);
v___x_1101_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__0___redArg();
return v___x_1101_;
}
else
{
lean_object* v_loc_1102_; lean_object* v___x_1103_; 
v_loc_1102_ = l_Lean_Syntax_getArg(v___x_1098_, v___x_958_);
lean_dec(v___x_1098_);
v___x_1103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1103_, 0, v_loc_1102_);
v_loc_1063_ = v___x_1103_;
v___y_1064_ = v_a_926_;
v___y_1065_ = v_a_927_;
v___y_1066_ = v_a_928_;
v___y_1067_ = v_a_929_;
v___y_1068_ = v_a_930_;
v___y_1069_ = v_a_931_;
v___y_1070_ = v_a_932_;
v___y_1071_ = v_a_933_;
goto v___jp_1062_;
}
}
else
{
lean_object* v___x_1104_; 
lean_dec(v___x_1098_);
v___x_1104_ = lean_box(0);
v_loc_1063_ = v___x_1104_;
v___y_1064_ = v_a_926_;
v___y_1065_ = v_a_927_;
v___y_1066_ = v_a_928_;
v___y_1067_ = v_a_929_;
v___y_1068_ = v_a_930_;
v___y_1069_ = v_a_931_;
v___y_1070_ = v_a_932_;
v___y_1071_ = v_a_933_;
goto v___jp_1062_;
}
v___jp_960_:
{
lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_973_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___closed__7));
v___x_974_ = lean_unsigned_to_nat(90u);
v___x_975_ = l_Lean_reportOutOfHeartbeats(v___x_973_, v_tk_959_, v___x_974_, v___y_966_, v___y_968_);
if (lean_obj_tag(v___x_975_) == 0)
{
lean_object* v___x_976_; 
lean_dec_ref_known(v___x_975_, 1);
v___x_976_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_967_, v___y_971_, v___y_962_, v___y_966_, v___y_968_);
if (lean_obj_tag(v___x_976_) == 0)
{
lean_object* v_a_977_; lean_object* v___f_978_; lean_object* v___x_979_; lean_object* v___f_980_; 
v_a_977_ = lean_ctor_get(v___x_976_, 0);
lean_inc_n(v_a_977_, 2);
lean_dec_ref_known(v___x_976_, 1);
lean_inc(v_tk_959_);
lean_inc(v___y_972_);
lean_inc(v___y_961_);
v___f_978_ = lean_alloc_closure((void*)(l_Lean_Elab_Rewrites_evalExact___lam__2___boxed), 16, 6);
lean_closure_set(v___f_978_, 0, v___y_961_);
lean_closure_set(v___f_978_, 1, v_a_977_);
lean_closure_set(v___f_978_, 2, v___y_972_);
lean_closure_set(v___f_978_, 3, v_tk_959_);
lean_closure_set(v___f_978_, 4, v___x_974_);
lean_closure_set(v___f_978_, 5, v___x_958_);
v___x_979_ = lean_box(v___x_955_);
v___f_980_ = lean_alloc_closure((void*)(l_Lean_Elab_Rewrites_evalExact___lam__3___boxed), 19, 10);
lean_closure_set(v___f_980_, 0, v_a_977_);
lean_closure_set(v___f_980_, 1, v___y_961_);
lean_closure_set(v___f_980_, 2, v___y_972_);
lean_closure_set(v___f_980_, 3, v___x_979_);
lean_closure_set(v___f_980_, 4, v_tk_959_);
lean_closure_set(v___f_980_, 5, v___x_974_);
lean_closure_set(v___f_980_, 6, v___x_958_);
lean_closure_set(v___f_980_, 7, v___x_951_);
lean_closure_set(v___f_980_, 8, v___x_952_);
lean_closure_set(v___f_980_, 9, v___x_953_);
if (lean_obj_tag(v___y_965_) == 0)
{
lean_object* v___x_981_; 
v___x_981_ = lean_box(0);
v___y_936_ = v___y_962_;
v___y_937_ = v___f_980_;
v___y_938_ = v___y_963_;
v___y_939_ = v___y_964_;
v___y_940_ = v___y_966_;
v___y_941_ = v___y_968_;
v___y_942_ = v___y_967_;
v___y_943_ = v___y_969_;
v___y_944_ = v___y_971_;
v___y_945_ = v___y_970_;
v___y_946_ = v___f_978_;
v___y_947_ = v___x_981_;
goto v___jp_935_;
}
else
{
lean_object* v_val_982_; lean_object* v___x_984_; uint8_t v_isShared_985_; uint8_t v_isSharedCheck_989_; 
v_val_982_ = lean_ctor_get(v___y_965_, 0);
v_isSharedCheck_989_ = !lean_is_exclusive(v___y_965_);
if (v_isSharedCheck_989_ == 0)
{
v___x_984_ = v___y_965_;
v_isShared_985_ = v_isSharedCheck_989_;
goto v_resetjp_983_;
}
else
{
lean_inc(v_val_982_);
lean_dec(v___y_965_);
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
v___y_936_ = v___y_962_;
v___y_937_ = v___f_980_;
v___y_938_ = v___y_963_;
v___y_939_ = v___y_964_;
v___y_940_ = v___y_966_;
v___y_941_ = v___y_968_;
v___y_942_ = v___y_967_;
v___y_943_ = v___y_969_;
v___y_944_ = v___y_971_;
v___y_945_ = v___y_970_;
v___y_946_ = v___f_978_;
v___y_947_ = v___x_987_;
goto v___jp_935_;
}
}
}
}
else
{
lean_object* v_a_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_997_; 
lean_dec(v___y_972_);
lean_dec(v___y_965_);
lean_dec(v___y_961_);
lean_dec(v_tk_959_);
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
lean_dec(v___y_965_);
lean_dec(v___y_961_);
lean_dec(v_tk_959_);
return v___x_975_;
}
}
v___jp_998_:
{
size_t v_sz_1012_; size_t v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; uint8_t v___x_1016_; 
v_sz_1012_ = lean_array_size(v___y_1011_);
v___x_1013_ = ((size_t)0ULL);
v___x_1014_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__7(v_sz_1012_, v___x_1013_, v___y_1011_);
v___x_1015_ = lean_array_get_size(v___x_1014_);
v___x_1016_ = lean_nat_dec_lt(v___x_958_, v___x_1015_);
if (v___x_1016_ == 0)
{
lean_dec_ref(v___x_1014_);
lean_inc(v___y_1003_);
v___y_961_ = v___y_999_;
v___y_962_ = v___y_1000_;
v___y_963_ = v___y_1001_;
v___y_964_ = v___y_1002_;
v___y_965_ = v___y_1005_;
v___y_966_ = v___y_1004_;
v___y_967_ = v___y_1007_;
v___y_968_ = v___y_1006_;
v___y_969_ = v___y_1008_;
v___y_970_ = v___y_1010_;
v___y_971_ = v___y_1009_;
v___y_972_ = v___y_1003_;
goto v___jp_960_;
}
else
{
uint8_t v___x_1017_; 
v___x_1017_ = lean_nat_dec_le(v___x_1015_, v___x_1015_);
if (v___x_1017_ == 0)
{
if (v___x_1016_ == 0)
{
lean_dec_ref(v___x_1014_);
lean_inc(v___y_1003_);
v___y_961_ = v___y_999_;
v___y_962_ = v___y_1000_;
v___y_963_ = v___y_1001_;
v___y_964_ = v___y_1002_;
v___y_965_ = v___y_1005_;
v___y_966_ = v___y_1004_;
v___y_967_ = v___y_1007_;
v___y_968_ = v___y_1006_;
v___y_969_ = v___y_1008_;
v___y_970_ = v___y_1010_;
v___y_971_ = v___y_1009_;
v___y_972_ = v___y_1003_;
goto v___jp_960_;
}
else
{
size_t v___x_1018_; lean_object* v___x_1019_; 
v___x_1018_ = lean_usize_of_nat(v___x_1015_);
lean_inc(v___y_1003_);
v___x_1019_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Rewrites_evalExact_spec__8(v___x_1014_, v___x_1013_, v___x_1018_, v___y_1003_);
lean_dec_ref(v___x_1014_);
v___y_961_ = v___y_999_;
v___y_962_ = v___y_1000_;
v___y_963_ = v___y_1001_;
v___y_964_ = v___y_1002_;
v___y_965_ = v___y_1005_;
v___y_966_ = v___y_1004_;
v___y_967_ = v___y_1007_;
v___y_968_ = v___y_1006_;
v___y_969_ = v___y_1008_;
v___y_970_ = v___y_1010_;
v___y_971_ = v___y_1009_;
v___y_972_ = v___x_1019_;
goto v___jp_960_;
}
}
else
{
size_t v___x_1020_; lean_object* v___x_1021_; 
v___x_1020_ = lean_usize_of_nat(v___x_1015_);
lean_inc(v___y_1003_);
v___x_1021_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Rewrites_evalExact_spec__8(v___x_1014_, v___x_1013_, v___x_1020_, v___y_1003_);
lean_dec_ref(v___x_1014_);
v___y_961_ = v___y_999_;
v___y_962_ = v___y_1000_;
v___y_963_ = v___y_1001_;
v___y_964_ = v___y_1002_;
v___y_965_ = v___y_1005_;
v___y_966_ = v___y_1004_;
v___y_967_ = v___y_1007_;
v___y_968_ = v___y_1006_;
v___y_969_ = v___y_1008_;
v___y_970_ = v___y_1010_;
v___y_971_ = v___y_1009_;
v___y_972_ = v___x_1021_;
goto v___jp_960_;
}
}
}
v___jp_1022_:
{
lean_object* v___x_1033_; 
v___x_1033_ = l_Lean_Meta_Rewrites_createModuleTreeRef(v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_);
if (lean_obj_tag(v___x_1033_) == 0)
{
lean_object* v_a_1034_; lean_object* v___x_1035_; 
v_a_1034_ = lean_ctor_get(v___x_1033_, 0);
lean_inc(v_a_1034_);
lean_dec_ref_known(v___x_1033_, 1);
v___x_1035_ = l_Lean_NameSet_empty;
if (lean_obj_tag(v_forbidden_1024_) == 0)
{
lean_object* v___x_1036_; 
v___x_1036_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___closed__8));
v___y_999_ = v_a_1034_;
v___y_1000_ = v___y_1030_;
v___y_1001_ = v___y_1028_;
v___y_1002_ = v___y_1027_;
v___y_1003_ = v___x_1035_;
v___y_1004_ = v___y_1031_;
v___y_1005_ = v___y_1023_;
v___y_1006_ = v___y_1032_;
v___y_1007_ = v___y_1026_;
v___y_1008_ = v___y_1025_;
v___y_1009_ = v___y_1029_;
v___y_1010_ = v___f_957_;
v___y_1011_ = v___x_1036_;
goto v___jp_998_;
}
else
{
lean_object* v_val_1037_; 
v_val_1037_ = lean_ctor_get(v_forbidden_1024_, 0);
lean_inc(v_val_1037_);
lean_dec_ref_known(v_forbidden_1024_, 1);
v___y_999_ = v_a_1034_;
v___y_1000_ = v___y_1030_;
v___y_1001_ = v___y_1028_;
v___y_1002_ = v___y_1027_;
v___y_1003_ = v___x_1035_;
v___y_1004_ = v___y_1031_;
v___y_1005_ = v___y_1023_;
v___y_1006_ = v___y_1032_;
v___y_1007_ = v___y_1026_;
v___y_1008_ = v___y_1025_;
v___y_1009_ = v___y_1029_;
v___y_1010_ = v___f_957_;
v___y_1011_ = v_val_1037_;
goto v___jp_998_;
}
}
else
{
lean_object* v_a_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1045_; 
lean_dec(v_forbidden_1024_);
lean_dec(v___y_1023_);
lean_dec(v_tk_959_);
v_a_1038_ = lean_ctor_get(v___x_1033_, 0);
v_isSharedCheck_1045_ = !lean_is_exclusive(v___x_1033_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_1040_ = v___x_1033_;
v_isShared_1041_ = v_isSharedCheck_1045_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_a_1038_);
lean_dec(v___x_1033_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1045_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v___x_1043_; 
if (v_isShared_1041_ == 0)
{
v___x_1043_ = v___x_1040_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v_a_1038_);
v___x_1043_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
return v___x_1043_;
}
}
}
}
v___jp_1046_:
{
size_t v_sz_1057_; size_t v___x_1058_; lean_object* v___x_1059_; 
v_sz_1057_ = lean_array_size(v___y_1056_);
v___x_1058_ = ((size_t)0ULL);
v___x_1059_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__9(v_sz_1057_, v___x_1058_, v___y_1056_);
if (lean_obj_tag(v___x_1059_) == 0)
{
lean_object* v___x_1060_; 
lean_dec(v___y_1051_);
lean_dec(v_tk_959_);
v___x_1060_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__0___redArg();
return v___x_1060_;
}
else
{
v___y_1023_ = v___y_1051_;
v_forbidden_1024_ = v___x_1059_;
v___y_1025_ = v___y_1055_;
v___y_1026_ = v___y_1050_;
v___y_1027_ = v___y_1049_;
v___y_1028_ = v___y_1052_;
v___y_1029_ = v___y_1047_;
v___y_1030_ = v___y_1048_;
v___y_1031_ = v___y_1054_;
v___y_1032_ = v___y_1053_;
goto v___jp_1022_;
}
}
v___jp_1062_:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; uint8_t v___x_1074_; 
v___x_1072_ = lean_unsigned_to_nat(2u);
v___x_1073_ = l_Lean_Syntax_getArg(v_stx_925_, v___x_1072_);
lean_dec(v_stx_925_);
v___x_1074_ = l_Lean_Syntax_isNone(v___x_1073_);
if (v___x_1074_ == 0)
{
uint8_t v___x_1075_; 
lean_inc(v___x_1073_);
v___x_1075_ = l_Lean_Syntax_matchesNull(v___x_1073_, v___x_1061_);
if (v___x_1075_ == 0)
{
lean_object* v___x_1076_; 
lean_dec(v___x_1073_);
lean_dec(v_loc_1063_);
lean_dec(v_tk_959_);
v___x_1076_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__0___redArg();
return v___x_1076_;
}
else
{
lean_object* v___x_1077_; lean_object* v___x_1078_; uint8_t v___x_1079_; 
v___x_1077_ = l_Lean_Syntax_getArg(v___x_1073_, v___x_958_);
lean_dec(v___x_1073_);
v___x_1078_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___closed__10));
lean_inc(v___x_1077_);
v___x_1079_ = l_Lean_Syntax_isOfKind(v___x_1077_, v___x_1078_);
if (v___x_1079_ == 0)
{
lean_object* v___x_1080_; 
lean_dec(v___x_1077_);
lean_dec(v_loc_1063_);
lean_dec(v_tk_959_);
v___x_1080_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__0___redArg();
return v___x_1080_;
}
else
{
lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; uint8_t v___x_1085_; 
v___x_1081_ = l_Lean_Syntax_getArg(v___x_1077_, v___x_1061_);
lean_dec(v___x_1077_);
v___x_1082_ = l_Lean_Syntax_getArgs(v___x_1081_);
lean_dec(v___x_1081_);
v___x_1083_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___closed__11));
v___x_1084_ = lean_array_get_size(v___x_1082_);
v___x_1085_ = lean_nat_dec_lt(v___x_958_, v___x_1084_);
if (v___x_1085_ == 0)
{
lean_dec_ref(v___x_1082_);
v___y_1047_ = v___y_1068_;
v___y_1048_ = v___y_1069_;
v___y_1049_ = v___y_1066_;
v___y_1050_ = v___y_1065_;
v___y_1051_ = v_loc_1063_;
v___y_1052_ = v___y_1067_;
v___y_1053_ = v___y_1071_;
v___y_1054_ = v___y_1070_;
v___y_1055_ = v___y_1064_;
v___y_1056_ = v___x_1083_;
goto v___jp_1046_;
}
else
{
lean_object* v___x_1086_; lean_object* v___x_1087_; uint8_t v___x_1088_; 
v___x_1086_ = lean_box(v___x_1079_);
v___x_1087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1087_, 0, v___x_1086_);
lean_ctor_set(v___x_1087_, 1, v___x_1083_);
v___x_1088_ = lean_nat_dec_le(v___x_1084_, v___x_1084_);
if (v___x_1088_ == 0)
{
if (v___x_1085_ == 0)
{
lean_dec_ref_known(v___x_1087_, 2);
lean_dec_ref(v___x_1082_);
v___y_1047_ = v___y_1068_;
v___y_1048_ = v___y_1069_;
v___y_1049_ = v___y_1066_;
v___y_1050_ = v___y_1065_;
v___y_1051_ = v_loc_1063_;
v___y_1052_ = v___y_1067_;
v___y_1053_ = v___y_1071_;
v___y_1054_ = v___y_1070_;
v___y_1055_ = v___y_1064_;
v___y_1056_ = v___x_1083_;
goto v___jp_1046_;
}
else
{
size_t v___x_1089_; size_t v___x_1090_; lean_object* v___x_1091_; lean_object* v_snd_1092_; 
v___x_1089_ = ((size_t)0ULL);
v___x_1090_ = lean_usize_of_nat(v___x_1084_);
v___x_1091_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Rewrites_evalExact_spec__10(v___x_1079_, v___x_1074_, v___x_1082_, v___x_1089_, v___x_1090_, v___x_1087_);
lean_dec_ref(v___x_1082_);
v_snd_1092_ = lean_ctor_get(v___x_1091_, 1);
lean_inc(v_snd_1092_);
lean_dec_ref(v___x_1091_);
v___y_1047_ = v___y_1068_;
v___y_1048_ = v___y_1069_;
v___y_1049_ = v___y_1066_;
v___y_1050_ = v___y_1065_;
v___y_1051_ = v_loc_1063_;
v___y_1052_ = v___y_1067_;
v___y_1053_ = v___y_1071_;
v___y_1054_ = v___y_1070_;
v___y_1055_ = v___y_1064_;
v___y_1056_ = v_snd_1092_;
goto v___jp_1046_;
}
}
else
{
size_t v___x_1093_; size_t v___x_1094_; lean_object* v___x_1095_; lean_object* v_snd_1096_; 
v___x_1093_ = ((size_t)0ULL);
v___x_1094_ = lean_usize_of_nat(v___x_1084_);
v___x_1095_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Rewrites_evalExact_spec__10(v___x_1079_, v___x_1074_, v___x_1082_, v___x_1093_, v___x_1094_, v___x_1087_);
lean_dec_ref(v___x_1082_);
v_snd_1096_ = lean_ctor_get(v___x_1095_, 1);
lean_inc(v_snd_1096_);
lean_dec_ref(v___x_1095_);
v___y_1047_ = v___y_1068_;
v___y_1048_ = v___y_1069_;
v___y_1049_ = v___y_1066_;
v___y_1050_ = v___y_1065_;
v___y_1051_ = v_loc_1063_;
v___y_1052_ = v___y_1067_;
v___y_1053_ = v___y_1071_;
v___y_1054_ = v___y_1070_;
v___y_1055_ = v___y_1064_;
v___y_1056_ = v_snd_1096_;
goto v___jp_1046_;
}
}
}
}
}
else
{
lean_object* v___x_1097_; 
lean_dec(v___x_1073_);
v___x_1097_ = lean_box(0);
v___y_1023_ = v_loc_1063_;
v_forbidden_1024_ = v___x_1097_;
v___y_1025_ = v___y_1064_;
v___y_1026_ = v___y_1065_;
v___y_1027_ = v___y_1066_;
v___y_1028_ = v___y_1067_;
v___y_1029_ = v___y_1068_;
v___y_1030_ = v___y_1069_;
v___y_1031_ = v___y_1070_;
v___y_1032_ = v___y_1071_;
goto v___jp_1022_;
}
}
}
v___jp_935_:
{
lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; 
v___x_948_ = l_Lean_mkOptionalNode(v___y_947_);
v___x_949_ = l_Lean_Elab_Tactic_expandOptLocation(v___x_948_);
lean_dec(v___x_948_);
lean_inc_ref(v___y_945_);
v___x_950_ = l_Lean_Elab_Tactic_withLocation(v___x_949_, v___y_946_, v___y_937_, v___y_945_, v___y_943_, v___y_942_, v___y_939_, v___y_938_, v___y_944_, v___y_936_, v___y_940_, v___y_941_);
lean_dec(v___x_949_);
return v___x_950_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact___boxed(lean_object* v_stx_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_){
_start:
{
lean_object* v_res_1115_; 
v_res_1115_ = l_Lean_Elab_Rewrites_evalExact(v_stx_1105_, v_a_1106_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_);
lean_dec(v_a_1113_);
lean_dec_ref(v_a_1112_);
lean_dec(v_a_1111_);
lean_dec_ref(v_a_1110_);
lean_dec(v_a_1109_);
lean_dec_ref(v_a_1108_);
lean_dec(v_a_1107_);
lean_dec_ref(v_a_1106_);
return v_res_1115_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__1(lean_object* v_00_u03b1_1116_, lean_object* v_msg_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_){
_start:
{
lean_object* v___x_1127_; 
v___x_1127_ = l_Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__1___redArg(v_msg_1117_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_);
return v___x_1127_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__1___boxed(lean_object* v_00_u03b1_1128_, lean_object* v_msg_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_){
_start:
{
lean_object* v_res_1139_; 
v_res_1139_ = l_Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__1(v_00_u03b1_1128_, v_msg_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_);
lean_dec(v___y_1137_);
lean_dec_ref(v___y_1136_);
lean_dec(v___y_1135_);
lean_dec_ref(v___y_1134_);
lean_dec(v___y_1133_);
lean_dec_ref(v___y_1132_);
lean_dec(v___y_1131_);
lean_dec_ref(v___y_1130_);
return v_res_1139_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__5(lean_object* v_f_1140_, lean_object* v_tk_1141_, lean_object* v_as_1142_, lean_object* v_as_x27_1143_, lean_object* v_b_1144_, lean_object* v_a_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_){
_start:
{
lean_object* v___x_1155_; 
v___x_1155_ = l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__5___redArg(v_f_1140_, v_tk_1141_, v_as_x27_1143_, v_b_1144_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_);
return v___x_1155_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__5___boxed(lean_object* v_f_1156_, lean_object* v_tk_1157_, lean_object* v_as_1158_, lean_object* v_as_x27_1159_, lean_object* v_b_1160_, lean_object* v_a_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_){
_start:
{
lean_object* v_res_1171_; 
v_res_1171_ = l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__5(v_f_1156_, v_tk_1157_, v_as_1158_, v_as_x27_1159_, v_b_1160_, v_a_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_);
lean_dec(v___y_1169_);
lean_dec_ref(v___y_1168_);
lean_dec(v___y_1167_);
lean_dec_ref(v___y_1166_);
lean_dec(v___y_1165_);
lean_dec_ref(v___y_1164_);
lean_dec(v___y_1163_);
lean_dec_ref(v___y_1162_);
lean_dec(v_as_x27_1159_);
lean_dec(v_as_1158_);
return v_res_1171_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1(){
_start:
{
lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; 
v___x_1181_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1182_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___closed__4));
v___x_1183_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___closed__3));
v___x_1184_ = lean_alloc_closure((void*)(l_Lean_Elab_Rewrites_evalExact___boxed), 10, 0);
v___x_1185_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1181_, v___x_1182_, v___x_1183_, v___x_1184_);
return v___x_1185_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___boxed(lean_object* v_a_1186_){
_start:
{
lean_object* v_res_1187_; 
v_res_1187_ = l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1();
return v_res_1187_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3(){
_start:
{
lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; 
v___x_1214_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___closed__3));
v___x_1215_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__6));
v___x_1216_ = l_Lean_addBuiltinDeclarationRanges(v___x_1214_, v___x_1215_);
return v___x_1216_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___boxed(lean_object* v_a_1217_){
_start:
{
lean_object* v_res_1218_; 
v_res_1218_ = l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3();
return v_res_1218_;
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
