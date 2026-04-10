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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_mkOptionalNode(lean_object*);
lean_object* l_Lean_Elab_Tactic_expandOptLocation(lean_object*);
lean_object* l_Lean_Elab_Tactic_withLocation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Elab_Tactic_saveState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
lean_object* l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMCtxImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_get_x3fInternal___redArg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__5___redArg___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Rewrites_evalExact___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "rewrites"};
static const lean_object* l_Lean_Elab_Rewrites_evalExact___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_Rewrites_evalExact___lam__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Rewrites_evalExact___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Rewrites_evalExact___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 174, 121, 91, 16, 171, 72, 14)}};
static const lean_object* l_Lean_Elab_Rewrites_evalExact___lam__1___closed__1 = (const lean_object*)&l_Lean_Elab_Rewrites_evalExact___lam__1___closed__1_value;
static const lean_string_object l_Lean_Elab_Rewrites_evalExact___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 60, .m_capacity = 60, .m_length = 59, .m_data = "Could not find any lemmas which can rewrite the hypothesis "};
static const lean_object* l_Lean_Elab_Rewrites_evalExact___lam__1___closed__2 = (const lean_object*)&l_Lean_Elab_Rewrites_evalExact___lam__1___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Rewrites_evalExact___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Rewrites_evalExact___lam__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_Rewrites_evalExact_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_Rewrites_evalExact_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Rewrites_evalExact___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "tacticTry_"};
static const lean_object* l_Lean_Elab_Rewrites_evalExact___lam__2___closed__0 = (const lean_object*)&l_Lean_Elab_Rewrites_evalExact___lam__2___closed__0_value;
static const lean_string_object l_Lean_Elab_Rewrites_evalExact___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "try"};
static const lean_object* l_Lean_Elab_Rewrites_evalExact___lam__2___closed__1 = (const lean_object*)&l_Lean_Elab_Rewrites_evalExact___lam__2___closed__1_value;
static const lean_string_object l_Lean_Elab_Rewrites_evalExact___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Lean_Elab_Rewrites_evalExact___lam__2___closed__2 = (const lean_object*)&l_Lean_Elab_Rewrites_evalExact___lam__2___closed__2_value;
static const lean_string_object l_Lean_Elab_Rewrites_evalExact___lam__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Lean_Elab_Rewrites_evalExact___lam__2___closed__3 = (const lean_object*)&l_Lean_Elab_Rewrites_evalExact___lam__2___closed__3_value;
static const lean_string_object l_Lean_Elab_Rewrites_evalExact___lam__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Elab_Rewrites_evalExact___lam__2___closed__4 = (const lean_object*)&l_Lean_Elab_Rewrites_evalExact___lam__2___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Rewrites_evalExact___lam__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Rewrites_evalExact___lam__2___closed__4_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Elab_Rewrites_evalExact___lam__2___closed__5 = (const lean_object*)&l_Lean_Elab_Rewrites_evalExact___lam__2___closed__5_value;
static const lean_string_object l_Lean_Elab_Rewrites_evalExact___lam__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticRfl"};
static const lean_object* l_Lean_Elab_Rewrites_evalExact___lam__2___closed__6 = (const lean_object*)&l_Lean_Elab_Rewrites_evalExact___lam__2___closed__6_value;
static const lean_string_object l_Lean_Elab_Rewrites_evalExact___lam__2___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rfl"};
static const lean_object* l_Lean_Elab_Rewrites_evalExact___lam__2___closed__7 = (const lean_object*)&l_Lean_Elab_Rewrites_evalExact___lam__2___closed__7_value;
static const lean_string_object l_Lean_Elab_Rewrites_evalExact___lam__2___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 53, .m_capacity = 53, .m_length = 52, .m_data = "Could not find any lemmas which can rewrite the goal"};
static const lean_object* l_Lean_Elab_Rewrites_evalExact___lam__2___closed__8 = (const lean_object*)&l_Lean_Elab_Rewrites_evalExact___lam__2___closed__8_value;
static lean_once_cell_t l_Lean_Elab_Rewrites_evalExact___lam__2___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Rewrites_evalExact___lam__2___closed__9;
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact___lam__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact___lam__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Rewrites_evalExact_spec__9(uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Rewrites_evalExact_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "group"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__8___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__8___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__8___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__8___closed__0_value),LEAN_SCALAR_PTR_LITERAL(206, 113, 20, 57, 188, 177, 187, 30)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__8___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__8___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__8(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Rewrites_evalExact_spec__7(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Rewrites_evalExact_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__6(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__6___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__1_spec__1(lean_object* v_msgData_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_){
_start:
{
lean_object* v___x_169_; lean_object* v_env_170_; lean_object* v___x_171_; lean_object* v_mctx_172_; lean_object* v_lctx_173_; lean_object* v_options_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_169_ = lean_st_ref_get(v___y_167_);
v_env_170_ = lean_ctor_get(v___x_169_, 0);
lean_inc_ref(v_env_170_);
lean_dec(v___x_169_);
v___x_171_ = lean_st_ref_get(v___y_165_);
v_mctx_172_ = lean_ctor_get(v___x_171_, 0);
lean_inc_ref(v_mctx_172_);
lean_dec(v___x_171_);
v_lctx_173_ = lean_ctor_get(v___y_164_, 2);
v_options_174_ = lean_ctor_get(v___y_166_, 2);
lean_inc_ref(v_options_174_);
lean_inc_ref(v_lctx_173_);
v___x_175_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_175_, 0, v_env_170_);
lean_ctor_set(v___x_175_, 1, v_mctx_172_);
lean_ctor_set(v___x_175_, 2, v_lctx_173_);
lean_ctor_set(v___x_175_, 3, v_options_174_);
v___x_176_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_176_, 0, v___x_175_);
lean_ctor_set(v___x_176_, 1, v_msgData_163_);
v___x_177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_177_, 0, v___x_176_);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__1_spec__1___boxed(lean_object* v_msgData_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_){
_start:
{
lean_object* v_res_184_; 
v_res_184_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__1_spec__1(v_msgData_178_, v___y_179_, v___y_180_, v___y_181_, v___y_182_);
lean_dec(v___y_182_);
lean_dec_ref(v___y_181_);
lean_dec(v___y_180_);
lean_dec_ref(v___y_179_);
return v_res_184_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__1___redArg(lean_object* v_msg_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_){
_start:
{
lean_object* v_ref_191_; lean_object* v___x_192_; lean_object* v_a_193_; lean_object* v___x_195_; uint8_t v_isShared_196_; uint8_t v_isSharedCheck_201_; 
v_ref_191_ = lean_ctor_get(v___y_188_, 5);
v___x_192_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__1_spec__1(v_msg_185_, v___y_186_, v___y_187_, v___y_188_, v___y_189_);
v_a_193_ = lean_ctor_get(v___x_192_, 0);
v_isSharedCheck_201_ = !lean_is_exclusive(v___x_192_);
if (v_isSharedCheck_201_ == 0)
{
v___x_195_ = v___x_192_;
v_isShared_196_ = v_isSharedCheck_201_;
goto v_resetjp_194_;
}
else
{
lean_inc(v_a_193_);
lean_dec(v___x_192_);
v___x_195_ = lean_box(0);
v_isShared_196_ = v_isSharedCheck_201_;
goto v_resetjp_194_;
}
v_resetjp_194_:
{
lean_object* v___x_197_; lean_object* v___x_199_; 
lean_inc(v_ref_191_);
v___x_197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_197_, 0, v_ref_191_);
lean_ctor_set(v___x_197_, 1, v_a_193_);
if (v_isShared_196_ == 0)
{
lean_ctor_set_tag(v___x_195_, 1);
lean_ctor_set(v___x_195_, 0, v___x_197_);
v___x_199_ = v___x_195_;
goto v_reusejp_198_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v___x_197_);
v___x_199_ = v_reuseFailAlloc_200_;
goto v_reusejp_198_;
}
v_reusejp_198_:
{
return v___x_199_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__1___redArg___boxed(lean_object* v_msg_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l_Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__1___redArg(v_msg_202_, v___y_203_, v___y_204_, v___y_205_, v___y_206_);
lean_dec(v___y_206_);
lean_dec_ref(v___y_205_);
lean_dec(v___y_204_);
lean_dec_ref(v___y_203_);
return v_res_208_;
}
}
static lean_object* _init_l_Lean_Elab_Rewrites_evalExact___lam__0___closed__1(void){
_start:
{
lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_210_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___lam__0___closed__0));
v___x_211_ = l_Lean_stringToMessageData(v___x_210_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact___lam__0(lean_object* v_x_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_){
_start:
{
lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_222_ = lean_obj_once(&l_Lean_Elab_Rewrites_evalExact___lam__0___closed__1, &l_Lean_Elab_Rewrites_evalExact___lam__0___closed__1_once, _init_l_Lean_Elab_Rewrites_evalExact___lam__0___closed__1);
v___x_223_ = l_Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__1___redArg(v___x_222_, v___y_217_, v___y_218_, v___y_219_, v___y_220_);
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact___lam__0___boxed(lean_object* v_x_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_){
_start:
{
lean_object* v_res_234_; 
v_res_234_ = l_Lean_Elab_Rewrites_evalExact___lam__0(v_x_224_, v___y_225_, v___y_226_, v___y_227_, v___y_228_, v___y_229_, v___y_230_, v___y_231_, v___y_232_);
lean_dec(v___y_232_);
lean_dec_ref(v___y_231_);
lean_dec(v___y_230_);
lean_dec_ref(v___y_229_);
lean_dec(v___y_228_);
lean_dec_ref(v___y_227_);
lean_dec(v___y_226_);
lean_dec_ref(v___y_225_);
lean_dec(v_x_224_);
return v_res_234_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__5___redArg___lam__0(lean_object* v_result_235_, lean_object* v_expr_236_, uint8_t v_symm_237_, lean_object* v_f_238_, lean_object* v_tk_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_){
_start:
{
lean_object* v___x_249_; 
v___x_249_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_241_, v___y_243_, v___y_245_, v___y_247_);
if (lean_obj_tag(v___x_249_) == 0)
{
lean_object* v_a_250_; lean_object* v_ref_251_; lean_object* v_eNew_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; 
v_a_250_ = lean_ctor_get(v___x_249_, 0);
lean_inc(v_a_250_);
lean_dec_ref(v___x_249_);
v_ref_251_ = lean_ctor_get(v___y_246_, 5);
v_eNew_252_ = lean_ctor_get(v_result_235_, 0);
v___x_253_ = lean_box(v_symm_237_);
v___x_254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_254_, 0, v_expr_236_);
lean_ctor_set(v___x_254_, 1, v___x_253_);
v___x_255_ = lean_box(0);
v___x_256_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_256_, 0, v___x_254_);
lean_ctor_set(v___x_256_, 1, v___x_255_);
lean_inc_ref(v_eNew_252_);
v___x_257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_257_, 0, v_eNew_252_);
v___x_258_ = l_Lean_Expr_fvar___override(v_f_238_);
v___x_259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_259_, 0, v___x_258_);
lean_inc(v_ref_251_);
v___x_260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_260_, 0, v_ref_251_);
v___x_261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_261_, 0, v_a_250_);
v___x_262_ = l_Lean_Meta_Tactic_TryThis_addRewriteSuggestion(v_tk_239_, v___x_256_, v___x_257_, v___x_259_, v___x_260_, v___x_261_, v___y_240_, v___y_241_, v___y_242_, v___y_243_, v___y_244_, v___y_245_, v___y_246_, v___y_247_);
return v___x_262_;
}
else
{
lean_object* v_a_263_; lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_270_; 
lean_dec(v_tk_239_);
lean_dec(v_f_238_);
lean_dec_ref(v_expr_236_);
v_a_263_ = lean_ctor_get(v___x_249_, 0);
v_isSharedCheck_270_ = !lean_is_exclusive(v___x_249_);
if (v_isSharedCheck_270_ == 0)
{
v___x_265_ = v___x_249_;
v_isShared_266_ = v_isSharedCheck_270_;
goto v_resetjp_264_;
}
else
{
lean_inc(v_a_263_);
lean_dec(v___x_249_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_270_;
goto v_resetjp_264_;
}
v_resetjp_264_:
{
lean_object* v___x_268_; 
if (v_isShared_266_ == 0)
{
v___x_268_ = v___x_265_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v_a_263_);
v___x_268_ = v_reuseFailAlloc_269_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
return v___x_268_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__5___redArg___lam__0___boxed(lean_object* v_result_271_, lean_object* v_expr_272_, lean_object* v_symm_273_, lean_object* v_f_274_, lean_object* v_tk_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_){
_start:
{
uint8_t v_symm_boxed_285_; lean_object* v_res_286_; 
v_symm_boxed_285_ = lean_unbox(v_symm_273_);
v_res_286_ = l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__5___redArg___lam__0(v_result_271_, v_expr_272_, v_symm_boxed_285_, v_f_274_, v_tk_275_, v___y_276_, v___y_277_, v___y_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_);
lean_dec(v___y_283_);
lean_dec_ref(v___y_282_);
lean_dec(v___y_281_);
lean_dec_ref(v___y_280_);
lean_dec(v___y_279_);
lean_dec_ref(v___y_278_);
lean_dec(v___y_277_);
lean_dec_ref(v___y_276_);
lean_dec_ref(v_result_271_);
return v_res_286_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__5___redArg(lean_object* v_f_287_, lean_object* v_tk_288_, lean_object* v_as_x27_289_, lean_object* v_b_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_){
_start:
{
if (lean_obj_tag(v_as_x27_289_) == 0)
{
lean_object* v___x_300_; 
lean_dec(v_tk_288_);
lean_dec(v_f_287_);
v___x_300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_300_, 0, v_b_290_);
return v___x_300_;
}
else
{
lean_object* v_head_301_; lean_object* v_tail_302_; lean_object* v_expr_303_; uint8_t v_symm_304_; lean_object* v_result_305_; lean_object* v_mctx_306_; lean_object* v___x_307_; lean_object* v___f_308_; lean_object* v___x_309_; 
v_head_301_ = lean_ctor_get(v_as_x27_289_, 0);
lean_inc(v_head_301_);
v_tail_302_ = lean_ctor_get(v_as_x27_289_, 1);
lean_inc(v_tail_302_);
lean_dec_ref(v_as_x27_289_);
v_expr_303_ = lean_ctor_get(v_head_301_, 0);
lean_inc_ref(v_expr_303_);
v_symm_304_ = lean_ctor_get_uint8(v_head_301_, sizeof(void*)*4);
v_result_305_ = lean_ctor_get(v_head_301_, 2);
lean_inc_ref(v_result_305_);
v_mctx_306_ = lean_ctor_get(v_head_301_, 3);
lean_inc_ref(v_mctx_306_);
lean_dec(v_head_301_);
v___x_307_ = lean_box(v_symm_304_);
lean_inc(v_tk_288_);
lean_inc(v_f_287_);
v___f_308_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__5___redArg___lam__0___boxed), 14, 5);
lean_closure_set(v___f_308_, 0, v_result_305_);
lean_closure_set(v___f_308_, 1, v_expr_303_);
lean_closure_set(v___f_308_, 2, v___x_307_);
lean_closure_set(v___f_308_, 3, v_f_287_);
lean_closure_set(v___f_308_, 4, v_tk_288_);
v___x_309_ = l_Lean_Meta_withMCtx___at___00Lean_Elab_Rewrites_evalExact_spec__4___redArg(v_mctx_306_, v___f_308_, v___y_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_, v___y_296_, v___y_297_, v___y_298_);
if (lean_obj_tag(v___x_309_) == 0)
{
lean_object* v___x_310_; 
lean_dec_ref(v___x_309_);
v___x_310_ = lean_box(0);
v_as_x27_289_ = v_tail_302_;
v_b_290_ = v___x_310_;
goto _start;
}
else
{
lean_dec(v_tail_302_);
lean_dec(v_tk_288_);
lean_dec(v_f_287_);
return v___x_309_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__5___redArg___boxed(lean_object* v_f_312_, lean_object* v_tk_313_, lean_object* v_as_x27_314_, lean_object* v_b_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_){
_start:
{
lean_object* v_res_325_; 
v_res_325_ = l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__5___redArg(v_f_312_, v_tk_313_, v_as_x27_314_, v_b_315_, v___y_316_, v___y_317_, v___y_318_, v___y_319_, v___y_320_, v___y_321_, v___y_322_, v___y_323_);
lean_dec(v___y_323_);
lean_dec_ref(v___y_322_);
lean_dec(v___y_321_);
lean_dec_ref(v___y_320_);
lean_dec(v___y_319_);
lean_dec_ref(v___y_318_);
lean_dec(v___y_317_);
lean_dec_ref(v___y_316_);
return v_res_325_;
}
}
static lean_object* _init_l_Lean_Elab_Rewrites_evalExact___lam__1___closed__3(void){
_start:
{
lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_330_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___lam__1___closed__2));
v___x_331_ = l_Lean_stringToMessageData(v___x_330_);
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact___lam__1(lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v___y_334_, lean_object* v_tk_335_, lean_object* v___x_336_, lean_object* v___x_337_, lean_object* v_f_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_){
_start:
{
lean_object* v___x_348_; 
lean_inc(v_f_338_);
v___x_348_ = l_Lean_FVarId_findDecl_x3f___redArg(v_f_338_, v___y_343_);
if (lean_obj_tag(v___x_348_) == 0)
{
lean_object* v_a_349_; lean_object* v___x_351_; uint8_t v_isShared_352_; uint8_t v_isSharedCheck_470_; 
v_a_349_ = lean_ctor_get(v___x_348_, 0);
v_isSharedCheck_470_ = !lean_is_exclusive(v___x_348_);
if (v_isSharedCheck_470_ == 0)
{
v___x_351_ = v___x_348_;
v_isShared_352_ = v_isSharedCheck_470_;
goto v_resetjp_350_;
}
else
{
lean_inc(v_a_349_);
lean_dec(v___x_348_);
v___x_351_ = lean_box(0);
v_isShared_352_ = v_isSharedCheck_470_;
goto v_resetjp_350_;
}
v_resetjp_350_:
{
if (lean_obj_tag(v_a_349_) == 1)
{
lean_object* v_val_353_; uint8_t v___x_354_; 
v_val_353_ = lean_ctor_get(v_a_349_, 0);
lean_inc(v_val_353_);
lean_dec_ref(v_a_349_);
v___x_354_ = l_Lean_LocalDecl_isImplementationDetail(v_val_353_);
lean_dec(v_val_353_);
if (v___x_354_ == 0)
{
lean_object* v___x_355_; 
lean_del_object(v___x_351_);
lean_inc(v_f_338_);
v___x_355_ = l_Lean_FVarId_getType___redArg(v_f_338_, v___y_343_, v___y_345_, v___y_346_);
if (lean_obj_tag(v___x_355_) == 0)
{
lean_object* v_a_356_; lean_object* v___x_357_; lean_object* v_a_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
v_a_356_ = lean_ctor_get(v___x_355_, 0);
lean_inc(v_a_356_);
lean_dec_ref(v___x_355_);
v___x_357_ = l_Lean_instantiateMVars___at___00Lean_Elab_Rewrites_evalExact_spec__2___redArg(v_a_356_, v___y_344_);
v_a_358_ = lean_ctor_get(v___x_357_, 0);
lean_inc(v_a_358_);
lean_dec_ref(v___x_357_);
v___x_359_ = lean_box(0);
lean_inc(v_f_338_);
v___x_360_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_360_, 0, v_f_338_);
lean_ctor_set(v___x_360_, 1, v___x_359_);
v___x_361_ = l_Lean_Meta_Rewrites_localHypotheses(v___x_360_, v___y_343_, v___y_344_, v___y_345_, v___y_346_);
lean_dec_ref(v___x_360_);
if (lean_obj_tag(v___x_361_) == 0)
{
lean_object* v_a_362_; uint8_t v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; 
v_a_362_ = lean_ctor_get(v___x_361_, 0);
lean_inc(v_a_362_);
lean_dec_ref(v___x_361_);
v___x_363_ = 2;
v___x_364_ = lean_unsigned_to_nat(20u);
v___x_365_ = lean_unsigned_to_nat(10u);
lean_inc(v_a_333_);
v___x_366_ = l_Lean_Meta_Rewrites_findRewrites(v_a_362_, v_a_332_, v_a_333_, v_a_358_, v___y_334_, v___x_363_, v___x_354_, v___x_364_, v___x_365_, v___y_343_, v___y_344_, v___y_345_, v___y_346_);
if (lean_obj_tag(v___x_366_) == 0)
{
lean_object* v_a_367_; lean_object* v___y_369_; lean_object* v___y_370_; lean_object* v___y_371_; lean_object* v___y_372_; lean_object* v___y_373_; lean_object* v___y_374_; lean_object* v___y_375_; lean_object* v___y_376_; lean_object* v___x_421_; lean_object* v___x_422_; 
v_a_367_ = lean_ctor_get(v___x_366_, 0);
lean_inc(v_a_367_);
lean_dec_ref(v___x_366_);
v___x_421_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___lam__1___closed__1));
v___x_422_ = l_Lean_reportOutOfHeartbeats(v___x_421_, v_tk_335_, v___x_336_, v___y_345_, v___y_346_);
if (lean_obj_tag(v___x_422_) == 0)
{
uint8_t v___x_423_; 
lean_dec_ref(v___x_422_);
v___x_423_ = l_List_isEmpty___redArg(v_a_367_);
if (v___x_423_ == 0)
{
v___y_369_ = v___y_339_;
v___y_370_ = v___y_340_;
v___y_371_ = v___y_341_;
v___y_372_ = v___y_342_;
v___y_373_ = v___y_343_;
v___y_374_ = v___y_344_;
v___y_375_ = v___y_345_;
v___y_376_ = v___y_346_;
goto v___jp_368_;
}
else
{
lean_object* v___x_424_; 
lean_dec(v_a_367_);
lean_dec(v___x_337_);
lean_dec(v_tk_335_);
lean_dec(v_a_333_);
v___x_424_ = l_Lean_FVarId_getUserName___redArg(v_f_338_, v___y_343_, v___y_345_, v___y_346_);
if (lean_obj_tag(v___x_424_) == 0)
{
lean_object* v_a_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; 
v_a_425_ = lean_ctor_get(v___x_424_, 0);
lean_inc(v_a_425_);
lean_dec_ref(v___x_424_);
v___x_426_ = lean_obj_once(&l_Lean_Elab_Rewrites_evalExact___lam__1___closed__3, &l_Lean_Elab_Rewrites_evalExact___lam__1___closed__3_once, _init_l_Lean_Elab_Rewrites_evalExact___lam__1___closed__3);
v___x_427_ = l_Lean_MessageData_ofName(v_a_425_);
v___x_428_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_428_, 0, v___x_426_);
lean_ctor_set(v___x_428_, 1, v___x_427_);
v___x_429_ = l_Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__1___redArg(v___x_428_, v___y_343_, v___y_344_, v___y_345_, v___y_346_);
return v___x_429_;
}
else
{
lean_object* v_a_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_437_; 
v_a_430_ = lean_ctor_get(v___x_424_, 0);
v_isSharedCheck_437_ = !lean_is_exclusive(v___x_424_);
if (v_isSharedCheck_437_ == 0)
{
v___x_432_ = v___x_424_;
v_isShared_433_ = v_isSharedCheck_437_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_a_430_);
lean_dec(v___x_424_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_437_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
lean_object* v___x_435_; 
if (v_isShared_433_ == 0)
{
v___x_435_ = v___x_432_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v_a_430_);
v___x_435_ = v_reuseFailAlloc_436_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
return v___x_435_;
}
}
}
}
}
else
{
lean_dec(v_a_367_);
lean_dec(v_f_338_);
lean_dec(v___x_337_);
lean_dec(v_tk_335_);
lean_dec(v_a_333_);
return v___x_422_;
}
v___jp_368_:
{
lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_377_ = lean_box(0);
lean_inc(v_a_367_);
lean_inc(v_f_338_);
v___x_378_ = l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__5___redArg(v_f_338_, v_tk_335_, v_a_367_, v___x_377_, v___y_369_, v___y_370_, v___y_371_, v___y_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_);
if (lean_obj_tag(v___x_378_) == 0)
{
lean_object* v___x_380_; uint8_t v_isShared_381_; uint8_t v_isSharedCheck_419_; 
v_isSharedCheck_419_ = !lean_is_exclusive(v___x_378_);
if (v_isSharedCheck_419_ == 0)
{
lean_object* v_unused_420_; 
v_unused_420_ = lean_ctor_get(v___x_378_, 0);
lean_dec(v_unused_420_);
v___x_380_ = v___x_378_;
v_isShared_381_ = v_isSharedCheck_419_;
goto v_resetjp_379_;
}
else
{
lean_dec(v___x_378_);
v___x_380_ = lean_box(0);
v_isShared_381_ = v_isSharedCheck_419_;
goto v_resetjp_379_;
}
v_resetjp_379_:
{
lean_object* v___x_382_; 
v___x_382_ = l_List_get_x3fInternal___redArg(v_a_367_, v___x_337_);
lean_dec(v_a_367_);
if (lean_obj_tag(v___x_382_) == 1)
{
lean_object* v_val_383_; lean_object* v___x_384_; lean_object* v_result_385_; lean_object* v_mctx_386_; lean_object* v_cache_387_; lean_object* v_zetaDeltaFVarIds_388_; lean_object* v_postponed_389_; lean_object* v_diag_390_; lean_object* v___x_392_; uint8_t v_isShared_393_; uint8_t v_isSharedCheck_414_; 
lean_del_object(v___x_380_);
v_val_383_ = lean_ctor_get(v___x_382_, 0);
lean_inc(v_val_383_);
lean_dec_ref(v___x_382_);
v___x_384_ = lean_st_ref_take(v___y_374_);
v_result_385_ = lean_ctor_get(v_val_383_, 2);
lean_inc_ref(v_result_385_);
v_mctx_386_ = lean_ctor_get(v_val_383_, 3);
lean_inc_ref(v_mctx_386_);
lean_dec(v_val_383_);
v_cache_387_ = lean_ctor_get(v___x_384_, 1);
v_zetaDeltaFVarIds_388_ = lean_ctor_get(v___x_384_, 2);
v_postponed_389_ = lean_ctor_get(v___x_384_, 3);
v_diag_390_ = lean_ctor_get(v___x_384_, 4);
v_isSharedCheck_414_ = !lean_is_exclusive(v___x_384_);
if (v_isSharedCheck_414_ == 0)
{
lean_object* v_unused_415_; 
v_unused_415_ = lean_ctor_get(v___x_384_, 0);
lean_dec(v_unused_415_);
v___x_392_ = v___x_384_;
v_isShared_393_ = v_isSharedCheck_414_;
goto v_resetjp_391_;
}
else
{
lean_inc(v_diag_390_);
lean_inc(v_postponed_389_);
lean_inc(v_zetaDeltaFVarIds_388_);
lean_inc(v_cache_387_);
lean_dec(v___x_384_);
v___x_392_ = lean_box(0);
v_isShared_393_ = v_isSharedCheck_414_;
goto v_resetjp_391_;
}
v_resetjp_391_:
{
lean_object* v___x_395_; 
if (v_isShared_393_ == 0)
{
lean_ctor_set(v___x_392_, 0, v_mctx_386_);
v___x_395_ = v___x_392_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v_mctx_386_);
lean_ctor_set(v_reuseFailAlloc_413_, 1, v_cache_387_);
lean_ctor_set(v_reuseFailAlloc_413_, 2, v_zetaDeltaFVarIds_388_);
lean_ctor_set(v_reuseFailAlloc_413_, 3, v_postponed_389_);
lean_ctor_set(v_reuseFailAlloc_413_, 4, v_diag_390_);
v___x_395_ = v_reuseFailAlloc_413_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
lean_object* v___x_396_; lean_object* v_eNew_397_; lean_object* v_eqProof_398_; lean_object* v_mvarIds_399_; lean_object* v___x_400_; 
v___x_396_ = lean_st_ref_set(v___y_374_, v___x_395_);
v_eNew_397_ = lean_ctor_get(v_result_385_, 0);
lean_inc_ref(v_eNew_397_);
v_eqProof_398_ = lean_ctor_get(v_result_385_, 1);
lean_inc_ref(v_eqProof_398_);
v_mvarIds_399_ = lean_ctor_get(v_result_385_, 2);
lean_inc(v_mvarIds_399_);
lean_dec_ref(v_result_385_);
v___x_400_ = l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore(v_a_333_, v_f_338_, v_eNew_397_, v_eqProof_398_, v___y_373_, v___y_374_, v___y_375_, v___y_376_);
if (lean_obj_tag(v___x_400_) == 0)
{
lean_object* v_a_401_; lean_object* v_mvarId_402_; lean_object* v___x_403_; lean_object* v___x_404_; 
v_a_401_ = lean_ctor_get(v___x_400_, 0);
lean_inc(v_a_401_);
lean_dec_ref(v___x_400_);
v_mvarId_402_ = lean_ctor_get(v_a_401_, 1);
lean_inc(v_mvarId_402_);
lean_dec(v_a_401_);
v___x_403_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_403_, 0, v_mvarId_402_);
lean_ctor_set(v___x_403_, 1, v_mvarIds_399_);
v___x_404_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_403_, v___y_370_, v___y_373_, v___y_374_, v___y_375_, v___y_376_);
return v___x_404_;
}
else
{
lean_object* v_a_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_412_; 
lean_dec(v_mvarIds_399_);
v_a_405_ = lean_ctor_get(v___x_400_, 0);
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_400_);
if (v_isSharedCheck_412_ == 0)
{
v___x_407_ = v___x_400_;
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_a_405_);
lean_dec(v___x_400_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v___x_410_; 
if (v_isShared_408_ == 0)
{
v___x_410_ = v___x_407_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v_a_405_);
v___x_410_ = v_reuseFailAlloc_411_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
return v___x_410_;
}
}
}
}
}
}
else
{
lean_object* v___x_417_; 
lean_dec(v___x_382_);
lean_dec(v_f_338_);
lean_dec(v_a_333_);
if (v_isShared_381_ == 0)
{
lean_ctor_set(v___x_380_, 0, v___x_377_);
v___x_417_ = v___x_380_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v___x_377_);
v___x_417_ = v_reuseFailAlloc_418_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
return v___x_417_;
}
}
}
}
else
{
lean_dec(v_a_367_);
lean_dec(v_f_338_);
lean_dec(v___x_337_);
lean_dec(v_a_333_);
return v___x_378_;
}
}
}
else
{
lean_object* v_a_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_445_; 
lean_dec(v_f_338_);
lean_dec(v___x_337_);
lean_dec(v_tk_335_);
lean_dec(v_a_333_);
v_a_438_ = lean_ctor_get(v___x_366_, 0);
v_isSharedCheck_445_ = !lean_is_exclusive(v___x_366_);
if (v_isSharedCheck_445_ == 0)
{
v___x_440_ = v___x_366_;
v_isShared_441_ = v_isSharedCheck_445_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_a_438_);
lean_dec(v___x_366_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_445_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v___x_443_; 
if (v_isShared_441_ == 0)
{
v___x_443_ = v___x_440_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v_a_438_);
v___x_443_ = v_reuseFailAlloc_444_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
return v___x_443_;
}
}
}
}
else
{
lean_object* v_a_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_453_; 
lean_dec(v_a_358_);
lean_dec(v_f_338_);
lean_dec(v___x_337_);
lean_dec(v_tk_335_);
lean_dec(v_a_333_);
lean_dec(v_a_332_);
v_a_446_ = lean_ctor_get(v___x_361_, 0);
v_isSharedCheck_453_ = !lean_is_exclusive(v___x_361_);
if (v_isSharedCheck_453_ == 0)
{
v___x_448_ = v___x_361_;
v_isShared_449_ = v_isSharedCheck_453_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_a_446_);
lean_dec(v___x_361_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_453_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
lean_object* v___x_451_; 
if (v_isShared_449_ == 0)
{
v___x_451_ = v___x_448_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v_a_446_);
v___x_451_ = v_reuseFailAlloc_452_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
return v___x_451_;
}
}
}
}
else
{
lean_object* v_a_454_; lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_461_; 
lean_dec(v_f_338_);
lean_dec(v___x_337_);
lean_dec(v_tk_335_);
lean_dec(v_a_333_);
lean_dec(v_a_332_);
v_a_454_ = lean_ctor_get(v___x_355_, 0);
v_isSharedCheck_461_ = !lean_is_exclusive(v___x_355_);
if (v_isSharedCheck_461_ == 0)
{
v___x_456_ = v___x_355_;
v_isShared_457_ = v_isSharedCheck_461_;
goto v_resetjp_455_;
}
else
{
lean_inc(v_a_454_);
lean_dec(v___x_355_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_461_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
lean_object* v___x_459_; 
if (v_isShared_457_ == 0)
{
v___x_459_ = v___x_456_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v_a_454_);
v___x_459_ = v_reuseFailAlloc_460_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
return v___x_459_;
}
}
}
}
else
{
lean_object* v___x_462_; lean_object* v___x_464_; 
lean_dec(v_f_338_);
lean_dec(v___x_337_);
lean_dec(v_tk_335_);
lean_dec(v_a_333_);
lean_dec(v_a_332_);
v___x_462_ = lean_box(0);
if (v_isShared_352_ == 0)
{
lean_ctor_set(v___x_351_, 0, v___x_462_);
v___x_464_ = v___x_351_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v___x_462_);
v___x_464_ = v_reuseFailAlloc_465_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
return v___x_464_;
}
}
}
else
{
lean_object* v___x_466_; lean_object* v___x_468_; 
lean_dec(v_a_349_);
lean_dec(v_f_338_);
lean_dec(v___x_337_);
lean_dec(v_tk_335_);
lean_dec(v_a_333_);
lean_dec(v_a_332_);
v___x_466_ = lean_box(0);
if (v_isShared_352_ == 0)
{
lean_ctor_set(v___x_351_, 0, v___x_466_);
v___x_468_ = v___x_351_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v___x_466_);
v___x_468_ = v_reuseFailAlloc_469_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
return v___x_468_;
}
}
}
}
else
{
lean_object* v_a_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_478_; 
lean_dec(v_f_338_);
lean_dec(v___x_337_);
lean_dec(v_tk_335_);
lean_dec(v_a_333_);
lean_dec(v_a_332_);
v_a_471_ = lean_ctor_get(v___x_348_, 0);
v_isSharedCheck_478_ = !lean_is_exclusive(v___x_348_);
if (v_isSharedCheck_478_ == 0)
{
v___x_473_ = v___x_348_;
v_isShared_474_ = v_isSharedCheck_478_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_a_471_);
lean_dec(v___x_348_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_478_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v___x_476_; 
if (v_isShared_474_ == 0)
{
v___x_476_ = v___x_473_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v_a_471_);
v___x_476_ = v_reuseFailAlloc_477_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
return v___x_476_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact___lam__1___boxed(lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v___y_481_, lean_object* v_tk_482_, lean_object* v___x_483_, lean_object* v___x_484_, lean_object* v_f_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_){
_start:
{
lean_object* v_res_495_; 
v_res_495_ = l_Lean_Elab_Rewrites_evalExact___lam__1(v_a_479_, v_a_480_, v___y_481_, v_tk_482_, v___x_483_, v___x_484_, v_f_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_);
lean_dec(v___y_493_);
lean_dec_ref(v___y_492_);
lean_dec(v___y_491_);
lean_dec_ref(v___y_490_);
lean_dec(v___y_489_);
lean_dec_ref(v___y_488_);
lean_dec(v___y_487_);
lean_dec_ref(v___y_486_);
lean_dec(v___x_483_);
lean_dec(v___y_481_);
return v_res_495_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_Rewrites_evalExact_spec__3(lean_object* v_state_496_, lean_object* v_tk_497_, lean_object* v_as_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_){
_start:
{
if (lean_obj_tag(v_as_498_) == 0)
{
lean_object* v___x_508_; lean_object* v___x_509_; 
lean_dec(v_tk_497_);
lean_dec_ref(v_state_496_);
v___x_508_ = lean_box(0);
v___x_509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_509_, 0, v___x_508_);
return v___x_509_;
}
else
{
lean_object* v_head_510_; lean_object* v_tail_511_; lean_object* v___x_512_; lean_object* v___x_513_; 
v_head_510_ = lean_ctor_get(v_as_498_, 0);
lean_inc(v_head_510_);
v_tail_511_ = lean_ctor_get(v_as_498_, 1);
lean_inc(v_tail_511_);
lean_dec_ref(v_as_498_);
lean_inc_ref(v_state_496_);
v___x_512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_512_, 0, v_state_496_);
lean_inc(v_tk_497_);
v___x_513_ = l_Lean_Meta_Rewrites_RewriteResult_addSuggestion(v_tk_497_, v_head_510_, v___x_512_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_);
if (lean_obj_tag(v___x_513_) == 0)
{
lean_dec_ref(v___x_513_);
v_as_498_ = v_tail_511_;
goto _start;
}
else
{
lean_dec(v_tail_511_);
lean_dec(v_tk_497_);
lean_dec_ref(v_state_496_);
return v___x_513_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_Rewrites_evalExact_spec__3___boxed(lean_object* v_state_515_, lean_object* v_tk_516_, lean_object* v_as_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l_List_forM___at___00Lean_Elab_Rewrites_evalExact_spec__3(v_state_515_, v_tk_516_, v_as_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_);
lean_dec(v___y_525_);
lean_dec_ref(v___y_524_);
lean_dec(v___y_523_);
lean_dec_ref(v___y_522_);
lean_dec(v___y_521_);
lean_dec_ref(v___y_520_);
lean_dec(v___y_519_);
lean_dec_ref(v___y_518_);
return v_res_527_;
}
}
static lean_object* _init_l_Lean_Elab_Rewrites_evalExact___lam__2___closed__9(void){
_start:
{
lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_538_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___lam__2___closed__8));
v___x_539_ = l_Lean_stringToMessageData(v___x_538_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact___lam__2(lean_object* v_a_540_, lean_object* v_a_541_, lean_object* v___y_542_, uint8_t v___x_543_, lean_object* v_tk_544_, lean_object* v___x_545_, lean_object* v___x_546_, lean_object* v___x_547_, lean_object* v___x_548_, lean_object* v___x_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_){
_start:
{
lean_object* v___x_559_; 
lean_inc(v_a_540_);
v___x_559_ = l_Lean_MVarId_getType(v_a_540_, v___y_554_, v___y_555_, v___y_556_, v___y_557_);
if (lean_obj_tag(v___x_559_) == 0)
{
lean_object* v_a_560_; lean_object* v___x_561_; lean_object* v_a_562_; lean_object* v___x_563_; lean_object* v___x_564_; 
v_a_560_ = lean_ctor_get(v___x_559_, 0);
lean_inc(v_a_560_);
lean_dec_ref(v___x_559_);
v___x_561_ = l_Lean_instantiateMVars___at___00Lean_Elab_Rewrites_evalExact_spec__2___redArg(v_a_560_, v___y_555_);
v_a_562_ = lean_ctor_get(v___x_561_, 0);
lean_inc(v_a_562_);
lean_dec_ref(v___x_561_);
v___x_563_ = lean_box(0);
v___x_564_ = l_Lean_Meta_Rewrites_localHypotheses(v___x_563_, v___y_554_, v___y_555_, v___y_556_, v___y_557_);
if (lean_obj_tag(v___x_564_) == 0)
{
lean_object* v_a_565_; uint8_t v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; 
v_a_565_ = lean_ctor_get(v___x_564_, 0);
lean_inc(v_a_565_);
lean_dec_ref(v___x_564_);
v___x_566_ = 2;
v___x_567_ = lean_unsigned_to_nat(20u);
v___x_568_ = lean_unsigned_to_nat(10u);
lean_inc(v_a_540_);
v___x_569_ = l_Lean_Meta_Rewrites_findRewrites(v_a_565_, v_a_541_, v_a_540_, v_a_562_, v___y_542_, v___x_566_, v___x_543_, v___x_567_, v___x_568_, v___y_554_, v___y_555_, v___y_556_, v___y_557_);
if (lean_obj_tag(v___x_569_) == 0)
{
lean_object* v_a_570_; lean_object* v___y_572_; lean_object* v___y_573_; lean_object* v___y_574_; lean_object* v___y_575_; lean_object* v___y_576_; lean_object* v___y_577_; lean_object* v___y_578_; lean_object* v___y_579_; lean_object* v___x_657_; lean_object* v___x_658_; 
v_a_570_ = lean_ctor_get(v___x_569_, 0);
lean_inc(v_a_570_);
lean_dec_ref(v___x_569_);
v___x_657_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___lam__1___closed__1));
v___x_658_ = l_Lean_reportOutOfHeartbeats(v___x_657_, v_tk_544_, v___x_545_, v___y_556_, v___y_557_);
if (lean_obj_tag(v___x_658_) == 0)
{
uint8_t v___x_659_; 
lean_dec_ref(v___x_658_);
v___x_659_ = l_List_isEmpty___redArg(v_a_570_);
if (v___x_659_ == 0)
{
v___y_572_ = v___y_550_;
v___y_573_ = v___y_551_;
v___y_574_ = v___y_552_;
v___y_575_ = v___y_553_;
v___y_576_ = v___y_554_;
v___y_577_ = v___y_555_;
v___y_578_ = v___y_556_;
v___y_579_ = v___y_557_;
goto v___jp_571_;
}
else
{
lean_object* v___x_660_; lean_object* v___x_661_; 
lean_dec(v_a_570_);
lean_dec_ref(v___x_549_);
lean_dec_ref(v___x_548_);
lean_dec_ref(v___x_547_);
lean_dec(v___x_546_);
lean_dec(v_tk_544_);
lean_dec(v_a_540_);
v___x_660_ = lean_obj_once(&l_Lean_Elab_Rewrites_evalExact___lam__2___closed__9, &l_Lean_Elab_Rewrites_evalExact___lam__2___closed__9_once, _init_l_Lean_Elab_Rewrites_evalExact___lam__2___closed__9);
v___x_661_ = l_Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__1___redArg(v___x_660_, v___y_554_, v___y_555_, v___y_556_, v___y_557_);
return v___x_661_;
}
}
else
{
lean_dec(v_a_570_);
lean_dec_ref(v___x_549_);
lean_dec_ref(v___x_548_);
lean_dec_ref(v___x_547_);
lean_dec(v___x_546_);
lean_dec(v_tk_544_);
lean_dec(v_a_540_);
return v___x_658_;
}
v___jp_571_:
{
lean_object* v___x_580_; 
v___x_580_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_573_, v___y_575_, v___y_577_, v___y_579_);
if (lean_obj_tag(v___x_580_) == 0)
{
lean_object* v_a_581_; lean_object* v___x_582_; 
v_a_581_ = lean_ctor_get(v___x_580_, 0);
lean_inc(v_a_581_);
lean_dec_ref(v___x_580_);
v___x_582_ = l_List_get_x3fInternal___redArg(v_a_570_, v___x_546_);
if (lean_obj_tag(v___x_582_) == 1)
{
lean_object* v_val_583_; lean_object* v___x_584_; lean_object* v_result_585_; lean_object* v_mctx_586_; lean_object* v_cache_587_; lean_object* v_zetaDeltaFVarIds_588_; lean_object* v_postponed_589_; lean_object* v_diag_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_646_; 
lean_dec(v_a_581_);
v_val_583_ = lean_ctor_get(v___x_582_, 0);
lean_inc(v_val_583_);
lean_dec_ref(v___x_582_);
v___x_584_ = lean_st_ref_take(v___y_577_);
v_result_585_ = lean_ctor_get(v_val_583_, 2);
lean_inc_ref(v_result_585_);
v_mctx_586_ = lean_ctor_get(v_val_583_, 3);
lean_inc_ref(v_mctx_586_);
lean_dec(v_val_583_);
v_cache_587_ = lean_ctor_get(v___x_584_, 1);
v_zetaDeltaFVarIds_588_ = lean_ctor_get(v___x_584_, 2);
v_postponed_589_ = lean_ctor_get(v___x_584_, 3);
v_diag_590_ = lean_ctor_get(v___x_584_, 4);
v_isSharedCheck_646_ = !lean_is_exclusive(v___x_584_);
if (v_isSharedCheck_646_ == 0)
{
lean_object* v_unused_647_; 
v_unused_647_ = lean_ctor_get(v___x_584_, 0);
lean_dec(v_unused_647_);
v___x_592_ = v___x_584_;
v_isShared_593_ = v_isSharedCheck_646_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_diag_590_);
lean_inc(v_postponed_589_);
lean_inc(v_zetaDeltaFVarIds_588_);
lean_inc(v_cache_587_);
lean_dec(v___x_584_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_646_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v___x_595_; 
if (v_isShared_593_ == 0)
{
lean_ctor_set(v___x_592_, 0, v_mctx_586_);
v___x_595_ = v___x_592_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v_mctx_586_);
lean_ctor_set(v_reuseFailAlloc_645_, 1, v_cache_587_);
lean_ctor_set(v_reuseFailAlloc_645_, 2, v_zetaDeltaFVarIds_588_);
lean_ctor_set(v_reuseFailAlloc_645_, 3, v_postponed_589_);
lean_ctor_set(v_reuseFailAlloc_645_, 4, v_diag_590_);
v___x_595_ = v_reuseFailAlloc_645_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
lean_object* v___x_596_; lean_object* v___x_597_; 
v___x_596_ = lean_st_ref_set(v___y_577_, v___x_595_);
v___x_597_ = l_Lean_Elab_Tactic_saveState___redArg(v___y_573_, v___y_575_, v___y_577_, v___y_579_);
if (lean_obj_tag(v___x_597_) == 0)
{
lean_object* v_a_598_; lean_object* v_eNew_599_; lean_object* v_eqProof_600_; lean_object* v_mvarIds_601_; lean_object* v___x_602_; 
v_a_598_ = lean_ctor_get(v___x_597_, 0);
lean_inc(v_a_598_);
lean_dec_ref(v___x_597_);
v_eNew_599_ = lean_ctor_get(v_result_585_, 0);
lean_inc_ref(v_eNew_599_);
v_eqProof_600_ = lean_ctor_get(v_result_585_, 1);
lean_inc_ref(v_eqProof_600_);
v_mvarIds_601_ = lean_ctor_get(v_result_585_, 2);
lean_inc(v_mvarIds_601_);
lean_dec_ref(v_result_585_);
v___x_602_ = l_Lean_MVarId_replaceTargetEq(v_a_540_, v_eNew_599_, v_eqProof_600_, v___y_576_, v___y_577_, v___y_578_, v___y_579_);
if (lean_obj_tag(v___x_602_) == 0)
{
lean_object* v_a_603_; lean_object* v___x_604_; lean_object* v___x_605_; 
v_a_603_ = lean_ctor_get(v___x_602_, 0);
lean_inc(v_a_603_);
lean_dec_ref(v___x_602_);
v___x_604_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_604_, 0, v_a_603_);
lean_ctor_set(v___x_604_, 1, v_mvarIds_601_);
v___x_605_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_604_, v___y_573_, v___y_576_, v___y_577_, v___y_578_, v___y_579_);
if (lean_obj_tag(v___x_605_) == 0)
{
lean_object* v_ref_606_; uint8_t v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
lean_dec_ref(v___x_605_);
v_ref_606_ = lean_ctor_get(v___y_578_, 5);
v___x_607_ = 0;
v___x_608_ = l_Lean_SourceInfo_fromRef(v_ref_606_, v___x_607_);
v___x_609_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___lam__2___closed__0));
lean_inc_ref_n(v___x_549_, 3);
lean_inc_ref_n(v___x_548_, 3);
lean_inc_ref_n(v___x_547_, 3);
v___x_610_ = l_Lean_Name_mkStr4(v___x_547_, v___x_548_, v___x_549_, v___x_609_);
v___x_611_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___lam__2___closed__1));
lean_inc_n(v___x_608_, 6);
v___x_612_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_612_, 0, v___x_608_);
lean_ctor_set(v___x_612_, 1, v___x_611_);
v___x_613_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___lam__2___closed__2));
v___x_614_ = l_Lean_Name_mkStr4(v___x_547_, v___x_548_, v___x_549_, v___x_613_);
v___x_615_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___lam__2___closed__3));
v___x_616_ = l_Lean_Name_mkStr4(v___x_547_, v___x_548_, v___x_549_, v___x_615_);
v___x_617_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___lam__2___closed__5));
v___x_618_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___lam__2___closed__6));
v___x_619_ = l_Lean_Name_mkStr4(v___x_547_, v___x_548_, v___x_549_, v___x_618_);
v___x_620_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___lam__2___closed__7));
v___x_621_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_621_, 0, v___x_608_);
lean_ctor_set(v___x_621_, 1, v___x_620_);
v___x_622_ = l_Lean_Syntax_node1(v___x_608_, v___x_619_, v___x_621_);
v___x_623_ = l_Lean_Syntax_node1(v___x_608_, v___x_617_, v___x_622_);
v___x_624_ = l_Lean_Syntax_node1(v___x_608_, v___x_616_, v___x_623_);
v___x_625_ = l_Lean_Syntax_node1(v___x_608_, v___x_614_, v___x_624_);
v___x_626_ = l_Lean_Syntax_node2(v___x_608_, v___x_610_, v___x_612_, v___x_625_);
v___x_627_ = l_Lean_Elab_Tactic_evalTactic(v___x_626_, v___y_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_);
if (lean_obj_tag(v___x_627_) == 0)
{
lean_object* v___x_628_; 
lean_dec_ref(v___x_627_);
v___x_628_ = l_List_forM___at___00Lean_Elab_Rewrites_evalExact_spec__3(v_a_598_, v_tk_544_, v_a_570_, v___y_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_);
return v___x_628_;
}
else
{
lean_dec(v_a_598_);
lean_dec(v_a_570_);
lean_dec(v_tk_544_);
return v___x_627_;
}
}
else
{
lean_dec(v_a_598_);
lean_dec(v_a_570_);
lean_dec_ref(v___x_549_);
lean_dec_ref(v___x_548_);
lean_dec_ref(v___x_547_);
lean_dec(v_tk_544_);
return v___x_605_;
}
}
else
{
lean_object* v_a_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_636_; 
lean_dec(v_mvarIds_601_);
lean_dec(v_a_598_);
lean_dec(v_a_570_);
lean_dec_ref(v___x_549_);
lean_dec_ref(v___x_548_);
lean_dec_ref(v___x_547_);
lean_dec(v_tk_544_);
v_a_629_ = lean_ctor_get(v___x_602_, 0);
v_isSharedCheck_636_ = !lean_is_exclusive(v___x_602_);
if (v_isSharedCheck_636_ == 0)
{
v___x_631_ = v___x_602_;
v_isShared_632_ = v_isSharedCheck_636_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_a_629_);
lean_dec(v___x_602_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_636_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
lean_object* v___x_634_; 
if (v_isShared_632_ == 0)
{
v___x_634_ = v___x_631_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v_a_629_);
v___x_634_ = v_reuseFailAlloc_635_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
return v___x_634_;
}
}
}
}
else
{
lean_object* v_a_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_644_; 
lean_dec_ref(v_result_585_);
lean_dec(v_a_570_);
lean_dec_ref(v___x_549_);
lean_dec_ref(v___x_548_);
lean_dec_ref(v___x_547_);
lean_dec(v_tk_544_);
lean_dec(v_a_540_);
v_a_637_ = lean_ctor_get(v___x_597_, 0);
v_isSharedCheck_644_ = !lean_is_exclusive(v___x_597_);
if (v_isSharedCheck_644_ == 0)
{
v___x_639_ = v___x_597_;
v_isShared_640_ = v_isSharedCheck_644_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_a_637_);
lean_dec(v___x_597_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_644_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v___x_642_; 
if (v_isShared_640_ == 0)
{
v___x_642_ = v___x_639_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v_a_637_);
v___x_642_ = v_reuseFailAlloc_643_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
return v___x_642_;
}
}
}
}
}
}
else
{
lean_object* v___x_648_; 
lean_dec(v___x_582_);
lean_dec_ref(v___x_549_);
lean_dec_ref(v___x_548_);
lean_dec_ref(v___x_547_);
lean_dec(v_a_540_);
v___x_648_ = l_List_forM___at___00Lean_Elab_Rewrites_evalExact_spec__3(v_a_581_, v_tk_544_, v_a_570_, v___y_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_);
return v___x_648_;
}
}
else
{
lean_object* v_a_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_656_; 
lean_dec(v_a_570_);
lean_dec_ref(v___x_549_);
lean_dec_ref(v___x_548_);
lean_dec_ref(v___x_547_);
lean_dec(v___x_546_);
lean_dec(v_tk_544_);
lean_dec(v_a_540_);
v_a_649_ = lean_ctor_get(v___x_580_, 0);
v_isSharedCheck_656_ = !lean_is_exclusive(v___x_580_);
if (v_isSharedCheck_656_ == 0)
{
v___x_651_ = v___x_580_;
v_isShared_652_ = v_isSharedCheck_656_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_a_649_);
lean_dec(v___x_580_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_656_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v___x_654_; 
if (v_isShared_652_ == 0)
{
v___x_654_ = v___x_651_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v_a_649_);
v___x_654_ = v_reuseFailAlloc_655_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
return v___x_654_;
}
}
}
}
}
else
{
lean_object* v_a_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_669_; 
lean_dec_ref(v___x_549_);
lean_dec_ref(v___x_548_);
lean_dec_ref(v___x_547_);
lean_dec(v___x_546_);
lean_dec(v_tk_544_);
lean_dec(v_a_540_);
v_a_662_ = lean_ctor_get(v___x_569_, 0);
v_isSharedCheck_669_ = !lean_is_exclusive(v___x_569_);
if (v_isSharedCheck_669_ == 0)
{
v___x_664_ = v___x_569_;
v_isShared_665_ = v_isSharedCheck_669_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_a_662_);
lean_dec(v___x_569_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_669_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v___x_667_; 
if (v_isShared_665_ == 0)
{
v___x_667_ = v___x_664_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v_a_662_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
return v___x_667_;
}
}
}
}
else
{
lean_object* v_a_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_677_; 
lean_dec(v_a_562_);
lean_dec_ref(v___x_549_);
lean_dec_ref(v___x_548_);
lean_dec_ref(v___x_547_);
lean_dec(v___x_546_);
lean_dec(v_tk_544_);
lean_dec(v_a_541_);
lean_dec(v_a_540_);
v_a_670_ = lean_ctor_get(v___x_564_, 0);
v_isSharedCheck_677_ = !lean_is_exclusive(v___x_564_);
if (v_isSharedCheck_677_ == 0)
{
v___x_672_ = v___x_564_;
v_isShared_673_ = v_isSharedCheck_677_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_a_670_);
lean_dec(v___x_564_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_677_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v___x_675_; 
if (v_isShared_673_ == 0)
{
v___x_675_ = v___x_672_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v_a_670_);
v___x_675_ = v_reuseFailAlloc_676_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
return v___x_675_;
}
}
}
}
else
{
lean_object* v_a_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_685_; 
lean_dec_ref(v___x_549_);
lean_dec_ref(v___x_548_);
lean_dec_ref(v___x_547_);
lean_dec(v___x_546_);
lean_dec(v_tk_544_);
lean_dec(v_a_541_);
lean_dec(v_a_540_);
v_a_678_ = lean_ctor_get(v___x_559_, 0);
v_isSharedCheck_685_ = !lean_is_exclusive(v___x_559_);
if (v_isSharedCheck_685_ == 0)
{
v___x_680_ = v___x_559_;
v_isShared_681_ = v_isSharedCheck_685_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_a_678_);
lean_dec(v___x_559_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_685_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
lean_object* v___x_683_; 
if (v_isShared_681_ == 0)
{
v___x_683_ = v___x_680_;
goto v_reusejp_682_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v_a_678_);
v___x_683_ = v_reuseFailAlloc_684_;
goto v_reusejp_682_;
}
v_reusejp_682_:
{
return v___x_683_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact___lam__2___boxed(lean_object** _args){
lean_object* v_a_686_ = _args[0];
lean_object* v_a_687_ = _args[1];
lean_object* v___y_688_ = _args[2];
lean_object* v___x_689_ = _args[3];
lean_object* v_tk_690_ = _args[4];
lean_object* v___x_691_ = _args[5];
lean_object* v___x_692_ = _args[6];
lean_object* v___x_693_ = _args[7];
lean_object* v___x_694_ = _args[8];
lean_object* v___x_695_ = _args[9];
lean_object* v___y_696_ = _args[10];
lean_object* v___y_697_ = _args[11];
lean_object* v___y_698_ = _args[12];
lean_object* v___y_699_ = _args[13];
lean_object* v___y_700_ = _args[14];
lean_object* v___y_701_ = _args[15];
lean_object* v___y_702_ = _args[16];
lean_object* v___y_703_ = _args[17];
lean_object* v___y_704_ = _args[18];
_start:
{
uint8_t v___x_25501__boxed_705_; lean_object* v_res_706_; 
v___x_25501__boxed_705_ = lean_unbox(v___x_689_);
v_res_706_ = l_Lean_Elab_Rewrites_evalExact___lam__2(v_a_686_, v_a_687_, v___y_688_, v___x_25501__boxed_705_, v_tk_690_, v___x_691_, v___x_692_, v___x_693_, v___x_694_, v___x_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_);
lean_dec(v___y_703_);
lean_dec_ref(v___y_702_);
lean_dec(v___y_701_);
lean_dec_ref(v___y_700_);
lean_dec(v___y_699_);
lean_dec_ref(v___y_698_);
lean_dec(v___y_697_);
lean_dec_ref(v___y_696_);
lean_dec(v___x_691_);
lean_dec(v___y_688_);
return v_res_706_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Rewrites_evalExact_spec__9(uint8_t v___x_707_, uint8_t v___x_708_, lean_object* v_as_709_, size_t v_i_710_, size_t v_stop_711_, lean_object* v_b_712_){
_start:
{
lean_object* v___y_714_; uint8_t v___x_718_; 
v___x_718_ = lean_usize_dec_eq(v_i_710_, v_stop_711_);
if (v___x_718_ == 0)
{
lean_object* v_fst_719_; uint8_t v___x_720_; 
v_fst_719_ = lean_ctor_get(v_b_712_, 0);
v___x_720_ = lean_unbox(v_fst_719_);
if (v___x_720_ == 0)
{
lean_object* v_snd_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_729_; 
v_snd_721_ = lean_ctor_get(v_b_712_, 1);
v_isSharedCheck_729_ = !lean_is_exclusive(v_b_712_);
if (v_isSharedCheck_729_ == 0)
{
lean_object* v_unused_730_; 
v_unused_730_ = lean_ctor_get(v_b_712_, 0);
lean_dec(v_unused_730_);
v___x_723_ = v_b_712_;
v_isShared_724_ = v_isSharedCheck_729_;
goto v_resetjp_722_;
}
else
{
lean_inc(v_snd_721_);
lean_dec(v_b_712_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_729_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
lean_object* v___x_725_; lean_object* v___x_727_; 
v___x_725_ = lean_box(v___x_707_);
if (v_isShared_724_ == 0)
{
lean_ctor_set(v___x_723_, 0, v___x_725_);
v___x_727_ = v___x_723_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v___x_725_);
lean_ctor_set(v_reuseFailAlloc_728_, 1, v_snd_721_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
v___y_714_ = v___x_727_;
goto v___jp_713_;
}
}
}
else
{
lean_object* v_snd_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_741_; 
v_snd_731_ = lean_ctor_get(v_b_712_, 1);
v_isSharedCheck_741_ = !lean_is_exclusive(v_b_712_);
if (v_isSharedCheck_741_ == 0)
{
lean_object* v_unused_742_; 
v_unused_742_ = lean_ctor_get(v_b_712_, 0);
lean_dec(v_unused_742_);
v___x_733_ = v_b_712_;
v_isShared_734_ = v_isSharedCheck_741_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_snd_731_);
lean_dec(v_b_712_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_741_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_739_; 
v___x_735_ = lean_array_uget_borrowed(v_as_709_, v_i_710_);
lean_inc(v___x_735_);
v___x_736_ = lean_array_push(v_snd_731_, v___x_735_);
v___x_737_ = lean_box(v___x_708_);
if (v_isShared_734_ == 0)
{
lean_ctor_set(v___x_733_, 1, v___x_736_);
lean_ctor_set(v___x_733_, 0, v___x_737_);
v___x_739_ = v___x_733_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v___x_737_);
lean_ctor_set(v_reuseFailAlloc_740_, 1, v___x_736_);
v___x_739_ = v_reuseFailAlloc_740_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
v___y_714_ = v___x_739_;
goto v___jp_713_;
}
}
}
}
else
{
return v_b_712_;
}
v___jp_713_:
{
size_t v___x_715_; size_t v___x_716_; 
v___x_715_ = ((size_t)1ULL);
v___x_716_ = lean_usize_add(v_i_710_, v___x_715_);
v_i_710_ = v___x_716_;
v_b_712_ = v___y_714_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Rewrites_evalExact_spec__9___boxed(lean_object* v___x_743_, lean_object* v___x_744_, lean_object* v_as_745_, lean_object* v_i_746_, lean_object* v_stop_747_, lean_object* v_b_748_){
_start:
{
uint8_t v___x_25806__boxed_749_; uint8_t v___x_25807__boxed_750_; size_t v_i_boxed_751_; size_t v_stop_boxed_752_; lean_object* v_res_753_; 
v___x_25806__boxed_749_ = lean_unbox(v___x_743_);
v___x_25807__boxed_750_ = lean_unbox(v___x_744_);
v_i_boxed_751_ = lean_unbox_usize(v_i_746_);
lean_dec(v_i_746_);
v_stop_boxed_752_ = lean_unbox_usize(v_stop_747_);
lean_dec(v_stop_747_);
v_res_753_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Rewrites_evalExact_spec__9(v___x_25806__boxed_749_, v___x_25807__boxed_750_, v_as_745_, v_i_boxed_751_, v_stop_boxed_752_, v_b_748_);
lean_dec_ref(v_as_745_);
return v_res_753_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__8(size_t v_sz_757_, size_t v_i_758_, lean_object* v_bs_759_){
_start:
{
uint8_t v___x_760_; 
v___x_760_ = lean_usize_dec_lt(v_i_758_, v_sz_757_);
if (v___x_760_ == 0)
{
lean_object* v___x_761_; 
v___x_761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_761_, 0, v_bs_759_);
return v___x_761_;
}
else
{
lean_object* v_v_762_; lean_object* v___x_763_; uint8_t v___x_764_; 
v_v_762_ = lean_array_uget(v_bs_759_, v_i_758_);
v___x_763_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__8___closed__1));
lean_inc(v_v_762_);
v___x_764_ = l_Lean_Syntax_isOfKind(v_v_762_, v___x_763_);
if (v___x_764_ == 0)
{
lean_object* v___x_765_; 
lean_dec(v_v_762_);
lean_dec_ref(v_bs_759_);
v___x_765_ = lean_box(0);
return v___x_765_;
}
else
{
lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v_bs_x27_768_; lean_object* v_forbidden_769_; size_t v___x_770_; size_t v___x_771_; lean_object* v___x_772_; 
v___x_766_ = lean_unsigned_to_nat(1u);
v___x_767_ = lean_unsigned_to_nat(0u);
v_bs_x27_768_ = lean_array_uset(v_bs_759_, v_i_758_, v___x_767_);
v_forbidden_769_ = l_Lean_Syntax_getArg(v_v_762_, v___x_766_);
lean_dec(v_v_762_);
v___x_770_ = ((size_t)1ULL);
v___x_771_ = lean_usize_add(v_i_758_, v___x_770_);
v___x_772_ = lean_array_uset(v_bs_x27_768_, v_i_758_, v_forbidden_769_);
v_i_758_ = v___x_771_;
v_bs_759_ = v___x_772_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__8___boxed(lean_object* v_sz_774_, lean_object* v_i_775_, lean_object* v_bs_776_){
_start:
{
size_t v_sz_boxed_777_; size_t v_i_boxed_778_; lean_object* v_res_779_; 
v_sz_boxed_777_ = lean_unbox_usize(v_sz_774_);
lean_dec(v_sz_774_);
v_i_boxed_778_ = lean_unbox_usize(v_i_775_);
lean_dec(v_i_775_);
v_res_779_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__8(v_sz_boxed_777_, v_i_boxed_778_, v_bs_776_);
return v_res_779_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Rewrites_evalExact_spec__7(lean_object* v_as_780_, size_t v_i_781_, size_t v_stop_782_, lean_object* v_b_783_){
_start:
{
uint8_t v___x_784_; 
v___x_784_ = lean_usize_dec_eq(v_i_781_, v_stop_782_);
if (v___x_784_ == 0)
{
lean_object* v___x_785_; lean_object* v___x_786_; size_t v___x_787_; size_t v___x_788_; 
v___x_785_ = lean_array_uget_borrowed(v_as_780_, v_i_781_);
lean_inc(v___x_785_);
v___x_786_ = l_Lean_NameSet_insert(v_b_783_, v___x_785_);
v___x_787_ = ((size_t)1ULL);
v___x_788_ = lean_usize_add(v_i_781_, v___x_787_);
v_i_781_ = v___x_788_;
v_b_783_ = v___x_786_;
goto _start;
}
else
{
return v_b_783_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Rewrites_evalExact_spec__7___boxed(lean_object* v_as_790_, lean_object* v_i_791_, lean_object* v_stop_792_, lean_object* v_b_793_){
_start:
{
size_t v_i_boxed_794_; size_t v_stop_boxed_795_; lean_object* v_res_796_; 
v_i_boxed_794_ = lean_unbox_usize(v_i_791_);
lean_dec(v_i_791_);
v_stop_boxed_795_ = lean_unbox_usize(v_stop_792_);
lean_dec(v_stop_792_);
v_res_796_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Rewrites_evalExact_spec__7(v_as_790_, v_i_boxed_794_, v_stop_boxed_795_, v_b_793_);
lean_dec_ref(v_as_790_);
return v_res_796_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__6(size_t v_sz_797_, size_t v_i_798_, lean_object* v_bs_799_){
_start:
{
uint8_t v___x_800_; 
v___x_800_ = lean_usize_dec_lt(v_i_798_, v_sz_797_);
if (v___x_800_ == 0)
{
return v_bs_799_;
}
else
{
lean_object* v_v_801_; lean_object* v___x_802_; lean_object* v_bs_x27_803_; lean_object* v___x_804_; size_t v___x_805_; size_t v___x_806_; lean_object* v___x_807_; 
v_v_801_ = lean_array_uget(v_bs_799_, v_i_798_);
v___x_802_ = lean_unsigned_to_nat(0u);
v_bs_x27_803_ = lean_array_uset(v_bs_799_, v_i_798_, v___x_802_);
v___x_804_ = l_Lean_Syntax_getId(v_v_801_);
lean_dec(v_v_801_);
v___x_805_ = ((size_t)1ULL);
v___x_806_ = lean_usize_add(v_i_798_, v___x_805_);
v___x_807_ = lean_array_uset(v_bs_x27_803_, v_i_798_, v___x_804_);
v_i_798_ = v___x_806_;
v_bs_799_ = v___x_807_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__6___boxed(lean_object* v_sz_809_, lean_object* v_i_810_, lean_object* v_bs_811_){
_start:
{
size_t v_sz_boxed_812_; size_t v_i_boxed_813_; lean_object* v_res_814_; 
v_sz_boxed_812_ = lean_unbox_usize(v_sz_809_);
lean_dec(v_sz_809_);
v_i_boxed_813_ = lean_unbox_usize(v_i_810_);
lean_dec(v_i_810_);
v_res_814_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__6(v_sz_boxed_812_, v_i_boxed_813_, v_bs_811_);
return v_res_814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact(lean_object* v_stx_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_){
_start:
{
lean_object* v___y_849_; lean_object* v___y_850_; lean_object* v___y_851_; lean_object* v___y_852_; lean_object* v___y_853_; lean_object* v___y_854_; lean_object* v___y_855_; lean_object* v___y_856_; lean_object* v___y_857_; lean_object* v___y_858_; lean_object* v___y_859_; lean_object* v___y_860_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; uint8_t v___x_868_; 
v___x_864_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___closed__0));
v___x_865_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___closed__1));
v___x_866_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___closed__2));
v___x_867_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___closed__4));
lean_inc(v_stx_838_);
v___x_868_ = l_Lean_Syntax_isOfKind(v_stx_838_, v___x_867_);
if (v___x_868_ == 0)
{
lean_object* v___x_869_; 
lean_dec(v_stx_838_);
v___x_869_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__0___redArg();
return v___x_869_;
}
else
{
lean_object* v___f_870_; lean_object* v___x_871_; lean_object* v_tk_872_; lean_object* v___y_874_; lean_object* v___y_875_; lean_object* v___y_876_; lean_object* v___y_877_; lean_object* v___y_878_; lean_object* v___y_879_; lean_object* v___y_880_; lean_object* v___y_881_; lean_object* v___y_882_; lean_object* v___y_883_; lean_object* v___y_884_; lean_object* v___y_885_; lean_object* v___y_912_; lean_object* v___y_913_; lean_object* v___y_914_; lean_object* v___y_915_; lean_object* v___y_916_; lean_object* v___y_917_; lean_object* v___y_918_; lean_object* v___y_919_; lean_object* v___y_920_; lean_object* v___y_921_; lean_object* v___y_922_; lean_object* v___y_923_; lean_object* v___y_924_; lean_object* v___y_936_; lean_object* v_forbidden_937_; lean_object* v___y_938_; lean_object* v___y_939_; lean_object* v___y_940_; lean_object* v___y_941_; lean_object* v___y_942_; lean_object* v___y_943_; lean_object* v___y_944_; lean_object* v___y_945_; lean_object* v___y_960_; lean_object* v___y_961_; lean_object* v___y_962_; lean_object* v___y_963_; lean_object* v___y_964_; lean_object* v___y_965_; lean_object* v___y_966_; lean_object* v___y_967_; lean_object* v___y_968_; lean_object* v___y_969_; lean_object* v___x_974_; lean_object* v_loc_976_; lean_object* v___y_977_; lean_object* v___y_978_; lean_object* v___y_979_; lean_object* v___y_980_; lean_object* v___y_981_; lean_object* v___y_982_; lean_object* v___y_983_; lean_object* v___y_984_; lean_object* v___x_1011_; uint8_t v___x_1012_; 
v___f_870_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___closed__5));
v___x_871_ = lean_unsigned_to_nat(0u);
v_tk_872_ = l_Lean_Syntax_getArg(v_stx_838_, v___x_871_);
v___x_974_ = lean_unsigned_to_nat(1u);
v___x_1011_ = l_Lean_Syntax_getArg(v_stx_838_, v___x_974_);
v___x_1012_ = l_Lean_Syntax_isNone(v___x_1011_);
if (v___x_1012_ == 0)
{
uint8_t v___x_1013_; 
lean_inc(v___x_1011_);
v___x_1013_ = l_Lean_Syntax_matchesNull(v___x_1011_, v___x_974_);
if (v___x_1013_ == 0)
{
lean_object* v___x_1014_; 
lean_dec(v___x_1011_);
lean_dec(v_tk_872_);
lean_dec(v_stx_838_);
v___x_1014_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__0___redArg();
return v___x_1014_;
}
else
{
lean_object* v_loc_1015_; lean_object* v___x_1016_; 
v_loc_1015_ = l_Lean_Syntax_getArg(v___x_1011_, v___x_871_);
lean_dec(v___x_1011_);
v___x_1016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1016_, 0, v_loc_1015_);
v_loc_976_ = v___x_1016_;
v___y_977_ = v_a_839_;
v___y_978_ = v_a_840_;
v___y_979_ = v_a_841_;
v___y_980_ = v_a_842_;
v___y_981_ = v_a_843_;
v___y_982_ = v_a_844_;
v___y_983_ = v_a_845_;
v___y_984_ = v_a_846_;
goto v___jp_975_;
}
}
else
{
lean_object* v___x_1017_; 
lean_dec(v___x_1011_);
v___x_1017_ = lean_box(0);
v_loc_976_ = v___x_1017_;
v___y_977_ = v_a_839_;
v___y_978_ = v_a_840_;
v___y_979_ = v_a_841_;
v___y_980_ = v_a_842_;
v___y_981_ = v_a_843_;
v___y_982_ = v_a_844_;
v___y_983_ = v_a_845_;
v___y_984_ = v_a_846_;
goto v___jp_975_;
}
v___jp_873_:
{
lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; 
v___x_886_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___closed__7));
v___x_887_ = lean_unsigned_to_nat(90u);
v___x_888_ = l_Lean_reportOutOfHeartbeats(v___x_886_, v_tk_872_, v___x_887_, v___y_883_, v___y_882_);
if (lean_obj_tag(v___x_888_) == 0)
{
lean_object* v___x_889_; 
lean_dec_ref(v___x_888_);
v___x_889_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_880_, v___y_877_, v___y_881_, v___y_883_, v___y_882_);
if (lean_obj_tag(v___x_889_) == 0)
{
lean_object* v_a_890_; lean_object* v___f_891_; lean_object* v___x_892_; lean_object* v___f_893_; 
v_a_890_ = lean_ctor_get(v___x_889_, 0);
lean_inc_n(v_a_890_, 2);
lean_dec_ref(v___x_889_);
lean_inc(v_tk_872_);
lean_inc(v___y_885_);
lean_inc(v___y_874_);
v___f_891_ = lean_alloc_closure((void*)(l_Lean_Elab_Rewrites_evalExact___lam__1___boxed), 16, 6);
lean_closure_set(v___f_891_, 0, v___y_874_);
lean_closure_set(v___f_891_, 1, v_a_890_);
lean_closure_set(v___f_891_, 2, v___y_885_);
lean_closure_set(v___f_891_, 3, v_tk_872_);
lean_closure_set(v___f_891_, 4, v___x_887_);
lean_closure_set(v___f_891_, 5, v___x_871_);
v___x_892_ = lean_box(v___x_868_);
v___f_893_ = lean_alloc_closure((void*)(l_Lean_Elab_Rewrites_evalExact___lam__2___boxed), 19, 10);
lean_closure_set(v___f_893_, 0, v_a_890_);
lean_closure_set(v___f_893_, 1, v___y_874_);
lean_closure_set(v___f_893_, 2, v___y_885_);
lean_closure_set(v___f_893_, 3, v___x_892_);
lean_closure_set(v___f_893_, 4, v_tk_872_);
lean_closure_set(v___f_893_, 5, v___x_887_);
lean_closure_set(v___f_893_, 6, v___x_871_);
lean_closure_set(v___f_893_, 7, v___x_864_);
lean_closure_set(v___f_893_, 8, v___x_865_);
lean_closure_set(v___f_893_, 9, v___x_866_);
if (lean_obj_tag(v___y_876_) == 0)
{
lean_object* v___x_894_; 
v___x_894_ = lean_box(0);
v___y_849_ = v___y_875_;
v___y_850_ = v___y_877_;
v___y_851_ = v___f_891_;
v___y_852_ = v___y_878_;
v___y_853_ = v___y_879_;
v___y_854_ = v___y_880_;
v___y_855_ = v___y_881_;
v___y_856_ = v___y_882_;
v___y_857_ = v___y_883_;
v___y_858_ = v___y_884_;
v___y_859_ = v___f_893_;
v___y_860_ = v___x_894_;
goto v___jp_848_;
}
else
{
lean_object* v_val_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_902_; 
v_val_895_ = lean_ctor_get(v___y_876_, 0);
v_isSharedCheck_902_ = !lean_is_exclusive(v___y_876_);
if (v_isSharedCheck_902_ == 0)
{
v___x_897_ = v___y_876_;
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_val_895_);
lean_dec(v___y_876_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v___x_900_; 
if (v_isShared_898_ == 0)
{
v___x_900_ = v___x_897_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v_val_895_);
v___x_900_ = v_reuseFailAlloc_901_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
v___y_849_ = v___y_875_;
v___y_850_ = v___y_877_;
v___y_851_ = v___f_891_;
v___y_852_ = v___y_878_;
v___y_853_ = v___y_879_;
v___y_854_ = v___y_880_;
v___y_855_ = v___y_881_;
v___y_856_ = v___y_882_;
v___y_857_ = v___y_883_;
v___y_858_ = v___y_884_;
v___y_859_ = v___f_893_;
v___y_860_ = v___x_900_;
goto v___jp_848_;
}
}
}
}
else
{
lean_object* v_a_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_910_; 
lean_dec(v___y_885_);
lean_dec(v___y_876_);
lean_dec(v___y_874_);
lean_dec(v_tk_872_);
v_a_903_ = lean_ctor_get(v___x_889_, 0);
v_isSharedCheck_910_ = !lean_is_exclusive(v___x_889_);
if (v_isSharedCheck_910_ == 0)
{
v___x_905_ = v___x_889_;
v_isShared_906_ = v_isSharedCheck_910_;
goto v_resetjp_904_;
}
else
{
lean_inc(v_a_903_);
lean_dec(v___x_889_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_910_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
lean_object* v___x_908_; 
if (v_isShared_906_ == 0)
{
v___x_908_ = v___x_905_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v_a_903_);
v___x_908_ = v_reuseFailAlloc_909_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
return v___x_908_;
}
}
}
}
else
{
lean_dec(v___y_885_);
lean_dec(v___y_876_);
lean_dec(v___y_874_);
lean_dec(v_tk_872_);
return v___x_888_;
}
}
v___jp_911_:
{
size_t v_sz_925_; size_t v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; uint8_t v___x_929_; 
v_sz_925_ = lean_array_size(v___y_924_);
v___x_926_ = ((size_t)0ULL);
v___x_927_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__6(v_sz_925_, v___x_926_, v___y_924_);
v___x_928_ = lean_array_get_size(v___x_927_);
v___x_929_ = lean_nat_dec_lt(v___x_871_, v___x_928_);
if (v___x_929_ == 0)
{
lean_dec_ref(v___x_927_);
lean_inc(v___y_917_);
v___y_874_ = v___y_912_;
v___y_875_ = v___y_913_;
v___y_876_ = v___y_915_;
v___y_877_ = v___y_914_;
v___y_878_ = v___y_916_;
v___y_879_ = v___y_919_;
v___y_880_ = v___y_918_;
v___y_881_ = v___y_920_;
v___y_882_ = v___y_921_;
v___y_883_ = v___y_922_;
v___y_884_ = v___y_923_;
v___y_885_ = v___y_917_;
goto v___jp_873_;
}
else
{
uint8_t v___x_930_; 
v___x_930_ = lean_nat_dec_le(v___x_928_, v___x_928_);
if (v___x_930_ == 0)
{
if (v___x_929_ == 0)
{
lean_dec_ref(v___x_927_);
lean_inc(v___y_917_);
v___y_874_ = v___y_912_;
v___y_875_ = v___y_913_;
v___y_876_ = v___y_915_;
v___y_877_ = v___y_914_;
v___y_878_ = v___y_916_;
v___y_879_ = v___y_919_;
v___y_880_ = v___y_918_;
v___y_881_ = v___y_920_;
v___y_882_ = v___y_921_;
v___y_883_ = v___y_922_;
v___y_884_ = v___y_923_;
v___y_885_ = v___y_917_;
goto v___jp_873_;
}
else
{
size_t v___x_931_; lean_object* v___x_932_; 
v___x_931_ = lean_usize_of_nat(v___x_928_);
lean_inc(v___y_917_);
v___x_932_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Rewrites_evalExact_spec__7(v___x_927_, v___x_926_, v___x_931_, v___y_917_);
lean_dec_ref(v___x_927_);
v___y_874_ = v___y_912_;
v___y_875_ = v___y_913_;
v___y_876_ = v___y_915_;
v___y_877_ = v___y_914_;
v___y_878_ = v___y_916_;
v___y_879_ = v___y_919_;
v___y_880_ = v___y_918_;
v___y_881_ = v___y_920_;
v___y_882_ = v___y_921_;
v___y_883_ = v___y_922_;
v___y_884_ = v___y_923_;
v___y_885_ = v___x_932_;
goto v___jp_873_;
}
}
else
{
size_t v___x_933_; lean_object* v___x_934_; 
v___x_933_ = lean_usize_of_nat(v___x_928_);
lean_inc(v___y_917_);
v___x_934_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Rewrites_evalExact_spec__7(v___x_927_, v___x_926_, v___x_933_, v___y_917_);
lean_dec_ref(v___x_927_);
v___y_874_ = v___y_912_;
v___y_875_ = v___y_913_;
v___y_876_ = v___y_915_;
v___y_877_ = v___y_914_;
v___y_878_ = v___y_916_;
v___y_879_ = v___y_919_;
v___y_880_ = v___y_918_;
v___y_881_ = v___y_920_;
v___y_882_ = v___y_921_;
v___y_883_ = v___y_922_;
v___y_884_ = v___y_923_;
v___y_885_ = v___x_934_;
goto v___jp_873_;
}
}
}
v___jp_935_:
{
lean_object* v___x_946_; 
v___x_946_ = l_Lean_Meta_Rewrites_createModuleTreeRef(v___y_942_, v___y_943_, v___y_944_, v___y_945_);
if (lean_obj_tag(v___x_946_) == 0)
{
lean_object* v_a_947_; lean_object* v___x_948_; 
v_a_947_ = lean_ctor_get(v___x_946_, 0);
lean_inc(v_a_947_);
lean_dec_ref(v___x_946_);
v___x_948_ = l_Lean_NameSet_empty;
if (lean_obj_tag(v_forbidden_937_) == 0)
{
lean_object* v___x_949_; 
v___x_949_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___closed__8));
v___y_912_ = v_a_947_;
v___y_913_ = v___f_870_;
v___y_914_ = v___y_942_;
v___y_915_ = v___y_936_;
v___y_916_ = v___y_938_;
v___y_917_ = v___x_948_;
v___y_918_ = v___y_939_;
v___y_919_ = v___y_941_;
v___y_920_ = v___y_943_;
v___y_921_ = v___y_945_;
v___y_922_ = v___y_944_;
v___y_923_ = v___y_940_;
v___y_924_ = v___x_949_;
goto v___jp_911_;
}
else
{
lean_object* v_val_950_; 
v_val_950_ = lean_ctor_get(v_forbidden_937_, 0);
lean_inc(v_val_950_);
lean_dec_ref(v_forbidden_937_);
v___y_912_ = v_a_947_;
v___y_913_ = v___f_870_;
v___y_914_ = v___y_942_;
v___y_915_ = v___y_936_;
v___y_916_ = v___y_938_;
v___y_917_ = v___x_948_;
v___y_918_ = v___y_939_;
v___y_919_ = v___y_941_;
v___y_920_ = v___y_943_;
v___y_921_ = v___y_945_;
v___y_922_ = v___y_944_;
v___y_923_ = v___y_940_;
v___y_924_ = v_val_950_;
goto v___jp_911_;
}
}
else
{
lean_object* v_a_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_958_; 
lean_dec(v_forbidden_937_);
lean_dec(v___y_936_);
lean_dec(v_tk_872_);
v_a_951_ = lean_ctor_get(v___x_946_, 0);
v_isSharedCheck_958_ = !lean_is_exclusive(v___x_946_);
if (v_isSharedCheck_958_ == 0)
{
v___x_953_ = v___x_946_;
v_isShared_954_ = v_isSharedCheck_958_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_a_951_);
lean_dec(v___x_946_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_958_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
lean_object* v___x_956_; 
if (v_isShared_954_ == 0)
{
v___x_956_ = v___x_953_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v_a_951_);
v___x_956_ = v_reuseFailAlloc_957_;
goto v_reusejp_955_;
}
v_reusejp_955_:
{
return v___x_956_;
}
}
}
}
v___jp_959_:
{
size_t v_sz_970_; size_t v___x_971_; lean_object* v___x_972_; 
v_sz_970_ = lean_array_size(v___y_969_);
v___x_971_ = ((size_t)0ULL);
v___x_972_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Rewrites_evalExact_spec__8(v_sz_970_, v___x_971_, v___y_969_);
if (lean_obj_tag(v___x_972_) == 0)
{
lean_object* v___x_973_; 
lean_dec(v___y_962_);
lean_dec(v_tk_872_);
v___x_973_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__0___redArg();
return v___x_973_;
}
else
{
v___y_936_ = v___y_962_;
v_forbidden_937_ = v___x_972_;
v___y_938_ = v___y_964_;
v___y_939_ = v___y_961_;
v___y_940_ = v___y_965_;
v___y_941_ = v___y_967_;
v___y_942_ = v___y_960_;
v___y_943_ = v___y_963_;
v___y_944_ = v___y_968_;
v___y_945_ = v___y_966_;
goto v___jp_935_;
}
}
v___jp_975_:
{
lean_object* v___x_985_; lean_object* v___x_986_; uint8_t v___x_987_; 
v___x_985_ = lean_unsigned_to_nat(2u);
v___x_986_ = l_Lean_Syntax_getArg(v_stx_838_, v___x_985_);
lean_dec(v_stx_838_);
v___x_987_ = l_Lean_Syntax_isNone(v___x_986_);
if (v___x_987_ == 0)
{
uint8_t v___x_988_; 
lean_inc(v___x_986_);
v___x_988_ = l_Lean_Syntax_matchesNull(v___x_986_, v___x_974_);
if (v___x_988_ == 0)
{
lean_object* v___x_989_; 
lean_dec(v___x_986_);
lean_dec(v_loc_976_);
lean_dec(v_tk_872_);
v___x_989_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__0___redArg();
return v___x_989_;
}
else
{
lean_object* v___x_990_; lean_object* v___x_991_; uint8_t v___x_992_; 
v___x_990_ = l_Lean_Syntax_getArg(v___x_986_, v___x_871_);
lean_dec(v___x_986_);
v___x_991_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___closed__10));
lean_inc(v___x_990_);
v___x_992_ = l_Lean_Syntax_isOfKind(v___x_990_, v___x_991_);
if (v___x_992_ == 0)
{
lean_object* v___x_993_; 
lean_dec(v___x_990_);
lean_dec(v_loc_976_);
lean_dec(v_tk_872_);
v___x_993_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Rewrites_evalExact_spec__0___redArg();
return v___x_993_;
}
else
{
lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; uint8_t v___x_998_; 
v___x_994_ = l_Lean_Syntax_getArg(v___x_990_, v___x_974_);
lean_dec(v___x_990_);
v___x_995_ = l_Lean_Syntax_getArgs(v___x_994_);
lean_dec(v___x_994_);
v___x_996_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___closed__11));
v___x_997_ = lean_array_get_size(v___x_995_);
v___x_998_ = lean_nat_dec_lt(v___x_871_, v___x_997_);
if (v___x_998_ == 0)
{
lean_dec_ref(v___x_995_);
v___y_960_ = v___y_981_;
v___y_961_ = v___y_978_;
v___y_962_ = v_loc_976_;
v___y_963_ = v___y_982_;
v___y_964_ = v___y_977_;
v___y_965_ = v___y_979_;
v___y_966_ = v___y_984_;
v___y_967_ = v___y_980_;
v___y_968_ = v___y_983_;
v___y_969_ = v___x_996_;
goto v___jp_959_;
}
else
{
lean_object* v___x_999_; lean_object* v___x_1000_; uint8_t v___x_1001_; 
v___x_999_ = lean_box(v___x_992_);
v___x_1000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1000_, 0, v___x_999_);
lean_ctor_set(v___x_1000_, 1, v___x_996_);
v___x_1001_ = lean_nat_dec_le(v___x_997_, v___x_997_);
if (v___x_1001_ == 0)
{
if (v___x_998_ == 0)
{
lean_dec_ref(v___x_1000_);
lean_dec_ref(v___x_995_);
v___y_960_ = v___y_981_;
v___y_961_ = v___y_978_;
v___y_962_ = v_loc_976_;
v___y_963_ = v___y_982_;
v___y_964_ = v___y_977_;
v___y_965_ = v___y_979_;
v___y_966_ = v___y_984_;
v___y_967_ = v___y_980_;
v___y_968_ = v___y_983_;
v___y_969_ = v___x_996_;
goto v___jp_959_;
}
else
{
size_t v___x_1002_; size_t v___x_1003_; lean_object* v___x_1004_; lean_object* v_snd_1005_; 
v___x_1002_ = ((size_t)0ULL);
v___x_1003_ = lean_usize_of_nat(v___x_997_);
v___x_1004_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Rewrites_evalExact_spec__9(v___x_992_, v___x_987_, v___x_995_, v___x_1002_, v___x_1003_, v___x_1000_);
lean_dec_ref(v___x_995_);
v_snd_1005_ = lean_ctor_get(v___x_1004_, 1);
lean_inc(v_snd_1005_);
lean_dec_ref(v___x_1004_);
v___y_960_ = v___y_981_;
v___y_961_ = v___y_978_;
v___y_962_ = v_loc_976_;
v___y_963_ = v___y_982_;
v___y_964_ = v___y_977_;
v___y_965_ = v___y_979_;
v___y_966_ = v___y_984_;
v___y_967_ = v___y_980_;
v___y_968_ = v___y_983_;
v___y_969_ = v_snd_1005_;
goto v___jp_959_;
}
}
else
{
size_t v___x_1006_; size_t v___x_1007_; lean_object* v___x_1008_; lean_object* v_snd_1009_; 
v___x_1006_ = ((size_t)0ULL);
v___x_1007_ = lean_usize_of_nat(v___x_997_);
v___x_1008_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Rewrites_evalExact_spec__9(v___x_992_, v___x_987_, v___x_995_, v___x_1006_, v___x_1007_, v___x_1000_);
lean_dec_ref(v___x_995_);
v_snd_1009_ = lean_ctor_get(v___x_1008_, 1);
lean_inc(v_snd_1009_);
lean_dec_ref(v___x_1008_);
v___y_960_ = v___y_981_;
v___y_961_ = v___y_978_;
v___y_962_ = v_loc_976_;
v___y_963_ = v___y_982_;
v___y_964_ = v___y_977_;
v___y_965_ = v___y_979_;
v___y_966_ = v___y_984_;
v___y_967_ = v___y_980_;
v___y_968_ = v___y_983_;
v___y_969_ = v_snd_1009_;
goto v___jp_959_;
}
}
}
}
}
else
{
lean_object* v___x_1010_; 
lean_dec(v___x_986_);
v___x_1010_ = lean_box(0);
v___y_936_ = v_loc_976_;
v_forbidden_937_ = v___x_1010_;
v___y_938_ = v___y_977_;
v___y_939_ = v___y_978_;
v___y_940_ = v___y_979_;
v___y_941_ = v___y_980_;
v___y_942_ = v___y_981_;
v___y_943_ = v___y_982_;
v___y_944_ = v___y_983_;
v___y_945_ = v___y_984_;
goto v___jp_935_;
}
}
}
v___jp_848_:
{
lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; 
v___x_861_ = l_Lean_mkOptionalNode(v___y_860_);
v___x_862_ = l_Lean_Elab_Tactic_expandOptLocation(v___x_861_);
lean_dec(v___x_861_);
lean_inc_ref(v___y_849_);
v___x_863_ = l_Lean_Elab_Tactic_withLocation(v___x_862_, v___y_851_, v___y_859_, v___y_849_, v___y_852_, v___y_854_, v___y_858_, v___y_853_, v___y_850_, v___y_855_, v___y_857_, v___y_856_);
lean_dec(v___x_862_);
return v___x_863_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Rewrites_evalExact___boxed(lean_object* v_stx_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_){
_start:
{
lean_object* v_res_1028_; 
v_res_1028_ = l_Lean_Elab_Rewrites_evalExact(v_stx_1018_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_);
lean_dec(v_a_1026_);
lean_dec_ref(v_a_1025_);
lean_dec(v_a_1024_);
lean_dec_ref(v_a_1023_);
lean_dec(v_a_1022_);
lean_dec_ref(v_a_1021_);
lean_dec(v_a_1020_);
lean_dec_ref(v_a_1019_);
return v_res_1028_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__1(lean_object* v_00_u03b1_1029_, lean_object* v_msg_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_){
_start:
{
lean_object* v___x_1040_; 
v___x_1040_ = l_Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__1___redArg(v_msg_1030_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_);
return v___x_1040_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__1___boxed(lean_object* v_00_u03b1_1041_, lean_object* v_msg_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_){
_start:
{
lean_object* v_res_1052_; 
v_res_1052_ = l_Lean_throwError___at___00Lean_Elab_Rewrites_evalExact_spec__1(v_00_u03b1_1041_, v_msg_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_);
lean_dec(v___y_1050_);
lean_dec_ref(v___y_1049_);
lean_dec(v___y_1048_);
lean_dec_ref(v___y_1047_);
lean_dec(v___y_1046_);
lean_dec_ref(v___y_1045_);
lean_dec(v___y_1044_);
lean_dec_ref(v___y_1043_);
return v_res_1052_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__5(lean_object* v_f_1053_, lean_object* v_tk_1054_, lean_object* v_as_1055_, lean_object* v_as_x27_1056_, lean_object* v_b_1057_, lean_object* v_a_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_){
_start:
{
lean_object* v___x_1068_; 
v___x_1068_ = l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__5___redArg(v_f_1053_, v_tk_1054_, v_as_x27_1056_, v_b_1057_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_);
return v___x_1068_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__5___boxed(lean_object* v_f_1069_, lean_object* v_tk_1070_, lean_object* v_as_1071_, lean_object* v_as_x27_1072_, lean_object* v_b_1073_, lean_object* v_a_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_){
_start:
{
lean_object* v_res_1084_; 
v_res_1084_ = l_List_forIn_x27_loop___at___00Lean_Elab_Rewrites_evalExact_spec__5(v_f_1069_, v_tk_1070_, v_as_1071_, v_as_x27_1072_, v_b_1073_, v_a_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_);
lean_dec(v___y_1082_);
lean_dec_ref(v___y_1081_);
lean_dec(v___y_1080_);
lean_dec_ref(v___y_1079_);
lean_dec(v___y_1078_);
lean_dec_ref(v___y_1077_);
lean_dec(v___y_1076_);
lean_dec_ref(v___y_1075_);
lean_dec(v_as_1071_);
return v_res_1084_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1(){
_start:
{
lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; 
v___x_1094_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1095_ = ((lean_object*)(l_Lean_Elab_Rewrites_evalExact___closed__4));
v___x_1096_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___closed__3));
v___x_1097_ = lean_alloc_closure((void*)(l_Lean_Elab_Rewrites_evalExact___boxed), 10, 0);
v___x_1098_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1094_, v___x_1095_, v___x_1096_, v___x_1097_);
return v___x_1098_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___boxed(lean_object* v_a_1099_){
_start:
{
lean_object* v_res_1100_; 
v_res_1100_ = l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1();
return v_res_1100_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3(){
_start:
{
lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; 
v___x_1127_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact__1___closed__3));
v___x_1128_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___closed__6));
v___x_1129_ = l_Lean_addBuiltinDeclarationRanges(v___x_1127_, v___x_1128_);
return v___x_1129_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3___boxed(lean_object* v_a_1130_){
_start:
{
lean_object* v_res_1131_; 
v_res_1131_ = l___private_Lean_Elab_Tactic_Rewrites_0__Lean_Elab_Rewrites_evalExact___regBuiltin_Lean_Elab_Rewrites_evalExact_declRange__3();
return v_res_1131_;
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
