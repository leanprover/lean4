// Lean compiler output
// Module: Lean.Elab.Tactic.Split
// Imports: public import Lean.Meta.Tactic.Split public import Lean.Elab.Tactic.Location
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
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getNondepPropHyps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Meta_splitLocalDecl_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Meta_splitTarget_x3f(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_hint_x27(lean_object*);
extern lean_object* l_Lean_MessageData_nil;
lean_object* l_Lean_MessageData_ofLazyM(lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_MessageData_joinSep(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_MessageData_andList(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
uint8_t l_Lean_isStructure(lean_object*, lean_object*);
lean_object* l_Lean_getStructureFields(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isIdent(lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
uint8_t l_Lean_Name_isStr(lean_object*);
lean_object* l_Lean_LocalContext_findFromUserName_x3f(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Array_mkArray0___redArg();
lean_object* l_Lean_mkIdent(lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_hint(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getFVarId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getType___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_inlineExpr(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_expandOptLocation(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getBoolOption___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint_spec__0___redArg(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getBoolOption___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getBoolOption___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getBoolOption___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 87, .m_capacity = 87, .m_length = 86, .m_data = "Use `set_option trace.split.failure true` to display additional diagnostic information"};
static const lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___lam__0___closed__1;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___lam__0___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "split"};
static const lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "failure"};
static const lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__1_value),LEAN_SCALAR_PTR_LITERAL(66, 167, 105, 68, 61, 13, 118, 183)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__2_value),LEAN_SCALAR_PTR_LITERAL(58, 89, 146, 5, 74, 122, 101, 113)}};
static const lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__3_value;
static const lean_closure_object l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___lam__0___boxed, .m_arity = 7, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__4_value;
static const lean_array_object l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__5_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint;
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "tactic"};
static const lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(99, 76, 33, 121, 85, 143, 17, 224)}};
static const lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__1_value),LEAN_SCALAR_PTR_LITERAL(104, 58, 38, 157, 113, 69, 9, 24)}};
static const lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__5_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__6_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__7_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__8;
static const lean_string_object l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "location"};
static const lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__9 = (const lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__9_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__10_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__10_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__10_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__9_value),LEAN_SCALAR_PTR_LITERAL(124, 82, 43, 228, 241, 102, 135, 24)}};
static const lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__10 = (const lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__10_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "at"};
static const lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__11 = (const lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__11_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "locationHyp"};
static const lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__12 = (const lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__12_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__13_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__13_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__13_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__12_value),LEAN_SCALAR_PTR_LITERAL(229, 146, 67, 234, 45, 36, 143, 176)}};
static const lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__13 = (const lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__13_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "To apply `split` at the hypothesis `"};
static const lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__14 = (const lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__14_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__15;
static const lean_string_object l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "`, use `split at "};
static const lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__16 = (const lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__16_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__17;
static const lean_string_object l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`:"};
static const lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__18 = (const lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__18_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__19;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 71, .m_capacity = 71, .m_length = 70, .m_data = "Tactic `split` failed: Specifying a term to split is not supported yet"};
static const lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__0___closed__0 = (const lean_object*)&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__0___closed__0_value;
static lean_once_cell_t l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__0___closed__1;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 53, .m_capacity = 53, .m_length = 52, .m_data = "Tactic `split` failed: Specifying multiple targets ("};
static const lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__1;
static const lean_string_object l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = ") is not supported"};
static const lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__3;
static const lean_string_object l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 112, .m_capacity = 112, .m_length = 111, .m_data = "Specify a single target to split, or use `split at *` to split the first target that can be automatically split"};
static const lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__5;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__6;
static const lean_string_object l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "hypotheses"};
static const lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__7_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__8;
static const lean_string_object l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "hypothesis"};
static const lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__9 = (const lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__9_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__10;
static const lean_string_object l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__11 = (const lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__11_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "the goal and "};
static const lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__12 = (const lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__12_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "If you meant to destruct this "};
static const lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__1;
static const lean_string_object l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = ", use the `cases` tactic instead"};
static const lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__3;
static const lean_string_object l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "And"};
static const lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(49, 220, 212, 156, 122, 214, 55, 135)}};
static const lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__5_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Prod"};
static const lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__6_value),LEAN_SCALAR_PTR_LITERAL(121, 119, 164, 206, 221, 118, 48, 212)}};
static const lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__7_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "structure"};
static const lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__8_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "pair"};
static const lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__9 = (const lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__9_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "conjunction"};
static const lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__10 = (const lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__10_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__1_value),LEAN_SCALAR_PTR_LITERAL(249, 90, 54, 167, 41, 130, 106, 252)}};
static const lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 58, .m_capacity = 58, .m_length = 57, .m_data = "Could not split an `if` or `match` expression in the goal"};
static const lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal___closed__1_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 58, .m_capacity = 58, .m_length = 57, .m_data = "Could not split an `if` or `match` expression in the type"};
static const lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp___closed__1;
static const lean_string_object l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "of `"};
static const lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard_spec__0(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 187, .m_capacity = 187, .m_length = 186, .m_data = "`split at *` does not attempt to split at non-propositional hypotheses or those on which other hypotheses depend. It may still be possible to manually split a hypothesis using `split at`"};
static const lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__0_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__1_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__2;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__3;
static const lean_string_object l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 89, .m_capacity = 89, .m_length = 88, .m_data = "Could not split the goal, and no hypotheses that could be automatically split were found"};
static const lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__5;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__6;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__7;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__8;
static const lean_string_object l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__9 = (const lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__9_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__9_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__10 = (const lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__10_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__11;
static const lean_string_object l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 62, .m_capacity = 62, .m_length = 61, .m_data = "Could not split the goal or any of the following hypotheses: "};
static const lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__12 = (const lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__12_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__13;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSplit_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSplit_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSplit_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSplit_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSplit_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSplit___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSplit___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSplit___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSplit___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSplit___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSplit___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_evalSplit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_evalSplit___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_evalSplit___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_evalSplit___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSplit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSplit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "evalSplit"};
static const lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit__1___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit__1___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(102, 41, 135, 116, 35, 116, 137, 89)}};
static const lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(14) << 1) | 1)),((lean_object*)(((size_t)(43) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(38) << 1) | 1)),((lean_object*)(((size_t)(20) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___closed__0_value),((lean_object*)(((size_t)(43) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___closed__1_value),((lean_object*)(((size_t)(20) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(14) << 1) | 1)),((lean_object*)(((size_t)(47) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(14) << 1) | 1)),((lean_object*)(((size_t)(56) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___closed__3_value),((lean_object*)(((size_t)(47) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___closed__4_value),((lean_object*)(((size_t)(56) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getBoolOption___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint_spec__0___redArg(lean_object* v_k_1_, uint8_t v_defValue_2_, lean_object* v___y_3_){
_start:
{
lean_object* v___x_5_; lean_object* v_map_6_; lean_object* v___x_7_; 
v___x_5_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_3_);
v_map_6_ = lean_ctor_get(v___x_5_, 0);
lean_inc(v_map_6_);
lean_dec_ref(v___x_5_);
v___x_7_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_6_, v_k_1_);
lean_dec(v_map_6_);
if (lean_obj_tag(v___x_7_) == 0)
{
lean_object* v___x_8_; lean_object* v___x_9_; 
v___x_8_ = lean_box(v_defValue_2_);
v___x_9_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_9_, 0, v___x_8_);
return v___x_9_;
}
else
{
lean_object* v_val_10_; lean_object* v___x_12_; uint8_t v_isShared_13_; uint8_t v_isSharedCheck_23_; 
v_val_10_ = lean_ctor_get(v___x_7_, 0);
v_isSharedCheck_23_ = !lean_is_exclusive(v___x_7_);
if (v_isSharedCheck_23_ == 0)
{
v___x_12_ = v___x_7_;
v_isShared_13_ = v_isSharedCheck_23_;
goto v_resetjp_11_;
}
else
{
lean_inc(v_val_10_);
lean_dec(v___x_7_);
v___x_12_ = lean_box(0);
v_isShared_13_ = v_isSharedCheck_23_;
goto v_resetjp_11_;
}
v_resetjp_11_:
{
if (lean_obj_tag(v_val_10_) == 1)
{
uint8_t v_v_14_; lean_object* v___x_15_; lean_object* v___x_17_; 
v_v_14_ = lean_ctor_get_uint8(v_val_10_, 0);
lean_dec_ref_known(v_val_10_, 0);
v___x_15_ = lean_box(v_v_14_);
if (v_isShared_13_ == 0)
{
lean_ctor_set_tag(v___x_12_, 0);
lean_ctor_set(v___x_12_, 0, v___x_15_);
v___x_17_ = v___x_12_;
goto v_reusejp_16_;
}
else
{
lean_object* v_reuseFailAlloc_18_; 
v_reuseFailAlloc_18_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_18_, 0, v___x_15_);
v___x_17_ = v_reuseFailAlloc_18_;
goto v_reusejp_16_;
}
v_reusejp_16_:
{
return v___x_17_;
}
}
else
{
lean_object* v___x_19_; lean_object* v___x_21_; 
lean_dec(v_val_10_);
v___x_19_ = lean_box(v_defValue_2_);
if (v_isShared_13_ == 0)
{
lean_ctor_set_tag(v___x_12_, 0);
lean_ctor_set(v___x_12_, 0, v___x_19_);
v___x_21_ = v___x_12_;
goto v_reusejp_20_;
}
else
{
lean_object* v_reuseFailAlloc_22_; 
v_reuseFailAlloc_22_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_22_, 0, v___x_19_);
v___x_21_ = v_reuseFailAlloc_22_;
goto v_reusejp_20_;
}
v_reusejp_20_:
{
return v___x_21_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getBoolOption___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint_spec__0___redArg___boxed(lean_object* v_k_24_, lean_object* v_defValue_25_, lean_object* v___y_26_, lean_object* v___y_27_){
_start:
{
uint8_t v_defValue_boxed_28_; lean_object* v_res_29_; 
v_defValue_boxed_28_ = lean_unbox(v_defValue_25_);
v_res_29_ = l_Lean_getBoolOption___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint_spec__0___redArg(v_k_24_, v_defValue_boxed_28_, v___y_26_);
lean_dec_ref(v___y_26_);
lean_dec(v_k_24_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBoolOption___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint_spec__0(lean_object* v_k_30_, uint8_t v_defValue_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = l_Lean_getBoolOption___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint_spec__0___redArg(v_k_30_, v_defValue_31_, v___y_34_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBoolOption___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint_spec__0___boxed(lean_object* v_k_38_, lean_object* v_defValue_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_){
_start:
{
uint8_t v_defValue_boxed_45_; lean_object* v_res_46_; 
v_defValue_boxed_45_ = lean_unbox(v_defValue_39_);
v_res_46_ = l_Lean_getBoolOption___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint_spec__0(v_k_38_, v_defValue_boxed_45_, v___y_40_, v___y_41_, v___y_42_, v___y_43_);
lean_dec(v___y_43_);
lean_dec_ref(v___y_42_);
lean_dec(v___y_41_);
lean_dec_ref(v___y_40_);
lean_dec(v_k_38_);
return v_res_46_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___lam__0___closed__1(void){
_start:
{
lean_object* v___x_48_; lean_object* v___x_49_; 
v___x_48_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___lam__0___closed__0));
v___x_49_ = l_Lean_stringToMessageData(v___x_48_);
return v___x_49_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___lam__0___closed__2(void){
_start:
{
lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_50_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___lam__0___closed__1, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___lam__0___closed__1);
v___x_51_ = l_Lean_MessageData_hint_x27(v___x_50_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___lam__0(lean_object* v___x_52_, uint8_t v___x_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_){
_start:
{
lean_object* v___x_59_; lean_object* v_a_60_; lean_object* v___x_62_; uint8_t v_isShared_63_; uint8_t v_isSharedCheck_73_; 
v___x_59_ = l_Lean_getBoolOption___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint_spec__0___redArg(v___x_52_, v___x_53_, v___y_56_);
v_a_60_ = lean_ctor_get(v___x_59_, 0);
v_isSharedCheck_73_ = !lean_is_exclusive(v___x_59_);
if (v_isSharedCheck_73_ == 0)
{
v___x_62_ = v___x_59_;
v_isShared_63_ = v_isSharedCheck_73_;
goto v_resetjp_61_;
}
else
{
lean_inc(v_a_60_);
lean_dec(v___x_59_);
v___x_62_ = lean_box(0);
v_isShared_63_ = v_isSharedCheck_73_;
goto v_resetjp_61_;
}
v_resetjp_61_:
{
uint8_t v___x_64_; 
v___x_64_ = lean_unbox(v_a_60_);
lean_dec(v_a_60_);
if (v___x_64_ == 0)
{
lean_object* v___x_65_; lean_object* v___x_67_; 
v___x_65_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___lam__0___closed__2, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___lam__0___closed__2_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___lam__0___closed__2);
if (v_isShared_63_ == 0)
{
lean_ctor_set(v___x_62_, 0, v___x_65_);
v___x_67_ = v___x_62_;
goto v_reusejp_66_;
}
else
{
lean_object* v_reuseFailAlloc_68_; 
v_reuseFailAlloc_68_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_68_, 0, v___x_65_);
v___x_67_ = v_reuseFailAlloc_68_;
goto v_reusejp_66_;
}
v_reusejp_66_:
{
return v___x_67_;
}
}
else
{
lean_object* v___x_69_; lean_object* v___x_71_; 
v___x_69_ = l_Lean_MessageData_nil;
if (v_isShared_63_ == 0)
{
lean_ctor_set(v___x_62_, 0, v___x_69_);
v___x_71_ = v___x_62_;
goto v_reusejp_70_;
}
else
{
lean_object* v_reuseFailAlloc_72_; 
v_reuseFailAlloc_72_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_72_, 0, v___x_69_);
v___x_71_ = v_reuseFailAlloc_72_;
goto v_reusejp_70_;
}
v_reusejp_70_:
{
return v___x_71_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___lam__0___boxed(lean_object* v___x_74_, lean_object* v___x_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_){
_start:
{
uint8_t v___x_676__boxed_81_; lean_object* v_res_82_; 
v___x_676__boxed_81_ = lean_unbox(v___x_75_);
v_res_82_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___lam__0(v___x_74_, v___x_676__boxed_81_, v___y_76_, v___y_77_, v___y_78_, v___y_79_);
lean_dec(v___y_79_);
lean_dec_ref(v___y_78_);
lean_dec(v___y_77_);
lean_dec_ref(v___y_76_);
lean_dec(v___x_74_);
return v_res_82_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__6(void){
_start:
{
lean_object* v___x_96_; lean_object* v___f_97_; lean_object* v___x_98_; 
v___x_96_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__5));
v___f_97_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__4));
v___x_98_ = l_Lean_MessageData_ofLazyM(v___f_97_, v___x_96_);
return v___x_98_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint(void){
_start:
{
lean_object* v___x_99_; 
v___x_99_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__6, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__6_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__6);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0_spec__0_spec__1(lean_object* v_msgData_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_){
_start:
{
lean_object* v___x_106_; lean_object* v_env_107_; uint8_t v___x_108_; lean_object* v_env_109_; lean_object* v___x_110_; lean_object* v_toCold_111_; lean_object* v_mctx_112_; lean_object* v_lctx_113_; lean_object* v_options_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_106_ = lean_st_ref_get(v___y_104_);
v_env_107_ = lean_ctor_get(v___x_106_, 0);
lean_inc_ref(v_env_107_);
lean_dec(v___x_106_);
v___x_108_ = 0;
v_env_109_ = l_Lean_Environment_setRecordingDeps(v_env_107_, v___x_108_);
v___x_110_ = lean_st_ref_get(v___y_102_);
v_toCold_111_ = lean_ctor_get(v___y_103_, 0);
v_mctx_112_ = lean_ctor_get(v___x_110_, 0);
lean_inc_ref(v_mctx_112_);
lean_dec(v___x_110_);
v_lctx_113_ = lean_ctor_get(v___y_101_, 2);
v_options_114_ = lean_ctor_get(v_toCold_111_, 2);
lean_inc_ref(v_options_114_);
lean_inc_ref(v_lctx_113_);
v___x_115_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_115_, 0, v_env_109_);
lean_ctor_set(v___x_115_, 1, v_mctx_112_);
lean_ctor_set(v___x_115_, 2, v_lctx_113_);
lean_ctor_set(v___x_115_, 3, v_options_114_);
v___x_116_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_116_, 0, v___x_115_);
lean_ctor_set(v___x_116_, 1, v_msgData_100_);
v___x_117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_117_, 0, v___x_116_);
return v___x_117_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0_spec__0_spec__1(v_msgData_118_, v___y_119_, v___y_120_, v___y_121_, v___y_122_);
lean_dec(v___y_122_);
lean_dec_ref(v___y_121_);
lean_dec(v___y_120_);
lean_dec_ref(v___y_119_);
return v_res_124_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0_spec__0___redArg(lean_object* v_msg_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_){
_start:
{
lean_object* v_ref_131_; lean_object* v___x_132_; lean_object* v_a_133_; lean_object* v___x_135_; uint8_t v_isShared_136_; uint8_t v_isSharedCheck_141_; 
v_ref_131_ = lean_ctor_get(v___y_128_, 2);
v___x_132_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0_spec__0_spec__1(v_msg_125_, v___y_126_, v___y_127_, v___y_128_, v___y_129_);
v_a_133_ = lean_ctor_get(v___x_132_, 0);
v_isSharedCheck_141_ = !lean_is_exclusive(v___x_132_);
if (v_isSharedCheck_141_ == 0)
{
v___x_135_ = v___x_132_;
v_isShared_136_ = v_isSharedCheck_141_;
goto v_resetjp_134_;
}
else
{
lean_inc(v_a_133_);
lean_dec(v___x_132_);
v___x_135_ = lean_box(0);
v_isShared_136_ = v_isSharedCheck_141_;
goto v_resetjp_134_;
}
v_resetjp_134_:
{
lean_object* v___x_137_; lean_object* v___x_139_; 
lean_inc(v_ref_131_);
v___x_137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_137_, 0, v_ref_131_);
lean_ctor_set(v___x_137_, 1, v_a_133_);
if (v_isShared_136_ == 0)
{
lean_ctor_set_tag(v___x_135_, 1);
lean_ctor_set(v___x_135_, 0, v___x_137_);
v___x_139_ = v___x_135_;
goto v_reusejp_138_;
}
else
{
lean_object* v_reuseFailAlloc_140_; 
v_reuseFailAlloc_140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_140_, 0, v___x_137_);
v___x_139_ = v_reuseFailAlloc_140_;
goto v_reusejp_138_;
}
v_reusejp_138_:
{
return v___x_139_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0_spec__0___redArg___boxed(lean_object* v_msg_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_){
_start:
{
lean_object* v_res_148_; 
v_res_148_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0_spec__0___redArg(v_msg_142_, v___y_143_, v___y_144_, v___y_145_, v___y_146_);
lean_dec(v___y_146_);
lean_dec_ref(v___y_145_);
lean_dec(v___y_144_);
lean_dec_ref(v___y_143_);
return v_res_148_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0___redArg(lean_object* v_ref_149_, lean_object* v_msg_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_){
_start:
{
lean_object* v_toCold_160_; lean_object* v_currRecDepth_161_; lean_object* v_ref_162_; uint16_t v_optionFlags_163_; uint8_t v_suppressElabErrors_164_; uint8_t v_isRecordingDeps_165_; lean_object* v_ref_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
v_toCold_160_ = lean_ctor_get(v___y_157_, 0);
v_currRecDepth_161_ = lean_ctor_get(v___y_157_, 1);
v_ref_162_ = lean_ctor_get(v___y_157_, 2);
v_optionFlags_163_ = lean_ctor_get_uint16(v___y_157_, sizeof(void*)*3);
v_suppressElabErrors_164_ = lean_ctor_get_uint8(v___y_157_, sizeof(void*)*3 + 2);
v_isRecordingDeps_165_ = lean_ctor_get_uint8(v___y_157_, sizeof(void*)*3 + 3);
v_ref_166_ = l_Lean_replaceRef(v_ref_149_, v_ref_162_);
lean_inc(v_currRecDepth_161_);
lean_inc_ref(v_toCold_160_);
v___x_167_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_167_, 0, v_toCold_160_);
lean_ctor_set(v___x_167_, 1, v_currRecDepth_161_);
lean_ctor_set(v___x_167_, 2, v_ref_166_);
lean_ctor_set_uint16(v___x_167_, sizeof(void*)*3, v_optionFlags_163_);
lean_ctor_set_uint8(v___x_167_, sizeof(void*)*3 + 2, v_suppressElabErrors_164_);
lean_ctor_set_uint8(v___x_167_, sizeof(void*)*3 + 3, v_isRecordingDeps_165_);
v___x_168_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0_spec__0___redArg(v_msg_150_, v___y_155_, v___y_156_, v___x_167_, v___y_158_);
lean_dec_ref_known(v___x_167_, 3);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0___redArg___boxed(lean_object* v_ref_169_, lean_object* v_msg_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0___redArg(v_ref_169_, v_msg_170_, v___y_171_, v___y_172_, v___y_173_, v___y_174_, v___y_175_, v___y_176_, v___y_177_, v___y_178_);
lean_dec(v___y_178_);
lean_dec_ref(v___y_177_);
lean_dec(v___y_176_);
lean_dec_ref(v___y_175_);
lean_dec(v___y_174_);
lean_dec_ref(v___y_173_);
lean_dec(v___y_172_);
lean_dec_ref(v___y_171_);
lean_dec(v_ref_169_);
return v_res_180_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__8(void){
_start:
{
lean_object* v___x_195_; 
v___x_195_ = l_Array_mkArray0___redArg();
return v___x_195_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__15(void){
_start:
{
lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_210_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__14));
v___x_211_ = l_Lean_stringToMessageData(v___x_210_);
return v___x_211_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__17(void){
_start:
{
lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_213_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__16));
v___x_214_ = l_Lean_stringToMessageData(v___x_213_);
return v___x_214_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__19(void){
_start:
{
lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_216_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__18));
v___x_217_ = l_Lean_stringToMessageData(v___x_216_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0(uint8_t v___x_218_, lean_object* v_t_219_, lean_object* v_error_220_, lean_object* v_loc_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_){
_start:
{
if (v___x_218_ == 0)
{
lean_object* v___x_231_; 
lean_dec(v_loc_221_);
v___x_231_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0___redArg(v_t_219_, v_error_220_, v___y_222_, v___y_223_, v___y_224_, v___y_225_, v___y_226_, v___y_227_, v___y_228_, v___y_229_);
return v___x_231_;
}
else
{
lean_object* v_name_232_; uint8_t v___x_233_; 
v_name_232_ = l_Lean_Syntax_getId(v_t_219_);
v___x_233_ = l_Lean_Name_isStr(v_name_232_);
if (v___x_233_ == 0)
{
lean_object* v___x_234_; 
lean_dec(v_name_232_);
lean_dec(v_loc_221_);
v___x_234_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0___redArg(v_t_219_, v_error_220_, v___y_222_, v___y_223_, v___y_224_, v___y_225_, v___y_226_, v___y_227_, v___y_228_, v___y_229_);
return v___x_234_;
}
else
{
if (lean_obj_tag(v_loc_221_) == 0)
{
lean_object* v_lctx_235_; lean_object* v___x_236_; 
v_lctx_235_ = lean_ctor_get(v___y_226_, 2);
v___x_236_ = l_Lean_LocalContext_findFromUserName_x3f(v_lctx_235_, v_name_232_);
if (lean_obj_tag(v___x_236_) == 1)
{
lean_object* v_val_237_; lean_object* v_ref_238_; lean_object* v___x_239_; uint8_t v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; uint8_t v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; 
v_val_237_ = lean_ctor_get(v___x_236_, 0);
lean_inc(v_val_237_);
lean_dec_ref_known(v___x_236_, 1);
v_ref_238_ = lean_ctor_get(v___y_228_, 2);
v___x_239_ = l_Lean_LocalDecl_toExpr(v_val_237_);
v___x_240_ = 0;
v___x_241_ = l_Lean_SourceInfo_fromRef(v_ref_238_, v___x_240_);
v___x_242_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__1));
v___x_243_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__1));
v___x_244_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__5));
lean_inc_n(v___x_241_, 7);
v___x_245_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_245_, 0, v___x_241_);
lean_ctor_set(v___x_245_, 1, v___x_243_);
v___x_246_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__7));
v___x_247_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__8, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__8_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__8);
v___x_248_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_248_, 0, v___x_241_);
lean_ctor_set(v___x_248_, 1, v___x_246_);
lean_ctor_set(v___x_248_, 2, v___x_247_);
v___x_249_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__10));
v___x_250_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__11));
v___x_251_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_251_, 0, v___x_241_);
lean_ctor_set(v___x_251_, 1, v___x_250_);
v___x_252_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__13));
v___x_253_ = l_Lean_mkIdent(v_name_232_);
v___x_254_ = l_Lean_Syntax_node1(v___x_241_, v___x_246_, v___x_253_);
v___x_255_ = l_Lean_Syntax_node1(v___x_241_, v___x_252_, v___x_254_);
v___x_256_ = l_Lean_Syntax_node2(v___x_241_, v___x_249_, v___x_251_, v___x_255_);
v___x_257_ = l_Lean_Syntax_node1(v___x_241_, v___x_246_, v___x_256_);
v___x_258_ = l_Lean_Syntax_node3(v___x_241_, v___x_244_, v___x_245_, v___x_248_, v___x_257_);
v___x_259_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__15, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__15_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__15);
v___x_260_ = l_Lean_MessageData_ofExpr(v___x_239_);
lean_inc_ref(v___x_260_);
v___x_261_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_261_, 0, v___x_259_);
lean_ctor_set(v___x_261_, 1, v___x_260_);
v___x_262_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__17, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__17_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__17);
v___x_263_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_263_, 0, v___x_261_);
lean_ctor_set(v___x_263_, 1, v___x_262_);
v___x_264_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_264_, 0, v___x_263_);
lean_ctor_set(v___x_264_, 1, v___x_260_);
v___x_265_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__19, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__19_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__19);
v___x_266_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_266_, 0, v___x_264_);
lean_ctor_set(v___x_266_, 1, v___x_265_);
v___x_267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_267_, 0, v___x_242_);
lean_ctor_set(v___x_267_, 1, v___x_258_);
v___x_268_ = lean_box(0);
v___x_269_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_269_, 0, v___x_267_);
lean_ctor_set(v___x_269_, 1, v___x_268_);
lean_ctor_set(v___x_269_, 2, v___x_268_);
lean_ctor_set(v___x_269_, 3, v___x_268_);
lean_ctor_set(v___x_269_, 4, v___x_268_);
lean_ctor_set(v___x_269_, 5, v___x_268_);
v___x_270_ = 0;
v___x_271_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_271_, 0, v___x_269_);
lean_ctor_set(v___x_271_, 1, v_loc_221_);
lean_ctor_set(v___x_271_, 2, v_loc_221_);
lean_ctor_set_uint8(v___x_271_, sizeof(void*)*3, v___x_270_);
v___x_272_ = lean_unsigned_to_nat(1u);
v___x_273_ = lean_mk_empty_array_with_capacity(v___x_272_);
v___x_274_ = lean_array_push(v___x_273_, v___x_271_);
v___x_275_ = l_Lean_MessageData_hint(v___x_266_, v___x_274_, v_loc_221_, v___x_268_, v___x_240_, v___y_228_, v___y_229_);
lean_dec_ref(v___x_274_);
if (lean_obj_tag(v___x_275_) == 0)
{
lean_object* v_a_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
v_a_276_ = lean_ctor_get(v___x_275_, 0);
lean_inc(v_a_276_);
lean_dec_ref_known(v___x_275_, 1);
v___x_277_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_277_, 0, v_error_220_);
lean_ctor_set(v___x_277_, 1, v_a_276_);
v___x_278_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0___redArg(v_t_219_, v___x_277_, v___y_222_, v___y_223_, v___y_224_, v___y_225_, v___y_226_, v___y_227_, v___y_228_, v___y_229_);
return v___x_278_;
}
else
{
lean_object* v_a_279_; lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_286_; 
lean_dec_ref(v_error_220_);
v_a_279_ = lean_ctor_get(v___x_275_, 0);
v_isSharedCheck_286_ = !lean_is_exclusive(v___x_275_);
if (v_isSharedCheck_286_ == 0)
{
v___x_281_ = v___x_275_;
v_isShared_282_ = v_isSharedCheck_286_;
goto v_resetjp_280_;
}
else
{
lean_inc(v_a_279_);
lean_dec(v___x_275_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_286_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
lean_object* v___x_284_; 
if (v_isShared_282_ == 0)
{
v___x_284_ = v___x_281_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v_a_279_);
v___x_284_ = v_reuseFailAlloc_285_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
return v___x_284_;
}
}
}
}
else
{
lean_object* v___x_287_; 
lean_dec(v___x_236_);
lean_dec(v_name_232_);
v___x_287_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0___redArg(v_t_219_, v_error_220_, v___y_222_, v___y_223_, v___y_224_, v___y_225_, v___y_226_, v___y_227_, v___y_228_, v___y_229_);
return v___x_287_;
}
}
else
{
lean_object* v___x_288_; 
lean_dec_ref_known(v_loc_221_, 1);
lean_dec(v_name_232_);
v___x_288_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0___redArg(v_t_219_, v_error_220_, v___y_222_, v___y_223_, v___y_224_, v___y_225_, v___y_226_, v___y_227_, v___y_228_, v___y_229_);
return v___x_288_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___boxed(lean_object* v___x_289_, lean_object* v_t_290_, lean_object* v_error_291_, lean_object* v_loc_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_){
_start:
{
uint8_t v___x_6480__boxed_302_; lean_object* v_res_303_; 
v___x_6480__boxed_302_ = lean_unbox(v___x_289_);
v_res_303_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0(v___x_6480__boxed_302_, v_t_290_, v_error_291_, v_loc_292_, v___y_293_, v___y_294_, v___y_295_, v___y_296_, v___y_297_, v___y_298_, v___y_299_, v___y_300_);
lean_dec(v___y_300_);
lean_dec_ref(v___y_299_);
lean_dec(v___y_298_);
lean_dec_ref(v___y_297_);
lean_dec(v___y_296_);
lean_dec_ref(v___y_295_);
lean_dec(v___y_294_);
lean_dec_ref(v___y_293_);
lean_dec(v_t_290_);
return v_res_303_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___closed__1(void){
_start:
{
lean_object* v___x_305_; lean_object* v_error_306_; 
v___x_305_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___closed__0));
v_error_306_ = l_Lean_stringToMessageData(v___x_305_);
return v_error_306_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported(lean_object* v_t_307_, lean_object* v_loc_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_){
_start:
{
lean_object* v_error_318_; uint8_t v___x_319_; lean_object* v___x_320_; lean_object* v___y_321_; lean_object* v___x_322_; 
v_error_318_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___closed__1, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___closed__1_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___closed__1);
v___x_319_ = l_Lean_Syntax_isIdent(v_t_307_);
v___x_320_ = lean_box(v___x_319_);
v___y_321_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___boxed), 13, 4);
lean_closure_set(v___y_321_, 0, v___x_320_);
lean_closure_set(v___y_321_, 1, v_t_307_);
lean_closure_set(v___y_321_, 2, v_error_318_);
lean_closure_set(v___y_321_, 3, v_loc_308_);
v___x_322_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___y_321_, v_a_309_, v_a_310_, v_a_311_, v_a_312_, v_a_313_, v_a_314_, v_a_315_, v_a_316_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___boxed(lean_object* v_t_323_, lean_object* v_loc_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported(v_t_323_, v_loc_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_);
lean_dec(v_a_332_);
lean_dec_ref(v_a_331_);
lean_dec(v_a_330_);
lean_dec_ref(v_a_329_);
lean_dec(v_a_328_);
lean_dec_ref(v_a_327_);
lean_dec(v_a_326_);
lean_dec_ref(v_a_325_);
return v_res_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0(lean_object* v_00_u03b1_335_, lean_object* v_ref_336_, lean_object* v_msg_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_){
_start:
{
lean_object* v___x_347_; 
v___x_347_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0___redArg(v_ref_336_, v_msg_337_, v___y_338_, v___y_339_, v___y_340_, v___y_341_, v___y_342_, v___y_343_, v___y_344_, v___y_345_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0___boxed(lean_object* v_00_u03b1_348_, lean_object* v_ref_349_, lean_object* v_msg_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_){
_start:
{
lean_object* v_res_360_; 
v_res_360_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0(v_00_u03b1_348_, v_ref_349_, v_msg_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_);
lean_dec(v___y_358_);
lean_dec_ref(v___y_357_);
lean_dec(v___y_356_);
lean_dec_ref(v___y_355_);
lean_dec(v___y_354_);
lean_dec_ref(v___y_353_);
lean_dec(v___y_352_);
lean_dec_ref(v___y_351_);
lean_dec(v_ref_349_);
return v_res_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0_spec__0(lean_object* v_00_u03b1_361_, lean_object* v_msg_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_){
_start:
{
lean_object* v___x_372_; 
v___x_372_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0_spec__0___redArg(v_msg_362_, v___y_367_, v___y_368_, v___y_369_, v___y_370_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0_spec__0___boxed(lean_object* v_00_u03b1_373_, lean_object* v_msg_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0_spec__0(v_00_u03b1_373_, v_msg_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_);
lean_dec(v___y_382_);
lean_dec_ref(v___y_381_);
lean_dec(v___y_380_);
lean_dec_ref(v___y_379_);
lean_dec(v___y_378_);
lean_dec_ref(v___y_377_);
lean_dec(v___y_376_);
lean_dec_ref(v___y_375_);
return v_res_384_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__0___closed__1(void){
_start:
{
lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_386_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__0___closed__0));
v___x_387_ = l_Lean_stringToMessageData(v___x_386_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__0(lean_object* v_a_388_, lean_object* v_a_389_){
_start:
{
if (lean_obj_tag(v_a_388_) == 0)
{
lean_object* v___x_390_; 
v___x_390_ = l_List_reverse___redArg(v_a_389_);
return v___x_390_;
}
else
{
lean_object* v_head_391_; lean_object* v_tail_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_404_; 
v_head_391_ = lean_ctor_get(v_a_388_, 0);
v_tail_392_ = lean_ctor_get(v_a_388_, 1);
v_isSharedCheck_404_ = !lean_is_exclusive(v_a_388_);
if (v_isSharedCheck_404_ == 0)
{
v___x_394_ = v_a_388_;
v_isShared_395_ = v_isSharedCheck_404_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_tail_392_);
lean_inc(v_head_391_);
lean_dec(v_a_388_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_404_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_401_; 
v___x_396_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__0___closed__1, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__0___closed__1_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__0___closed__1);
v___x_397_ = l_Lean_MessageData_ofSyntax(v_head_391_);
v___x_398_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_398_, 0, v___x_396_);
lean_ctor_set(v___x_398_, 1, v___x_397_);
v___x_399_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_399_, 0, v___x_398_);
lean_ctor_set(v___x_399_, 1, v___x_396_);
if (v_isShared_395_ == 0)
{
lean_ctor_set(v___x_394_, 1, v_a_389_);
lean_ctor_set(v___x_394_, 0, v___x_399_);
v___x_401_ = v___x_394_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v___x_399_);
lean_ctor_set(v_reuseFailAlloc_403_, 1, v_a_389_);
v___x_401_ = v_reuseFailAlloc_403_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
v_a_388_ = v_tail_392_;
v_a_389_ = v___x_401_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1_spec__1___redArg(lean_object* v_msg_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_){
_start:
{
lean_object* v_ref_411_; lean_object* v___x_412_; lean_object* v_a_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_421_; 
v_ref_411_ = lean_ctor_get(v___y_408_, 2);
v___x_412_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported_spec__0_spec__0_spec__1(v_msg_405_, v___y_406_, v___y_407_, v___y_408_, v___y_409_);
v_a_413_ = lean_ctor_get(v___x_412_, 0);
v_isSharedCheck_421_ = !lean_is_exclusive(v___x_412_);
if (v_isSharedCheck_421_ == 0)
{
v___x_415_ = v___x_412_;
v_isShared_416_ = v_isSharedCheck_421_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_a_413_);
lean_dec(v___x_412_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_421_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
lean_object* v___x_417_; lean_object* v___x_419_; 
lean_inc(v_ref_411_);
v___x_417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_417_, 0, v_ref_411_);
lean_ctor_set(v___x_417_, 1, v_a_413_);
if (v_isShared_416_ == 0)
{
lean_ctor_set_tag(v___x_415_, 1);
lean_ctor_set(v___x_415_, 0, v___x_417_);
v___x_419_ = v___x_415_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v___x_417_);
v___x_419_ = v_reuseFailAlloc_420_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
return v___x_419_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1_spec__1___redArg___boxed(lean_object* v_msg_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1_spec__1___redArg(v_msg_422_, v___y_423_, v___y_424_, v___y_425_, v___y_426_);
lean_dec(v___y_426_);
lean_dec_ref(v___y_425_);
lean_dec(v___y_424_);
lean_dec_ref(v___y_423_);
return v_res_428_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1___redArg(lean_object* v_ref_429_, lean_object* v_msg_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_){
_start:
{
lean_object* v_toCold_436_; lean_object* v_currRecDepth_437_; lean_object* v_ref_438_; uint16_t v_optionFlags_439_; uint8_t v_suppressElabErrors_440_; uint8_t v_isRecordingDeps_441_; lean_object* v_ref_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
v_toCold_436_ = lean_ctor_get(v___y_433_, 0);
v_currRecDepth_437_ = lean_ctor_get(v___y_433_, 1);
v_ref_438_ = lean_ctor_get(v___y_433_, 2);
v_optionFlags_439_ = lean_ctor_get_uint16(v___y_433_, sizeof(void*)*3);
v_suppressElabErrors_440_ = lean_ctor_get_uint8(v___y_433_, sizeof(void*)*3 + 2);
v_isRecordingDeps_441_ = lean_ctor_get_uint8(v___y_433_, sizeof(void*)*3 + 3);
v_ref_442_ = l_Lean_replaceRef(v_ref_429_, v_ref_438_);
lean_inc(v_currRecDepth_437_);
lean_inc_ref(v_toCold_436_);
v___x_443_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_443_, 0, v_toCold_436_);
lean_ctor_set(v___x_443_, 1, v_currRecDepth_437_);
lean_ctor_set(v___x_443_, 2, v_ref_442_);
lean_ctor_set_uint16(v___x_443_, sizeof(void*)*3, v_optionFlags_439_);
lean_ctor_set_uint8(v___x_443_, sizeof(void*)*3 + 2, v_suppressElabErrors_440_);
lean_ctor_set_uint8(v___x_443_, sizeof(void*)*3 + 3, v_isRecordingDeps_441_);
v___x_444_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1_spec__1___redArg(v_msg_430_, v___y_431_, v___y_432_, v___x_443_, v___y_434_);
lean_dec_ref_known(v___x_443_, 3);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1___redArg___boxed(lean_object* v_ref_445_, lean_object* v_msg_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_){
_start:
{
lean_object* v_res_452_; 
v_res_452_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1___redArg(v_ref_445_, v_msg_446_, v___y_447_, v___y_448_, v___y_449_, v___y_450_);
lean_dec(v___y_450_);
lean_dec_ref(v___y_449_);
lean_dec(v___y_448_);
lean_dec_ref(v___y_447_);
lean_dec(v_ref_445_);
return v_res_452_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__1(void){
_start:
{
lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_454_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__0));
v___x_455_ = l_Lean_stringToMessageData(v___x_454_);
return v___x_455_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__3(void){
_start:
{
lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_457_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__2));
v___x_458_ = l_Lean_stringToMessageData(v___x_457_);
return v___x_458_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__5(void){
_start:
{
lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_460_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__4));
v___x_461_ = l_Lean_stringToMessageData(v___x_460_);
return v___x_461_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__6(void){
_start:
{
lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_462_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__5, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__5);
v___x_463_ = l_Lean_MessageData_hint_x27(v___x_462_);
return v___x_463_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__8(void){
_start:
{
lean_object* v___x_465_; lean_object* v___x_466_; 
v___x_465_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__7));
v___x_466_ = l_Lean_stringToMessageData(v___x_465_);
return v___x_466_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__10(void){
_start:
{
lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_468_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__9));
v___x_469_ = l_Lean_stringToMessageData(v___x_468_);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg(lean_object* v_stx_472_, uint8_t v_simplifyTarget_473_, lean_object* v_hyps_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_){
_start:
{
lean_object* v___y_481_; lean_object* v___y_482_; lean_object* v___y_499_; 
if (v_simplifyTarget_473_ == 0)
{
lean_object* v___x_505_; 
v___x_505_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__11));
v___y_499_ = v___x_505_;
goto v___jp_498_;
}
else
{
lean_object* v___x_506_; 
v___x_506_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__12));
v___y_499_ = v___x_506_;
goto v___jp_498_;
}
v___jp_480_:
{
lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v_hypsStr_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_483_ = lean_array_to_list(v_hyps_474_);
v___x_484_ = lean_box(0);
v___x_485_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__0(v___x_483_, v___x_484_);
v___x_486_ = l_Lean_MessageData_andList(v___x_485_);
lean_inc_ref(v___y_482_);
v_hypsStr_487_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_hypsStr_487_, 0, v___y_482_);
lean_ctor_set(v_hypsStr_487_, 1, v___x_486_);
v___x_488_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__1, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__1_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__1);
lean_inc_ref(v___y_481_);
v___x_489_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_489_, 0, v___y_481_);
v___x_490_ = l_Lean_MessageData_ofFormat(v___x_489_);
v___x_491_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_491_, 0, v___x_490_);
lean_ctor_set(v___x_491_, 1, v_hypsStr_487_);
v___x_492_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_492_, 0, v___x_488_);
lean_ctor_set(v___x_492_, 1, v___x_491_);
v___x_493_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__3, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__3_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__3);
v___x_494_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_494_, 0, v___x_492_);
lean_ctor_set(v___x_494_, 1, v___x_493_);
v___x_495_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__6, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__6_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__6);
v___x_496_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_496_, 0, v___x_494_);
lean_ctor_set(v___x_496_, 1, v___x_495_);
v___x_497_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1___redArg(v_stx_472_, v___x_496_, v_a_475_, v_a_476_, v_a_477_, v_a_478_);
return v___x_497_;
}
v___jp_498_:
{
lean_object* v___x_500_; lean_object* v___x_501_; uint8_t v___x_502_; 
v___x_500_ = lean_array_get_size(v_hyps_474_);
v___x_501_ = lean_unsigned_to_nat(1u);
v___x_502_ = lean_nat_dec_eq(v___x_500_, v___x_501_);
if (v___x_502_ == 0)
{
lean_object* v___x_503_; 
v___x_503_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__8, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__8_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__8);
v___y_481_ = v___y_499_;
v___y_482_ = v___x_503_;
goto v___jp_480_;
}
else
{
lean_object* v___x_504_; 
v___x_504_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__10, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__10_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___closed__10);
v___y_481_ = v___y_499_;
v___y_482_ = v___x_504_;
goto v___jp_480_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg___boxed(lean_object* v_stx_507_, lean_object* v_simplifyTarget_508_, lean_object* v_hyps_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_){
_start:
{
uint8_t v_simplifyTarget_boxed_515_; lean_object* v_res_516_; 
v_simplifyTarget_boxed_515_ = lean_unbox(v_simplifyTarget_508_);
v_res_516_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg(v_stx_507_, v_simplifyTarget_boxed_515_, v_hyps_509_, v_a_510_, v_a_511_, v_a_512_, v_a_513_);
lean_dec(v_a_513_);
lean_dec_ref(v_a_512_);
lean_dec(v_a_511_);
lean_dec_ref(v_a_510_);
lean_dec(v_stx_507_);
return v_res_516_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt(lean_object* v_stx_517_, uint8_t v_simplifyTarget_518_, lean_object* v_hyps_519_, lean_object* v_00_u03b1_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_){
_start:
{
lean_object* v___x_526_; 
v___x_526_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg(v_stx_517_, v_simplifyTarget_518_, v_hyps_519_, v_a_521_, v_a_522_, v_a_523_, v_a_524_);
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___boxed(lean_object* v_stx_527_, lean_object* v_simplifyTarget_528_, lean_object* v_hyps_529_, lean_object* v_00_u03b1_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_){
_start:
{
uint8_t v_simplifyTarget_boxed_536_; lean_object* v_res_537_; 
v_simplifyTarget_boxed_536_ = lean_unbox(v_simplifyTarget_528_);
v_res_537_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt(v_stx_527_, v_simplifyTarget_boxed_536_, v_hyps_529_, v_00_u03b1_530_, v_a_531_, v_a_532_, v_a_533_, v_a_534_);
lean_dec(v_a_534_);
lean_dec_ref(v_a_533_);
lean_dec(v_a_532_);
lean_dec_ref(v_a_531_);
lean_dec(v_stx_527_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1(lean_object* v_00_u03b1_538_, lean_object* v_ref_539_, lean_object* v_msg_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_){
_start:
{
lean_object* v___x_546_; 
v___x_546_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1___redArg(v_ref_539_, v_msg_540_, v___y_541_, v___y_542_, v___y_543_, v___y_544_);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1___boxed(lean_object* v_00_u03b1_547_, lean_object* v_ref_548_, lean_object* v_msg_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_){
_start:
{
lean_object* v_res_555_; 
v_res_555_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1(v_00_u03b1_547_, v_ref_548_, v_msg_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_);
lean_dec(v___y_553_);
lean_dec_ref(v___y_552_);
lean_dec(v___y_551_);
lean_dec_ref(v___y_550_);
lean_dec(v_ref_548_);
return v_res_555_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1_spec__1(lean_object* v_00_u03b1_556_, lean_object* v_msg_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_){
_start:
{
lean_object* v___x_563_; 
v___x_563_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1_spec__1___redArg(v_msg_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_);
return v___x_563_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1_spec__1___boxed(lean_object* v_00_u03b1_564_, lean_object* v_msg_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_){
_start:
{
lean_object* v_res_571_; 
v_res_571_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__1_spec__1(v_00_u03b1_564_, v_msg_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_);
lean_dec(v___y_569_);
lean_dec_ref(v___y_568_);
lean_dec(v___y_567_);
lean_dec_ref(v___y_566_);
return v_res_571_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__1(void){
_start:
{
lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_573_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__0));
v___x_574_ = l_Lean_stringToMessageData(v___x_573_);
return v___x_574_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__3(void){
_start:
{
lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_576_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__2));
v___x_577_ = l_Lean_stringToMessageData(v___x_576_);
return v___x_577_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0(lean_object* v_type_587_, lean_object* v___x_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_){
_start:
{
lean_object* v_val_595_; uint8_t v_a_604_; lean_object* v___x_614_; 
v___x_614_ = l_Lean_Expr_getAppFn(v___x_588_);
if (lean_obj_tag(v___x_614_) == 4)
{
lean_object* v_declName_615_; lean_object* v___x_616_; lean_object* v_env_617_; uint8_t v___x_618_; 
v_declName_615_ = lean_ctor_get(v___x_614_, 0);
lean_inc_n(v_declName_615_, 2);
lean_dec_ref_known(v___x_614_, 2);
v___x_616_ = lean_st_ref_get(v___y_592_);
v_env_617_ = lean_ctor_get(v___x_616_, 0);
lean_inc_ref_n(v_env_617_, 2);
lean_dec(v___x_616_);
v___x_618_ = l_Lean_isStructure(v_env_617_, v_declName_615_);
if (v___x_618_ == 0)
{
lean_dec_ref(v_env_617_);
lean_dec(v_declName_615_);
v_a_604_ = v___x_618_;
goto v___jp_603_;
}
else
{
lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; uint8_t v___x_622_; 
v___x_619_ = lean_unsigned_to_nat(0u);
v___x_620_ = l_Lean_getStructureFields(v_env_617_, v_declName_615_);
v___x_621_ = lean_array_get_size(v___x_620_);
lean_dec_ref(v___x_620_);
v___x_622_ = lean_nat_dec_lt(v___x_619_, v___x_621_);
v_a_604_ = v___x_622_;
goto v___jp_603_;
}
}
else
{
uint8_t v___x_623_; 
lean_dec_ref(v___x_614_);
v___x_623_ = 0;
v_a_604_ = v___x_623_;
goto v___jp_603_;
}
v___jp_594_:
{
lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
v___x_596_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__1, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__1);
lean_inc_ref(v_val_595_);
v___x_597_ = l_Lean_stringToMessageData(v_val_595_);
v___x_598_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_598_, 0, v___x_596_);
lean_ctor_set(v___x_598_, 1, v___x_597_);
v___x_599_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__3, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__3_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__3);
v___x_600_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_600_, 0, v___x_598_);
lean_ctor_set(v___x_600_, 1, v___x_599_);
v___x_601_ = l_Lean_MessageData_hint_x27(v___x_600_);
v___x_602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_602_, 0, v___x_601_);
return v___x_602_;
}
v___jp_603_:
{
lean_object* v___x_605_; uint8_t v___x_606_; 
v___x_605_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__5));
v___x_606_ = l_Lean_Expr_isAppOf(v_type_587_, v___x_605_);
if (v___x_606_ == 0)
{
lean_object* v___x_607_; uint8_t v___x_608_; 
v___x_607_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__7));
v___x_608_ = l_Lean_Expr_isAppOf(v_type_587_, v___x_607_);
if (v___x_608_ == 0)
{
if (v_a_604_ == 0)
{
lean_object* v___x_609_; lean_object* v___x_610_; 
v___x_609_ = l_Lean_MessageData_nil;
v___x_610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_610_, 0, v___x_609_);
return v___x_610_;
}
else
{
lean_object* v___x_611_; 
v___x_611_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__8));
v_val_595_ = v___x_611_;
goto v___jp_594_;
}
}
else
{
lean_object* v___x_612_; 
v___x_612_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__9));
v_val_595_ = v___x_612_;
goto v___jp_594_;
}
}
else
{
lean_object* v___x_613_; 
v___x_613_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___closed__10));
v_val_595_ = v___x_613_;
goto v___jp_594_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___boxed(lean_object* v_type_624_, lean_object* v___x_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_){
_start:
{
lean_object* v_res_631_; 
v_res_631_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0(v_type_624_, v___x_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_);
lean_dec(v___y_629_);
lean_dec_ref(v___y_628_);
lean_dec(v___y_627_);
lean_dec_ref(v___y_626_);
lean_dec_ref(v___x_625_);
lean_dec_ref(v_type_624_);
return v_res_631_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint(lean_object* v_type_632_){
_start:
{
lean_object* v___x_633_; lean_object* v___f_634_; lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_633_ = l_Lean_Expr_getAppFn(v_type_632_);
v___f_634_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint___lam__0___boxed), 7, 2);
lean_closure_set(v___f_634_, 0, v_type_632_);
lean_closure_set(v___f_634_, 1, v___x_633_);
v___x_635_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint___closed__5));
v___x_636_ = l_Lean_MessageData_ofLazyM(v___f_634_, v___x_635_);
return v___x_636_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal___closed__2(void){
_start:
{
lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_640_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal___closed__1));
v___x_641_ = l_Lean_stringToMessageData(v___x_640_);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal(lean_object* v_mvarId_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_){
_start:
{
lean_object* v___x_648_; 
lean_inc(v_mvarId_642_);
v___x_648_ = l_Lean_MVarId_getType(v_mvarId_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_);
if (lean_obj_tag(v___x_648_) == 0)
{
lean_object* v_a_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; 
v_a_649_ = lean_ctor_get(v___x_648_, 0);
lean_inc(v_a_649_);
lean_dec_ref_known(v___x_648_, 1);
v___x_650_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint(v_a_649_);
v___x_651_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal___closed__0));
v___x_652_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal___closed__2, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal___closed__2_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal___closed__2);
v___x_653_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_653_, 0, v___x_652_);
lean_ctor_set(v___x_653_, 1, v___x_650_);
v___x_654_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint;
v___x_655_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_655_, 0, v___x_653_);
lean_ctor_set(v___x_655_, 1, v___x_654_);
v___x_656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_656_, 0, v___x_655_);
v___x_657_ = l_Lean_Meta_throwTacticEx___redArg(v___x_651_, v_mvarId_642_, v___x_656_, v_a_643_, v_a_644_, v_a_645_, v_a_646_);
return v___x_657_;
}
else
{
lean_object* v_a_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_665_; 
lean_dec(v_mvarId_642_);
v_a_658_ = lean_ctor_get(v___x_648_, 0);
v_isSharedCheck_665_ = !lean_is_exclusive(v___x_648_);
if (v_isSharedCheck_665_ == 0)
{
v___x_660_ = v___x_648_;
v_isShared_661_ = v_isSharedCheck_665_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_a_658_);
lean_dec(v___x_648_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_665_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v___x_663_; 
if (v_isShared_661_ == 0)
{
v___x_663_ = v___x_660_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v_a_658_);
v___x_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
return v___x_663_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal___boxed(lean_object* v_mvarId_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_){
_start:
{
lean_object* v_res_672_; 
v_res_672_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal(v_mvarId_666_, v_a_667_, v_a_668_, v_a_669_, v_a_670_);
lean_dec(v_a_670_);
lean_dec_ref(v_a_669_);
lean_dec(v_a_668_);
lean_dec_ref(v_a_667_);
return v_res_672_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp___closed__1(void){
_start:
{
lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_674_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp___closed__0));
v___x_675_ = l_Lean_stringToMessageData(v___x_674_);
return v___x_675_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp___closed__3(void){
_start:
{
lean_object* v___x_677_; lean_object* v___x_678_; 
v___x_677_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp___closed__2));
v___x_678_ = l_Lean_stringToMessageData(v___x_677_);
return v___x_678_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp(lean_object* v_fvarId_679_, lean_object* v_mvarId_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_){
_start:
{
lean_object* v___x_686_; 
lean_inc(v_fvarId_679_);
v___x_686_ = l_Lean_FVarId_getType___redArg(v_fvarId_679_, v_a_681_, v_a_683_, v_a_684_);
if (lean_obj_tag(v___x_686_) == 0)
{
lean_object* v_a_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; 
v_a_687_ = lean_ctor_get(v___x_686_, 0);
lean_inc_n(v_a_687_, 2);
lean_dec_ref_known(v___x_686_, 1);
v___x_688_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal___closed__0));
v___x_689_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp___closed__1, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp___closed__1_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp___closed__1);
v___x_690_ = lean_unsigned_to_nat(30u);
v___x_691_ = l_Lean_inlineExpr(v_a_687_, v___x_690_);
v___x_692_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_692_, 0, v___x_689_);
lean_ctor_set(v___x_692_, 1, v___x_691_);
v___x_693_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp___closed__3, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp___closed__3_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp___closed__3);
v___x_694_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_694_, 0, v___x_692_);
lean_ctor_set(v___x_694_, 1, v___x_693_);
v___x_695_ = l_Lean_Expr_fvar___override(v_fvarId_679_);
v___x_696_ = l_Lean_MessageData_ofExpr(v___x_695_);
v___x_697_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_697_, 0, v___x_694_);
lean_ctor_set(v___x_697_, 1, v___x_696_);
v___x_698_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__0___closed__1, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__0___closed__1_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__0___closed__1);
v___x_699_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_699_, 0, v___x_697_);
lean_ctor_set(v___x_699_, 1, v___x_698_);
v___x_700_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_mkCasesHint(v_a_687_);
v___x_701_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_701_, 0, v___x_699_);
lean_ctor_set(v___x_701_, 1, v___x_700_);
v___x_702_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint;
v___x_703_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_703_, 0, v___x_701_);
lean_ctor_set(v___x_703_, 1, v___x_702_);
v___x_704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_704_, 0, v___x_703_);
v___x_705_ = l_Lean_Meta_throwTacticEx___redArg(v___x_688_, v_mvarId_680_, v___x_704_, v_a_681_, v_a_682_, v_a_683_, v_a_684_);
return v___x_705_;
}
else
{
lean_object* v_a_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_713_; 
lean_dec(v_mvarId_680_);
lean_dec(v_fvarId_679_);
v_a_706_ = lean_ctor_get(v___x_686_, 0);
v_isSharedCheck_713_ = !lean_is_exclusive(v___x_686_);
if (v_isSharedCheck_713_ == 0)
{
v___x_708_ = v___x_686_;
v_isShared_709_ = v_isSharedCheck_713_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_a_706_);
lean_dec(v___x_686_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_713_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v___x_711_; 
if (v_isShared_709_ == 0)
{
v___x_711_ = v___x_708_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v_a_706_);
v___x_711_ = v_reuseFailAlloc_712_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
return v___x_711_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp___boxed(lean_object* v_fvarId_714_, lean_object* v_mvarId_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_){
_start:
{
lean_object* v_res_721_; 
v_res_721_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp(v_fvarId_714_, v_mvarId_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_);
lean_dec(v_a_719_);
lean_dec_ref(v_a_718_);
lean_dec(v_a_717_);
lean_dec_ref(v_a_716_);
return v_res_721_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard_spec__0(lean_object* v_a_722_, lean_object* v_a_723_){
_start:
{
if (lean_obj_tag(v_a_722_) == 0)
{
lean_object* v___x_724_; 
v___x_724_ = l_List_reverse___redArg(v_a_723_);
return v___x_724_;
}
else
{
lean_object* v_head_725_; lean_object* v_tail_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_739_; 
v_head_725_ = lean_ctor_get(v_a_722_, 0);
v_tail_726_ = lean_ctor_get(v_a_722_, 1);
v_isSharedCheck_739_ = !lean_is_exclusive(v_a_722_);
if (v_isSharedCheck_739_ == 0)
{
v___x_728_ = v_a_722_;
v_isShared_729_ = v_isSharedCheck_739_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_tail_726_);
lean_inc(v_head_725_);
lean_dec(v_a_722_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_739_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_736_; 
v___x_730_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__0___closed__1, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__0___closed__1_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt_spec__0___closed__1);
v___x_731_ = l_Lean_Expr_fvar___override(v_head_725_);
v___x_732_ = l_Lean_MessageData_ofExpr(v___x_731_);
v___x_733_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_733_, 0, v___x_730_);
lean_ctor_set(v___x_733_, 1, v___x_732_);
v___x_734_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_734_, 0, v___x_733_);
lean_ctor_set(v___x_734_, 1, v___x_730_);
if (v_isShared_729_ == 0)
{
lean_ctor_set(v___x_728_, 1, v_a_723_);
lean_ctor_set(v___x_728_, 0, v___x_734_);
v___x_736_ = v___x_728_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v___x_734_);
lean_ctor_set(v_reuseFailAlloc_738_, 1, v_a_723_);
v___x_736_ = v_reuseFailAlloc_738_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
v_a_722_ = v_tail_726_;
v_a_723_ = v___x_736_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__2(void){
_start:
{
lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_743_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__1));
v___x_744_ = l_Lean_MessageData_ofFormat(v___x_743_);
return v___x_744_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__3(void){
_start:
{
lean_object* v___x_745_; lean_object* v_note_746_; 
v___x_745_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__2, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__2_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__2);
v_note_746_ = l_Lean_MessageData_note(v___x_745_);
return v_note_746_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__5(void){
_start:
{
lean_object* v___x_748_; lean_object* v___x_749_; 
v___x_748_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__4));
v___x_749_ = l_Lean_stringToMessageData(v___x_748_);
return v___x_749_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__6(void){
_start:
{
lean_object* v_note_750_; lean_object* v___x_751_; lean_object* v___x_752_; 
v_note_750_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__3, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__3_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__3);
v___x_751_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__5, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__5);
v___x_752_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_752_, 0, v___x_751_);
lean_ctor_set(v___x_752_, 1, v_note_750_);
return v___x_752_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__7(void){
_start:
{
lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_753_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint;
v___x_754_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__6, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__6_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__6);
v___x_755_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_755_, 0, v___x_754_);
lean_ctor_set(v___x_755_, 1, v___x_753_);
return v___x_755_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__8(void){
_start:
{
lean_object* v___x_756_; lean_object* v___x_757_; 
v___x_756_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__7, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__7_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__7);
v___x_757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_757_, 0, v___x_756_);
return v___x_757_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__11(void){
_start:
{
lean_object* v___x_761_; lean_object* v___x_762_; 
v___x_761_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__10));
v___x_762_ = l_Lean_MessageData_ofFormat(v___x_761_);
return v___x_762_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__13(void){
_start:
{
lean_object* v___x_764_; lean_object* v___x_765_; 
v___x_764_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__12));
v___x_765_ = l_Lean_stringToMessageData(v___x_764_);
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg(lean_object* v_fvarIds_766_, lean_object* v_mvarId_767_, lean_object* v_a_768_, lean_object* v_a_769_, lean_object* v_a_770_, lean_object* v_a_771_){
_start:
{
lean_object* v_note_773_; lean_object* v___x_774_; lean_object* v___x_775_; uint8_t v___x_776_; 
v_note_773_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__3, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__3_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__3);
v___x_774_ = lean_unsigned_to_nat(0u);
v___x_775_ = lean_array_get_size(v_fvarIds_766_);
v___x_776_ = lean_nat_dec_lt(v___x_774_, v___x_775_);
if (v___x_776_ == 0)
{
lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; 
lean_dec_ref(v_fvarIds_766_);
v___x_777_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal___closed__0));
v___x_778_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__8, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__8_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__8);
v___x_779_ = l_Lean_Meta_throwTacticEx___redArg(v___x_777_, v_mvarId_767_, v___x_778_, v_a_768_, v_a_769_, v_a_770_, v_a_771_);
return v___x_779_;
}
else
{
lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v_fvarMsgs_782_; lean_object* v___x_783_; lean_object* v_fvarMsgs_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; 
v___x_780_ = lean_array_to_list(v_fvarIds_766_);
v___x_781_ = lean_box(0);
v_fvarMsgs_782_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard_spec__0(v___x_780_, v___x_781_);
v___x_783_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__11, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__11_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__11);
v_fvarMsgs_784_ = l_Lean_MessageData_joinSep(v_fvarMsgs_782_, v___x_783_);
v___x_785_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal___closed__0));
v___x_786_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__13, &l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__13_once, _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___closed__13);
v___x_787_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_787_, 0, v___x_786_);
lean_ctor_set(v___x_787_, 1, v_fvarMsgs_784_);
v___x_788_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_788_, 0, v___x_787_);
lean_ctor_set(v___x_788_, 1, v_note_773_);
v___x_789_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint;
v___x_790_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_790_, 0, v___x_788_);
lean_ctor_set(v___x_790_, 1, v___x_789_);
v___x_791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_791_, 0, v___x_790_);
v___x_792_ = l_Lean_Meta_throwTacticEx___redArg(v___x_785_, v_mvarId_767_, v___x_791_, v_a_768_, v_a_769_, v_a_770_, v_a_771_);
return v___x_792_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg___boxed(lean_object* v_fvarIds_793_, lean_object* v_mvarId_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_){
_start:
{
lean_object* v_res_800_; 
v_res_800_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg(v_fvarIds_793_, v_mvarId_794_, v_a_795_, v_a_796_, v_a_797_, v_a_798_);
lean_dec(v_a_798_);
lean_dec_ref(v_a_797_);
lean_dec(v_a_796_);
lean_dec_ref(v_a_795_);
return v_res_800_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard(lean_object* v_00_u03b1_801_, lean_object* v_fvarIds_802_, lean_object* v_mvarId_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v_a_807_){
_start:
{
lean_object* v___x_809_; 
v___x_809_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg(v_fvarIds_802_, v_mvarId_803_, v_a_804_, v_a_805_, v_a_806_, v_a_807_);
return v___x_809_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___boxed(lean_object* v_00_u03b1_810_, lean_object* v_fvarIds_811_, lean_object* v_mvarId_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_){
_start:
{
lean_object* v_res_818_; 
v_res_818_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard(v_00_u03b1_810_, v_fvarIds_811_, v_mvarId_812_, v_a_813_, v_a_814_, v_a_815_, v_a_816_);
lean_dec(v_a_816_);
lean_dec_ref(v_a_815_);
lean_dec(v_a_814_);
lean_dec_ref(v_a_813_);
return v_res_818_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSplit_spec__0(lean_object* v_a_822_, lean_object* v_as_823_, size_t v_sz_824_, size_t v_i_825_, lean_object* v_b_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_){
_start:
{
uint8_t v___x_832_; 
v___x_832_ = lean_usize_dec_lt(v_i_825_, v_sz_824_);
if (v___x_832_ == 0)
{
lean_object* v___x_833_; 
lean_dec(v_a_822_);
v___x_833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_833_, 0, v_b_826_);
return v___x_833_;
}
else
{
lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v_a_836_; lean_object* v___x_837_; 
lean_dec_ref(v_b_826_);
v___x_834_ = lean_box(0);
v___x_835_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSplit_spec__0___closed__0));
v_a_836_ = lean_array_uget_borrowed(v_as_823_, v_i_825_);
lean_inc(v_a_836_);
lean_inc(v_a_822_);
v___x_837_ = l_Lean_Meta_splitLocalDecl_x3f(v_a_822_, v_a_836_, v___y_827_, v___y_828_, v___y_829_, v___y_830_);
if (lean_obj_tag(v___x_837_) == 0)
{
lean_object* v_a_838_; lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_849_; 
v_a_838_ = lean_ctor_get(v___x_837_, 0);
v_isSharedCheck_849_ = !lean_is_exclusive(v___x_837_);
if (v_isSharedCheck_849_ == 0)
{
v___x_840_ = v___x_837_;
v_isShared_841_ = v_isSharedCheck_849_;
goto v_resetjp_839_;
}
else
{
lean_inc(v_a_838_);
lean_dec(v___x_837_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_849_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
if (lean_obj_tag(v_a_838_) == 1)
{
lean_object* v___x_842_; lean_object* v___x_844_; 
lean_dec(v_a_822_);
v___x_842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_842_, 0, v_a_838_);
lean_ctor_set(v___x_842_, 1, v___x_834_);
if (v_isShared_841_ == 0)
{
lean_ctor_set(v___x_840_, 0, v___x_842_);
v___x_844_ = v___x_840_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v___x_842_);
v___x_844_ = v_reuseFailAlloc_845_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
return v___x_844_;
}
}
else
{
size_t v___x_846_; size_t v___x_847_; 
lean_del_object(v___x_840_);
lean_dec(v_a_838_);
v___x_846_ = ((size_t)1ULL);
v___x_847_ = lean_usize_add(v_i_825_, v___x_846_);
v_i_825_ = v___x_847_;
v_b_826_ = v___x_835_;
goto _start;
}
}
}
else
{
lean_object* v_a_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_857_; 
lean_dec(v_a_822_);
v_a_850_ = lean_ctor_get(v___x_837_, 0);
v_isSharedCheck_857_ = !lean_is_exclusive(v___x_837_);
if (v_isSharedCheck_857_ == 0)
{
v___x_852_ = v___x_837_;
v_isShared_853_ = v_isSharedCheck_857_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_a_850_);
lean_dec(v___x_837_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_857_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v___x_855_; 
if (v_isShared_853_ == 0)
{
v___x_855_ = v___x_852_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v_a_850_);
v___x_855_ = v_reuseFailAlloc_856_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
return v___x_855_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSplit_spec__0___boxed(lean_object* v_a_858_, lean_object* v_as_859_, lean_object* v_sz_860_, lean_object* v_i_861_, lean_object* v_b_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_){
_start:
{
size_t v_sz_boxed_868_; size_t v_i_boxed_869_; lean_object* v_res_870_; 
v_sz_boxed_868_ = lean_unbox_usize(v_sz_860_);
lean_dec(v_sz_860_);
v_i_boxed_869_ = lean_unbox_usize(v_i_861_);
lean_dec(v_i_861_);
v_res_870_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSplit_spec__0(v_a_858_, v_as_859_, v_sz_boxed_868_, v_i_boxed_869_, v_b_862_, v___y_863_, v___y_864_, v___y_865_, v___y_866_);
lean_dec(v___y_866_);
lean_dec_ref(v___y_865_);
lean_dec(v___y_864_);
lean_dec_ref(v___y_863_);
lean_dec_ref(v_as_859_);
return v_res_870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSplit___lam__0(lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_){
_start:
{
lean_object* v_a_881_; lean_object* v___x_892_; 
v___x_892_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_872_, v___y_875_, v___y_876_, v___y_877_, v___y_878_);
if (lean_obj_tag(v___x_892_) == 0)
{
lean_object* v_a_893_; lean_object* v___x_894_; 
v_a_893_ = lean_ctor_get(v___x_892_, 0);
lean_inc_n(v_a_893_, 2);
lean_dec_ref_known(v___x_892_, 1);
v___x_894_ = l_Lean_MVarId_getNondepPropHyps(v_a_893_, v___y_875_, v___y_876_, v___y_877_, v___y_878_);
if (lean_obj_tag(v___x_894_) == 0)
{
lean_object* v_a_895_; lean_object* v___x_896_; size_t v_sz_897_; size_t v___x_898_; lean_object* v___x_899_; 
v_a_895_ = lean_ctor_get(v___x_894_, 0);
lean_inc(v_a_895_);
lean_dec_ref_known(v___x_894_, 1);
v___x_896_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSplit_spec__0___closed__0));
v_sz_897_ = lean_array_size(v_a_895_);
v___x_898_ = ((size_t)0ULL);
lean_inc(v_a_893_);
v___x_899_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_evalSplit_spec__0(v_a_893_, v_a_895_, v_sz_897_, v___x_898_, v___x_896_, v___y_875_, v___y_876_, v___y_877_, v___y_878_);
if (lean_obj_tag(v___x_899_) == 0)
{
lean_object* v_a_900_; lean_object* v_fst_901_; 
v_a_900_ = lean_ctor_get(v___x_899_, 0);
lean_inc(v_a_900_);
lean_dec_ref_known(v___x_899_, 1);
v_fst_901_ = lean_ctor_get(v_a_900_, 0);
lean_inc(v_fst_901_);
lean_dec(v_a_900_);
if (lean_obj_tag(v_fst_901_) == 0)
{
uint8_t v___x_902_; uint8_t v___x_903_; lean_object* v___x_904_; 
v___x_902_ = 1;
v___x_903_ = 0;
lean_inc(v_a_893_);
v___x_904_ = l_Lean_Meta_splitTarget_x3f(v_a_893_, v___x_902_, v___x_903_, v___y_875_, v___y_876_, v___y_877_, v___y_878_);
if (lean_obj_tag(v___x_904_) == 0)
{
lean_object* v_a_905_; 
v_a_905_ = lean_ctor_get(v___x_904_, 0);
lean_inc(v_a_905_);
lean_dec_ref_known(v___x_904_, 1);
if (lean_obj_tag(v_a_905_) == 1)
{
lean_object* v_val_906_; 
lean_dec(v_a_895_);
lean_dec(v_a_893_);
v_val_906_ = lean_ctor_get(v_a_905_, 0);
lean_inc(v_val_906_);
lean_dec_ref_known(v_a_905_, 1);
v_a_881_ = v_val_906_;
goto v___jp_880_;
}
else
{
lean_object* v___x_907_; 
lean_dec(v_a_905_);
v___x_907_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitWildcard___redArg(v_a_895_, v_a_893_, v___y_875_, v___y_876_, v___y_877_, v___y_878_);
if (lean_obj_tag(v___x_907_) == 0)
{
lean_object* v_a_908_; 
v_a_908_ = lean_ctor_get(v___x_907_, 0);
lean_inc(v_a_908_);
lean_dec_ref_known(v___x_907_, 1);
v_a_881_ = v_a_908_;
goto v___jp_880_;
}
else
{
lean_object* v_a_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_916_; 
v_a_909_ = lean_ctor_get(v___x_907_, 0);
v_isSharedCheck_916_ = !lean_is_exclusive(v___x_907_);
if (v_isSharedCheck_916_ == 0)
{
v___x_911_ = v___x_907_;
v_isShared_912_ = v_isSharedCheck_916_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_a_909_);
lean_dec(v___x_907_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_916_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
lean_object* v___x_914_; 
if (v_isShared_912_ == 0)
{
v___x_914_ = v___x_911_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v_a_909_);
v___x_914_ = v_reuseFailAlloc_915_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
return v___x_914_;
}
}
}
}
}
else
{
lean_object* v_a_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_924_; 
lean_dec(v_a_895_);
lean_dec(v_a_893_);
v_a_917_ = lean_ctor_get(v___x_904_, 0);
v_isSharedCheck_924_ = !lean_is_exclusive(v___x_904_);
if (v_isSharedCheck_924_ == 0)
{
v___x_919_ = v___x_904_;
v_isShared_920_ = v_isSharedCheck_924_;
goto v_resetjp_918_;
}
else
{
lean_inc(v_a_917_);
lean_dec(v___x_904_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_924_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
lean_object* v___x_922_; 
if (v_isShared_920_ == 0)
{
v___x_922_ = v___x_919_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v_a_917_);
v___x_922_ = v_reuseFailAlloc_923_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
return v___x_922_;
}
}
}
}
else
{
lean_object* v_val_925_; 
lean_dec(v_a_895_);
lean_dec(v_a_893_);
v_val_925_ = lean_ctor_get(v_fst_901_, 0);
lean_inc(v_val_925_);
lean_dec_ref_known(v_fst_901_, 1);
v_a_881_ = v_val_925_;
goto v___jp_880_;
}
}
else
{
lean_object* v_a_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_933_; 
lean_dec(v_a_895_);
lean_dec(v_a_893_);
v_a_926_ = lean_ctor_get(v___x_899_, 0);
v_isSharedCheck_933_ = !lean_is_exclusive(v___x_899_);
if (v_isSharedCheck_933_ == 0)
{
v___x_928_ = v___x_899_;
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_a_926_);
lean_dec(v___x_899_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
lean_object* v___x_931_; 
if (v_isShared_929_ == 0)
{
v___x_931_ = v___x_928_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v_a_926_);
v___x_931_ = v_reuseFailAlloc_932_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
return v___x_931_;
}
}
}
}
else
{
lean_object* v_a_934_; lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_941_; 
lean_dec(v_a_893_);
v_a_934_ = lean_ctor_get(v___x_894_, 0);
v_isSharedCheck_941_ = !lean_is_exclusive(v___x_894_);
if (v_isSharedCheck_941_ == 0)
{
v___x_936_ = v___x_894_;
v_isShared_937_ = v_isSharedCheck_941_;
goto v_resetjp_935_;
}
else
{
lean_inc(v_a_934_);
lean_dec(v___x_894_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_941_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
lean_object* v___x_939_; 
if (v_isShared_937_ == 0)
{
v___x_939_ = v___x_936_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v_a_934_);
v___x_939_ = v_reuseFailAlloc_940_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
return v___x_939_;
}
}
}
}
else
{
lean_object* v_a_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_949_; 
v_a_942_ = lean_ctor_get(v___x_892_, 0);
v_isSharedCheck_949_ = !lean_is_exclusive(v___x_892_);
if (v_isSharedCheck_949_ == 0)
{
v___x_944_ = v___x_892_;
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_a_942_);
lean_dec(v___x_892_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v___x_947_; 
if (v_isShared_945_ == 0)
{
v___x_947_ = v___x_944_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v_a_942_);
v___x_947_ = v_reuseFailAlloc_948_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
return v___x_947_;
}
}
}
v___jp_880_:
{
lean_object* v___x_882_; lean_object* v___x_883_; 
v___x_882_ = lean_box(0);
v___x_883_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v_a_881_, v___y_872_, v___y_875_, v___y_876_, v___y_877_, v___y_878_);
if (lean_obj_tag(v___x_883_) == 0)
{
lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_890_; 
v_isSharedCheck_890_ = !lean_is_exclusive(v___x_883_);
if (v_isSharedCheck_890_ == 0)
{
lean_object* v_unused_891_; 
v_unused_891_ = lean_ctor_get(v___x_883_, 0);
lean_dec(v_unused_891_);
v___x_885_ = v___x_883_;
v_isShared_886_ = v_isSharedCheck_890_;
goto v_resetjp_884_;
}
else
{
lean_dec(v___x_883_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_890_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v___x_888_; 
if (v_isShared_886_ == 0)
{
lean_ctor_set(v___x_885_, 0, v___x_882_);
v___x_888_ = v___x_885_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v___x_882_);
v___x_888_ = v_reuseFailAlloc_889_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
return v___x_888_;
}
}
}
else
{
return v___x_883_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSplit___lam__0___boxed(lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_){
_start:
{
lean_object* v_res_959_; 
v_res_959_ = l_Lean_Elab_Tactic_evalSplit___lam__0(v___y_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_);
lean_dec(v___y_957_);
lean_dec_ref(v___y_956_);
lean_dec(v___y_955_);
lean_dec_ref(v___y_954_);
lean_dec(v___y_953_);
lean_dec_ref(v___y_952_);
lean_dec(v___y_951_);
lean_dec_ref(v___y_950_);
return v_res_959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSplit___lam__1(uint8_t v_type_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_){
_start:
{
lean_object* v_a_971_; lean_object* v___x_982_; 
v___x_982_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_962_, v___y_965_, v___y_966_, v___y_967_, v___y_968_);
if (lean_obj_tag(v___x_982_) == 0)
{
lean_object* v_a_983_; uint8_t v___x_984_; lean_object* v___x_985_; 
v_a_983_ = lean_ctor_get(v___x_982_, 0);
lean_inc_n(v_a_983_, 2);
lean_dec_ref_known(v___x_982_, 1);
v___x_984_ = 0;
v___x_985_ = l_Lean_Meta_splitTarget_x3f(v_a_983_, v_type_960_, v___x_984_, v___y_965_, v___y_966_, v___y_967_, v___y_968_);
if (lean_obj_tag(v___x_985_) == 0)
{
lean_object* v_a_986_; 
v_a_986_ = lean_ctor_get(v___x_985_, 0);
lean_inc(v_a_986_);
lean_dec_ref_known(v___x_985_, 1);
if (lean_obj_tag(v_a_986_) == 1)
{
lean_object* v_val_987_; 
lean_dec(v_a_983_);
v_val_987_ = lean_ctor_get(v_a_986_, 0);
lean_inc(v_val_987_);
lean_dec_ref_known(v_a_986_, 1);
v_a_971_ = v_val_987_;
goto v___jp_970_;
}
else
{
lean_object* v___x_988_; 
lean_dec(v_a_986_);
v___x_988_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitGoal(v_a_983_, v___y_965_, v___y_966_, v___y_967_, v___y_968_);
if (lean_obj_tag(v___x_988_) == 0)
{
lean_object* v_a_989_; 
v_a_989_ = lean_ctor_get(v___x_988_, 0);
lean_inc(v_a_989_);
lean_dec_ref_known(v___x_988_, 1);
v_a_971_ = v_a_989_;
goto v___jp_970_;
}
else
{
lean_object* v_a_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_997_; 
v_a_990_ = lean_ctor_get(v___x_988_, 0);
v_isSharedCheck_997_ = !lean_is_exclusive(v___x_988_);
if (v_isSharedCheck_997_ == 0)
{
v___x_992_ = v___x_988_;
v_isShared_993_ = v_isSharedCheck_997_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_a_990_);
lean_dec(v___x_988_);
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
}
else
{
lean_object* v_a_998_; lean_object* v___x_1000_; uint8_t v_isShared_1001_; uint8_t v_isSharedCheck_1005_; 
lean_dec(v_a_983_);
v_a_998_ = lean_ctor_get(v___x_985_, 0);
v_isSharedCheck_1005_ = !lean_is_exclusive(v___x_985_);
if (v_isSharedCheck_1005_ == 0)
{
v___x_1000_ = v___x_985_;
v_isShared_1001_ = v_isSharedCheck_1005_;
goto v_resetjp_999_;
}
else
{
lean_inc(v_a_998_);
lean_dec(v___x_985_);
v___x_1000_ = lean_box(0);
v_isShared_1001_ = v_isSharedCheck_1005_;
goto v_resetjp_999_;
}
v_resetjp_999_:
{
lean_object* v___x_1003_; 
if (v_isShared_1001_ == 0)
{
v___x_1003_ = v___x_1000_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v_a_998_);
v___x_1003_ = v_reuseFailAlloc_1004_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
return v___x_1003_;
}
}
}
}
else
{
lean_object* v_a_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1013_; 
v_a_1006_ = lean_ctor_get(v___x_982_, 0);
v_isSharedCheck_1013_ = !lean_is_exclusive(v___x_982_);
if (v_isSharedCheck_1013_ == 0)
{
v___x_1008_ = v___x_982_;
v_isShared_1009_ = v_isSharedCheck_1013_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_a_1006_);
lean_dec(v___x_982_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1013_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v___x_1011_; 
if (v_isShared_1009_ == 0)
{
v___x_1011_ = v___x_1008_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v_a_1006_);
v___x_1011_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
return v___x_1011_;
}
}
}
v___jp_970_:
{
lean_object* v___x_972_; lean_object* v___x_973_; 
v___x_972_ = lean_box(0);
v___x_973_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v_a_971_, v___y_962_, v___y_965_, v___y_966_, v___y_967_, v___y_968_);
if (lean_obj_tag(v___x_973_) == 0)
{
lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_980_; 
v_isSharedCheck_980_ = !lean_is_exclusive(v___x_973_);
if (v_isSharedCheck_980_ == 0)
{
lean_object* v_unused_981_; 
v_unused_981_ = lean_ctor_get(v___x_973_, 0);
lean_dec(v_unused_981_);
v___x_975_ = v___x_973_;
v_isShared_976_ = v_isSharedCheck_980_;
goto v_resetjp_974_;
}
else
{
lean_dec(v___x_973_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_980_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v___x_978_; 
if (v_isShared_976_ == 0)
{
lean_ctor_set(v___x_975_, 0, v___x_972_);
v___x_978_ = v___x_975_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v___x_972_);
v___x_978_ = v_reuseFailAlloc_979_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
return v___x_978_;
}
}
}
else
{
return v___x_973_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSplit___lam__1___boxed(lean_object* v_type_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_){
_start:
{
uint8_t v_type_3687__boxed_1024_; lean_object* v_res_1025_; 
v_type_3687__boxed_1024_ = lean_unbox(v_type_1014_);
v_res_1025_ = l_Lean_Elab_Tactic_evalSplit___lam__1(v_type_3687__boxed_1024_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_);
lean_dec(v___y_1022_);
lean_dec_ref(v___y_1021_);
lean_dec(v___y_1020_);
lean_dec_ref(v___y_1019_);
lean_dec(v___y_1018_);
lean_dec_ref(v___y_1017_);
lean_dec(v___y_1016_);
lean_dec_ref(v___y_1015_);
return v_res_1025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSplit___lam__2(lean_object* v_a_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_){
_start:
{
lean_object* v_a_1037_; lean_object* v___x_1048_; 
v___x_1048_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_1028_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_);
if (lean_obj_tag(v___x_1048_) == 0)
{
lean_object* v_a_1049_; lean_object* v___x_1050_; 
v_a_1049_ = lean_ctor_get(v___x_1048_, 0);
lean_inc_n(v_a_1049_, 2);
lean_dec_ref_known(v___x_1048_, 1);
lean_inc(v_a_1026_);
v___x_1050_ = l_Lean_Meta_splitLocalDecl_x3f(v_a_1049_, v_a_1026_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_);
if (lean_obj_tag(v___x_1050_) == 0)
{
lean_object* v_a_1051_; 
v_a_1051_ = lean_ctor_get(v___x_1050_, 0);
lean_inc(v_a_1051_);
lean_dec_ref_known(v___x_1050_, 1);
if (lean_obj_tag(v_a_1051_) == 1)
{
lean_object* v_val_1052_; 
lean_dec(v_a_1049_);
lean_dec(v_a_1026_);
v_val_1052_ = lean_ctor_get(v_a_1051_, 0);
lean_inc(v_val_1052_);
lean_dec_ref_known(v_a_1051_, 1);
v_a_1037_ = v_val_1052_;
goto v___jp_1036_;
}
else
{
lean_object* v___x_1053_; 
lean_dec(v_a_1051_);
v___x_1053_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwCouldNotSplitHyp(v_a_1026_, v_a_1049_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_);
if (lean_obj_tag(v___x_1053_) == 0)
{
lean_object* v_a_1054_; 
v_a_1054_ = lean_ctor_get(v___x_1053_, 0);
lean_inc(v_a_1054_);
lean_dec_ref_known(v___x_1053_, 1);
v_a_1037_ = v_a_1054_;
goto v___jp_1036_;
}
else
{
lean_object* v_a_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1062_; 
v_a_1055_ = lean_ctor_get(v___x_1053_, 0);
v_isSharedCheck_1062_ = !lean_is_exclusive(v___x_1053_);
if (v_isSharedCheck_1062_ == 0)
{
v___x_1057_ = v___x_1053_;
v_isShared_1058_ = v_isSharedCheck_1062_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_a_1055_);
lean_dec(v___x_1053_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1062_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
lean_object* v___x_1060_; 
if (v_isShared_1058_ == 0)
{
v___x_1060_ = v___x_1057_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v_a_1055_);
v___x_1060_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
return v___x_1060_;
}
}
}
}
}
else
{
lean_object* v_a_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1070_; 
lean_dec(v_a_1049_);
lean_dec(v_a_1026_);
v_a_1063_ = lean_ctor_get(v___x_1050_, 0);
v_isSharedCheck_1070_ = !lean_is_exclusive(v___x_1050_);
if (v_isSharedCheck_1070_ == 0)
{
v___x_1065_ = v___x_1050_;
v_isShared_1066_ = v_isSharedCheck_1070_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_a_1063_);
lean_dec(v___x_1050_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1070_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
lean_object* v___x_1068_; 
if (v_isShared_1066_ == 0)
{
v___x_1068_ = v___x_1065_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v_a_1063_);
v___x_1068_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
return v___x_1068_;
}
}
}
}
else
{
lean_object* v_a_1071_; lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1078_; 
lean_dec(v_a_1026_);
v_a_1071_ = lean_ctor_get(v___x_1048_, 0);
v_isSharedCheck_1078_ = !lean_is_exclusive(v___x_1048_);
if (v_isSharedCheck_1078_ == 0)
{
v___x_1073_ = v___x_1048_;
v_isShared_1074_ = v_isSharedCheck_1078_;
goto v_resetjp_1072_;
}
else
{
lean_inc(v_a_1071_);
lean_dec(v___x_1048_);
v___x_1073_ = lean_box(0);
v_isShared_1074_ = v_isSharedCheck_1078_;
goto v_resetjp_1072_;
}
v_resetjp_1072_:
{
lean_object* v___x_1076_; 
if (v_isShared_1074_ == 0)
{
v___x_1076_ = v___x_1073_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v_a_1071_);
v___x_1076_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
return v___x_1076_;
}
}
}
v___jp_1036_:
{
lean_object* v___x_1038_; lean_object* v___x_1039_; 
v___x_1038_ = lean_box(0);
v___x_1039_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v_a_1037_, v___y_1028_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_);
if (lean_obj_tag(v___x_1039_) == 0)
{
lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1046_; 
v_isSharedCheck_1046_ = !lean_is_exclusive(v___x_1039_);
if (v_isSharedCheck_1046_ == 0)
{
lean_object* v_unused_1047_; 
v_unused_1047_ = lean_ctor_get(v___x_1039_, 0);
lean_dec(v_unused_1047_);
v___x_1041_ = v___x_1039_;
v_isShared_1042_ = v_isSharedCheck_1046_;
goto v_resetjp_1040_;
}
else
{
lean_dec(v___x_1039_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1046_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v___x_1044_; 
if (v_isShared_1042_ == 0)
{
lean_ctor_set(v___x_1041_, 0, v___x_1038_);
v___x_1044_ = v___x_1041_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v___x_1038_);
v___x_1044_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
return v___x_1044_;
}
}
}
else
{
return v___x_1039_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSplit___lam__2___boxed(lean_object* v_a_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_){
_start:
{
lean_object* v_res_1089_; 
v_res_1089_ = l_Lean_Elab_Tactic_evalSplit___lam__2(v_a_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_);
lean_dec(v___y_1087_);
lean_dec_ref(v___y_1086_);
lean_dec(v___y_1085_);
lean_dec_ref(v___y_1084_);
lean_dec(v___y_1083_);
lean_dec_ref(v___y_1082_);
lean_dec(v___y_1081_);
lean_dec_ref(v___y_1080_);
return v_res_1089_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSplit(lean_object* v_stx_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_){
_start:
{
lean_object* v___f_1101_; lean_object* v___x_1102_; lean_object* v___y_1104_; uint8_t v___y_1105_; lean_object* v___y_1106_; lean_object* v___y_1107_; lean_object* v___y_1108_; lean_object* v___y_1109_; lean_object* v___y_1110_; lean_object* v___y_1111_; lean_object* v___y_1112_; lean_object* v___y_1113_; lean_object* v___y_1114_; lean_object* v___y_1131_; lean_object* v___y_1132_; lean_object* v___y_1133_; lean_object* v___y_1134_; uint8_t v___y_1135_; lean_object* v___y_1136_; lean_object* v___y_1137_; lean_object* v___y_1138_; lean_object* v___y_1139_; lean_object* v___y_1140_; lean_object* v___y_1141_; lean_object* v___y_1142_; uint8_t v___y_1145_; lean_object* v___y_1146_; lean_object* v___y_1147_; lean_object* v___y_1148_; lean_object* v___y_1149_; lean_object* v___y_1150_; lean_object* v___y_1151_; lean_object* v___y_1152_; lean_object* v___y_1153_; lean_object* v___y_1154_; lean_object* v___y_1155_; lean_object* v___y_1156_; lean_object* v___y_1161_; lean_object* v___y_1162_; lean_object* v___y_1163_; lean_object* v___y_1164_; lean_object* v___y_1165_; lean_object* v___y_1166_; lean_object* v___y_1167_; lean_object* v___y_1168_; lean_object* v___x_1180_; uint8_t v___x_1181_; 
v___f_1101_ = ((lean_object*)(l_Lean_Elab_Tactic_evalSplit___closed__0));
v___x_1102_ = lean_box(0);
v___x_1180_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__5));
lean_inc(v_stx_1091_);
v___x_1181_ = l_Lean_Syntax_isOfKind(v_stx_1091_, v___x_1180_);
if (v___x_1181_ == 0)
{
v___y_1161_ = v_a_1092_;
v___y_1162_ = v_a_1093_;
v___y_1163_ = v_a_1094_;
v___y_1164_ = v_a_1095_;
v___y_1165_ = v_a_1096_;
v___y_1166_ = v_a_1097_;
v___y_1167_ = v_a_1098_;
v___y_1168_ = v_a_1099_;
goto v___jp_1160_;
}
else
{
lean_object* v___x_1182_; lean_object* v___x_1183_; uint8_t v___x_1184_; 
v___x_1182_ = lean_unsigned_to_nat(1u);
v___x_1183_ = l_Lean_Syntax_getArg(v_stx_1091_, v___x_1182_);
lean_inc(v___x_1183_);
v___x_1184_ = l_Lean_Syntax_matchesNull(v___x_1183_, v___x_1182_);
if (v___x_1184_ == 0)
{
lean_dec(v___x_1183_);
v___y_1161_ = v_a_1092_;
v___y_1162_ = v_a_1093_;
v___y_1163_ = v_a_1094_;
v___y_1164_ = v_a_1095_;
v___y_1165_ = v_a_1096_;
v___y_1166_ = v_a_1097_;
v___y_1167_ = v_a_1098_;
v___y_1168_ = v_a_1099_;
goto v___jp_1160_;
}
else
{
lean_object* v___x_1185_; lean_object* v_t_1186_; lean_object* v___y_1188_; lean_object* v___y_1189_; lean_object* v___y_1190_; lean_object* v___y_1191_; lean_object* v___y_1192_; lean_object* v___y_1193_; lean_object* v___y_1194_; lean_object* v___y_1195_; lean_object* v___y_1196_; lean_object* v___x_1198_; lean_object* v___x_1199_; uint8_t v___x_1200_; 
v___x_1185_ = lean_unsigned_to_nat(0u);
v_t_1186_ = l_Lean_Syntax_getArg(v___x_1183_, v___x_1185_);
lean_dec(v___x_1183_);
v___x_1198_ = lean_unsigned_to_nat(2u);
v___x_1199_ = l_Lean_Syntax_getArg(v_stx_1091_, v___x_1198_);
v___x_1200_ = l_Lean_Syntax_isNone(v___x_1199_);
if (v___x_1200_ == 0)
{
uint8_t v___x_1201_; 
lean_inc(v___x_1199_);
v___x_1201_ = l_Lean_Syntax_matchesNull(v___x_1199_, v___x_1182_);
if (v___x_1201_ == 0)
{
lean_dec(v___x_1199_);
lean_dec(v_t_1186_);
v___y_1161_ = v_a_1092_;
v___y_1162_ = v_a_1093_;
v___y_1163_ = v_a_1094_;
v___y_1164_ = v_a_1095_;
v___y_1165_ = v_a_1096_;
v___y_1166_ = v_a_1097_;
v___y_1167_ = v_a_1098_;
v___y_1168_ = v_a_1099_;
goto v___jp_1160_;
}
else
{
lean_object* v___x_1202_; lean_object* v___x_1203_; uint8_t v___x_1204_; 
v___x_1202_ = l_Lean_Syntax_getArg(v___x_1199_, v___x_1185_);
lean_dec(v___x_1199_);
v___x_1203_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__10));
lean_inc(v___x_1202_);
v___x_1204_ = l_Lean_Syntax_isOfKind(v___x_1202_, v___x_1203_);
if (v___x_1204_ == 0)
{
lean_dec(v___x_1202_);
lean_dec(v_t_1186_);
v___y_1161_ = v_a_1092_;
v___y_1162_ = v_a_1093_;
v___y_1163_ = v_a_1094_;
v___y_1164_ = v_a_1095_;
v___y_1165_ = v_a_1096_;
v___y_1166_ = v_a_1097_;
v___y_1167_ = v_a_1098_;
v___y_1168_ = v_a_1099_;
goto v___jp_1160_;
}
else
{
lean_object* v_loc_1205_; lean_object* v___x_1206_; 
v_loc_1205_ = l_Lean_Syntax_getArg(v___x_1202_, v___x_1182_);
lean_dec(v___x_1202_);
v___x_1206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1206_, 0, v_loc_1205_);
v___y_1188_ = v_a_1099_;
v___y_1189_ = v_a_1092_;
v___y_1190_ = v_a_1098_;
v___y_1191_ = v_a_1097_;
v___y_1192_ = v_a_1093_;
v___y_1193_ = v_a_1095_;
v___y_1194_ = v_a_1096_;
v___y_1195_ = v_a_1094_;
v___y_1196_ = v___x_1206_;
goto v___jp_1187_;
}
}
}
else
{
lean_object* v___x_1207_; 
lean_dec(v___x_1199_);
v___x_1207_ = lean_box(0);
v___y_1188_ = v_a_1099_;
v___y_1189_ = v_a_1092_;
v___y_1190_ = v_a_1098_;
v___y_1191_ = v_a_1097_;
v___y_1192_ = v_a_1093_;
v___y_1193_ = v_a_1095_;
v___y_1194_ = v_a_1096_;
v___y_1195_ = v_a_1094_;
v___y_1196_ = v___x_1207_;
goto v___jp_1187_;
}
v___jp_1187_:
{
lean_object* v___x_1197_; 
v___x_1197_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported(v_t_1186_, v___y_1196_, v___y_1189_, v___y_1192_, v___y_1195_, v___y_1193_, v___y_1194_, v___y_1191_, v___y_1190_, v___y_1188_);
if (lean_obj_tag(v___x_1197_) == 0)
{
lean_dec_ref_known(v___x_1197_, 1);
v___y_1161_ = v___y_1189_;
v___y_1162_ = v___y_1192_;
v___y_1163_ = v___y_1195_;
v___y_1164_ = v___y_1193_;
v___y_1165_ = v___y_1194_;
v___y_1166_ = v___y_1191_;
v___y_1167_ = v___y_1190_;
v___y_1168_ = v___y_1188_;
goto v___jp_1160_;
}
else
{
lean_dec(v_stx_1091_);
return v___x_1197_;
}
}
}
}
v___jp_1103_:
{
if (v___y_1105_ == 0)
{
lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; 
lean_dec_ref(v___y_1104_);
v___x_1115_ = lean_unsigned_to_nat(0u);
v___x_1116_ = lean_array_get(v___x_1102_, v___y_1106_, v___x_1115_);
lean_dec_ref(v___y_1106_);
v___x_1117_ = l_Lean_Elab_Tactic_getFVarId(v___x_1116_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_);
if (lean_obj_tag(v___x_1117_) == 0)
{
lean_object* v_a_1118_; lean_object* v___f_1119_; lean_object* v___x_1120_; 
v_a_1118_ = lean_ctor_get(v___x_1117_, 0);
lean_inc(v_a_1118_);
lean_dec_ref_known(v___x_1117_, 1);
v___f_1119_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSplit___lam__2___boxed), 10, 1);
lean_closure_set(v___f_1119_, 0, v_a_1118_);
v___x_1120_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_1119_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_);
return v___x_1120_;
}
else
{
lean_object* v_a_1121_; lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1128_; 
v_a_1121_ = lean_ctor_get(v___x_1117_, 0);
v_isSharedCheck_1128_ = !lean_is_exclusive(v___x_1117_);
if (v_isSharedCheck_1128_ == 0)
{
v___x_1123_ = v___x_1117_;
v_isShared_1124_ = v_isSharedCheck_1128_;
goto v_resetjp_1122_;
}
else
{
lean_inc(v_a_1121_);
lean_dec(v___x_1117_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1128_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
lean_object* v___x_1126_; 
if (v_isShared_1124_ == 0)
{
v___x_1126_ = v___x_1123_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v_a_1121_);
v___x_1126_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
return v___x_1126_;
}
}
}
}
else
{
lean_object* v___x_1129_; 
lean_dec_ref(v___y_1106_);
v___x_1129_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___y_1104_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_);
return v___x_1129_;
}
}
v___jp_1130_:
{
lean_object* v___x_1143_; 
lean_dec_ref(v___y_1131_);
v___x_1143_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwMultipleLocationsAt___redArg(v___y_1141_, v___y_1135_, v___y_1139_, v___y_1142_, v___y_1134_, v___y_1133_, v___y_1140_);
lean_dec(v___y_1141_);
return v___x_1143_;
}
v___jp_1144_:
{
lean_object* v___x_1157_; lean_object* v___x_1158_; uint8_t v___x_1159_; 
v___x_1157_ = lean_unsigned_to_nat(1u);
v___x_1158_ = lean_array_get_size(v___y_1146_);
v___x_1159_ = lean_nat_dec_lt(v___x_1157_, v___x_1158_);
if (v___x_1159_ == 0)
{
lean_dec(v___y_1154_);
v___y_1104_ = v___y_1147_;
v___y_1105_ = v___y_1145_;
v___y_1106_ = v___y_1146_;
v___y_1107_ = v___y_1153_;
v___y_1108_ = v___y_1149_;
v___y_1109_ = v___y_1152_;
v___y_1110_ = v___y_1151_;
v___y_1111_ = v___y_1156_;
v___y_1112_ = v___y_1150_;
v___y_1113_ = v___y_1148_;
v___y_1114_ = v___y_1155_;
goto v___jp_1103_;
}
else
{
v___y_1131_ = v___y_1147_;
v___y_1132_ = v___y_1149_;
v___y_1133_ = v___y_1148_;
v___y_1134_ = v___y_1150_;
v___y_1135_ = v___y_1145_;
v___y_1136_ = v___y_1151_;
v___y_1137_ = v___y_1152_;
v___y_1138_ = v___y_1153_;
v___y_1139_ = v___y_1146_;
v___y_1140_ = v___y_1155_;
v___y_1141_ = v___y_1154_;
v___y_1142_ = v___y_1156_;
goto v___jp_1130_;
}
}
v___jp_1160_:
{
lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v_loc_1171_; 
v___x_1169_ = lean_unsigned_to_nat(2u);
v___x_1170_ = l_Lean_Syntax_getArg(v_stx_1091_, v___x_1169_);
lean_dec(v_stx_1091_);
v_loc_1171_ = l_Lean_Elab_Tactic_expandOptLocation(v___x_1170_);
if (lean_obj_tag(v_loc_1171_) == 0)
{
lean_object* v___x_1172_; 
lean_dec(v___x_1170_);
v___x_1172_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_1101_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_);
return v___x_1172_;
}
else
{
lean_object* v_hypotheses_1173_; uint8_t v_type_1174_; lean_object* v___x_1175_; lean_object* v___f_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; uint8_t v___x_1179_; 
v_hypotheses_1173_ = lean_ctor_get(v_loc_1171_, 0);
lean_inc_ref(v_hypotheses_1173_);
v_type_1174_ = lean_ctor_get_uint8(v_loc_1171_, sizeof(void*)*1);
lean_dec_ref_known(v_loc_1171_, 1);
v___x_1175_ = lean_box(v_type_1174_);
v___f_1176_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSplit___lam__1___boxed), 10, 1);
lean_closure_set(v___f_1176_, 0, v___x_1175_);
v___x_1177_ = lean_unsigned_to_nat(0u);
v___x_1178_ = lean_array_get_size(v_hypotheses_1173_);
v___x_1179_ = lean_nat_dec_lt(v___x_1177_, v___x_1178_);
if (v___x_1179_ == 0)
{
v___y_1145_ = v_type_1174_;
v___y_1146_ = v_hypotheses_1173_;
v___y_1147_ = v___f_1176_;
v___y_1148_ = v___y_1167_;
v___y_1149_ = v___y_1162_;
v___y_1150_ = v___y_1166_;
v___y_1151_ = v___y_1164_;
v___y_1152_ = v___y_1163_;
v___y_1153_ = v___y_1161_;
v___y_1154_ = v___x_1170_;
v___y_1155_ = v___y_1168_;
v___y_1156_ = v___y_1165_;
goto v___jp_1144_;
}
else
{
if (v_type_1174_ == 0)
{
v___y_1145_ = v_type_1174_;
v___y_1146_ = v_hypotheses_1173_;
v___y_1147_ = v___f_1176_;
v___y_1148_ = v___y_1167_;
v___y_1149_ = v___y_1162_;
v___y_1150_ = v___y_1166_;
v___y_1151_ = v___y_1164_;
v___y_1152_ = v___y_1163_;
v___y_1153_ = v___y_1161_;
v___y_1154_ = v___x_1170_;
v___y_1155_ = v___y_1168_;
v___y_1156_ = v___y_1165_;
goto v___jp_1144_;
}
else
{
v___y_1131_ = v___f_1176_;
v___y_1132_ = v___y_1162_;
v___y_1133_ = v___y_1167_;
v___y_1134_ = v___y_1166_;
v___y_1135_ = v_type_1174_;
v___y_1136_ = v___y_1164_;
v___y_1137_ = v___y_1163_;
v___y_1138_ = v___y_1161_;
v___y_1139_ = v_hypotheses_1173_;
v___y_1140_ = v___y_1168_;
v___y_1141_ = v___x_1170_;
v___y_1142_ = v___y_1165_;
goto v___jp_1130_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSplit___boxed(lean_object* v_stx_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_){
_start:
{
lean_object* v_res_1218_; 
v_res_1218_ = l_Lean_Elab_Tactic_evalSplit(v_stx_1208_, v_a_1209_, v_a_1210_, v_a_1211_, v_a_1212_, v_a_1213_, v_a_1214_, v_a_1215_, v_a_1216_);
lean_dec(v_a_1216_);
lean_dec_ref(v_a_1215_);
lean_dec(v_a_1214_);
lean_dec_ref(v_a_1213_);
lean_dec(v_a_1212_);
lean_dec_ref(v_a_1211_);
lean_dec(v_a_1210_);
lean_dec_ref(v_a_1209_);
return v_res_1218_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit__1(){
_start:
{
lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; 
v___x_1227_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1228_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_throwTermUnsupported___lam__0___closed__5));
v___x_1229_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit__1___closed__2));
v___x_1230_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSplit___boxed), 10, 0);
v___x_1231_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1227_, v___x_1228_, v___x_1229_, v___x_1230_);
return v___x_1231_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit__1___boxed(lean_object* v_a_1232_){
_start:
{
lean_object* v_res_1233_; 
v_res_1233_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit__1();
return v_res_1233_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3(){
_start:
{
lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; 
v___x_1260_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit__1___closed__2));
v___x_1261_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___closed__6));
v___x_1262_ = l_Lean_addBuiltinDeclarationRanges(v___x_1260_, v___x_1261_);
return v___x_1262_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3___boxed(lean_object* v_a_1263_){
_start:
{
lean_object* v_res_1264_; 
v_res_1264_ = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3();
return v_res_1264_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Split(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Location(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Split(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Split(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Location(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint = _init_l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint();
lean_mark_persistent(l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit_traceHint);
res = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Split_0__Lean_Elab_Tactic_evalSplit___regBuiltin_Lean_Elab_Tactic_evalSplit_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Split(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Split(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Location(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Split(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Split(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Location(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Split(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Split(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Split(builtin);
}
#ifdef __cplusplus
}
#endif
